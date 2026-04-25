import FullCorrectness.Basic
import FullCorrectness.Permutation
import FullCorrectness.Automorphism
import FullCorrectness.Isomorphic
import FullCorrectness.Equivariance
import FullCorrectness.Tiebreak
import FullCorrectness.Invariants
import FullCorrectness.Main

/-!
# Full correctness of the graph canonizer — umbrella + proof plan

Re-exports all submodules under `FullCorrectness/`. External consumers can
`import FullCorrectness` to pull in the whole proof; internal modules import
the specific step(s) they depend on.

The flat-flawed proof in `LeanGraphCanonizerV4Correctness.lean` is retired — its header
explains why its central equivariance claim is literally false. This tree replaces it.

## Target theorem (to be proved in §8)

```
run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

"`run` with all-zero starting vertex types is a complete graph-isomorphism invariant."

## Status at a glance

| Step | Subject                                           | File                                       | Status          |
| ---- | ------------------------------------------------- | ------------------------------------------ | --------------- |
| §1   | Automorphism group, orbits, `permute` action      | `Basic`, `Permutation`, `Automorphism`     | ✅ proved       |
| §1.7 | `Fintype G.Aut` (decidability + finiteness)       | `Automorphism`                             | ✅ proved       |
| §2   | `Isomorphic ↔ ∃σ, H = G.permute σ` bridge         | `Isomorphic`                               | ✅ proved       |
| §3   | Pipeline equivariance under Aut(G) (Stages A–D)   | `Equivariance`                             | A ✅, B 🧱 (RankState σ-invariance), C/D ✅ via Stage A |
| §4   | `convergeOnce` Aut-invariance (1 step)            | `Equivariance`                             | ✅ proved via writeback + getFrom-invariance |
| §4   | `convergeLoop` Aut-invariance (induction on fuel) | `Equivariance`                             | ✅ proved (with `vts.size = n`) |
| §5   | `TypedAut G vts` (subgroup + Fintype)             | `Tiebreak`                                 | ✅ defined       |
| §5.0 | `breakTie` output position-by-position            | `Tiebreak`                                 | ✅ proved (4 characterization lemmas) |
| §5.1 | `breakTie` is the v*-stabilizer of `TypedAut`     | `Tiebreak`                                 | ✅ proved (hypothesis revised — see note below) |
| §5.2 | `breakTie` strictly shrinks `TypedAut`            | `Tiebreak`                                 | ✅ proved (hypothesis revised — see note below) |
| §6.0 | `breakTieAt` output + τ-equivariance              | `Tiebreak`                                 | ✅ proved (3 characterization + 1 equivariance) |
| §6   | Tiebreak choice-independence (conceptual crux)    | `Tiebreak`                                 | ✅ closed modulo `runFrom_VtsInvariant_eq` (the chained §3 Stages B–D for `runFrom`) |
| §7   | `IsPrefixTyping` definition + zeros instance      | `Invariants`                               | ✅ defined + boundary proved |
| §7   | `breakTie_targetPos_is_min_tied`                  | `Invariants`                               | ✅ proved (uses §5 disjunctive characterization) |
| §7   | Other prefix invariants (3)                       | `Invariants`                               | 🧱 stated, `sorry` |
| §8   | Assemble `run_canonical_correctness`              | `Main`                                     | 🧱 assembled, (⟹) `sorry`; (⟸) proved |

**Sorry count.** 4 (Equivariance: `comparePathsBetween_total_preorder`,
`comparePathsBetween_equivCompat`, `calculatePathRankings_fromRanks_inv`,
`calculatePathRankings_betweenRanks_inv`) + 1 (Tiebreak — `runFrom_VtsInvariant_eq`) +
3 (Invariants — §7) + 1 (Main) = **9 open obligations** (down from 10). Closures this
iteration:

- **`sortedPerm_class_eq`** ✅ — counting argument (positions in sorted lists bounded
  by `lt_count` from below and `not_gt_count` from above; both `Perm`-invariant via
  `List.Perm.countP_eq`). Required four hypotheses on `cmp` in the signature (refl,
  both directions of antisymmetry, `≤`-trans), propagated to `orderInsensitiveListCmp_perm`
  and its two callers via the helper lemmas `comparePathSegments_total_preorder` /
  `comparePathsBetween_total_preorder`.
- **`sortBy_pairwise`** ✅ — standard insertion-sort sortedness, via a new
  `insertSorted_pairwise` helper using `h_antisym₂` and `h_trans`.
- **`comparePathSegments_total_preorder`** ✅ — proved after a small refactor of
  `comparePathSegments` ([LeanGraphCanonizerV4.lean:107](LeanGraphCanonizerV4.lean#L107))
  that replaced the original `panic!` mixed-bottom/inner case with a fixed ordering
  (`bottom < inner`). The previous `panic!` returned `default = .lt` in both directions,
  breaking antisymmetry. The fixed ordering preserves the algorithm's behavior on the
  actual lists (which are always uniform, never mixed) and verifies that
  `LeanGraphCanonizerV4Tests` still passes. Three small `cmpInner_*` helpers reduce the
  inner-inner branch to Nat trichotomy + `omega`.

Remaining in `Equivariance`:
- `comparePathsBetween_total_preorder`: needs `orderInsensitiveListCmp` analogues of
  refl/antisym/trans. The `cmp` here is `comparePathSegments` (now a total preorder), so
  the structural argument is in scope but requires foldl-based analysis of
  `orderInsensitiveListCmp` on `(L, L)`, swapped lists, and chained lists.
- `comparePathsBetween_equivCompat`: same architectural shape — needs
  `orderInsensitiveListCmp` to respect `.eq` substitution under bilateral cmp-compat.
- `calculatePathRankings_fromRanks_inv` / `..._betweenRanks_inv`: the deep fold-level
  σ-invariance of the rank tables. Foldl induction on the depth loop.

**Closed during the equivariance push:**
- **Stage D** trivially via `σ ∈ Aut G ⟹ G.permute σ = G`.
- **Stage C** by Stage A + Stage-D-style substitution.
- **Stage A** (`initializePaths_Aut_equivariant`) — `succ` case proved via two helper
  lemmas (`PathsBetween_initializePaths_eq`, `PathsFrom_initializePaths_eq`) + nested
  `Array.ext` descending through `pathsOfLength`.
- **Stage B** (`calculatePathRankings_RankState_invariant`) — reduced via the structural
  `RankState.σInvariant` predicate + extensionality (`σInvariant.permute_eq_self`). The
  remaining content is `calculatePathRankings_σInvariant`: σ-invariance of the rank state
  under `σ ∈ Aut G` + σ-invariant `vts`. This is the genuine "path bijection under Aut"
  content and requires σ-equivariance of `comparePathSegments`/`comparePathsBetween`/
  `comparePathsFrom`/`sortBy`/`assignRanks` propagated through the outer fold.
- **`convergeOnce_Aut_invariant`** via a `convergeOnce_writeback` lemma (proved) +
  `RankState.getFrom_permute` (proved) + the `RankState` invariant.
- **`convergeOnce_size_preserving`** proved (foldl invariant, mechanical).
- **`calculatePathRankings_fromRanks_size`** proved (foldl invariant on the algorithm body).

**Remaining structural work in `Equivariance`** (all sorried, each well-scoped):
- `comparePathsBetween_total_preorder`: provides the four total-preorder properties for
  `comparePathsBetween`. The inner cmp `comparePathSegments` is now a total preorder
  (closed via the algorithm refactor), so this reduces to lifting total-preorder
  properties through `orderInsensitiveListCmp` (a foldl-based comparator). The `_refl`
  lifting helper (`orderInsensitiveListCmp_refl`) is now proved; the `_swap` and `_trans`
  lifting helpers are tractable by induction on the zipped `sortBy` outputs but require
  careful handling of the foldl reduction, where after `List.foldl_cons` the
  function-application form is beta-reduced and abstract step lemmas don't match via
  `rw`. The fix is to write the per-step equalities in their reduced form using `show`,
  similar to how `orderInsensitiveListCmp_refl` is structured.
- `comparePathsBetween_equivCompat`: `comparePathsBetween` respects equivalence classes
  (needed for `orderInsensitiveListCmp_perm` at the `comparePathsFrom` level). Requires
  an auxiliary `orderInsensitiveListCmp_equivCompat` lemma — same architectural shape
  as `comparePathsBetween_total_preorder`, both depend on `orderInsensitiveListCmp`
  property-lifting helpers.
- `calculatePathRankings_fromRanks_inv` / `..._betweenRanks_inv`: the fold-level
  σ-invariance of the rank tables. Requires foldl induction on the depth loop plus
  σ-equivariance of sortBy + assignRanks at each step.

**Proved infrastructure in `Equivariance`**:
- `comparePathSegments_σ_equivariant` — base case of compare σ-equivariance.
- `comparePathSegments_equivCompat` — `comparePathSegments` respects equivalence classes
  (supplies the hypothesis for `orderInsensitiveListCmp_perm` at the inner level).
- `sortBy_perm` + `perm_insertSorted` — sortBy preserves multiset (`Perm`).
- `sortBy_map` + `orderInsensitiveListCmp_map` — sort/compare respect `map`-ping by a
  `cmp`-preserving function (handles the depth=0 branch directly).
- `insertSorted_map_pointwise` + `sortBy_map_pointwise` + `orderInsensitiveListCmp_map_pointwise`
  + `foldl_congr_mem` — pointwise (per-element) variants; used to bridge
  `comparePathsBetween_σ_equivariant`'s per-element `h_len` hypothesis into the uniform
  condition expected by `orderInsensitiveListCmp_map`.
- `comparePathsBetween_σ_equivariant` — proved (modulo the Perm + orderInsensitiveListCmp_perm
  sorries).
- `comparePathsFrom_σ_equivariant` — proved (bridge closed via `orderInsensitiveListCmp_map_pointwise`).
- `sortedPerm_class_eq` — **proved** via the counting argument: `lt_count L L[i] ≤ i` and
  `not_gt_count L L[i] ≥ i + 1` in any sorted `L`, both `Perm`-transferred to `L'`, then
  ruled out `cmp L'[i] x = .lt` and `= .gt` separately by extending the counts via the
  helpers `h_le_lt` / `h_lt_le` (which combine refl, both antisymmetries, and ≤-trans).
  Takes four cmp hypotheses (refl, antisym₁, antisym₂, ≤-trans) in its signature.
- `sortBy_pairwise` — **proved** via a new `insertSorted_pairwise` helper. Insertion at
  the leftmost `≠ .gt` position; the head case uses `h_antisym₂` to flip `.gt → .lt`,
  the recursive case uses `h_trans`. Takes `h_antisym₂` and `h_trans` hypotheses.
- `comparePathSegments_total_preorder` — **proved**. Refl, both antisymmetries, and
  `≤`-transitivity of `comparePathSegments` after the algorithm refactor (panic →
  fixed `bottom < inner` ordering). Three internal `cmpInner_*` helpers reduce the
  inner-inner branch to Nat trichotomy + `omega`.
- `orderInsensitiveListCmp_perm` — **proved modulo the new cmp total-preorder hypotheses**
  passed through to `sortedPerm_class_eq` and `sortBy_pairwise`. Structural argument
  uses `foldl_pointwise_eq` + bilateral `h_compat`.
- `foldl_pointwise_eq` — generic pointwise foldl equality helper.
- `map_reindex_perm` — generic list reindex-`Perm` helper using Mathlib's
  `Equiv.Perm.ofFn_comp_perm`; bridges list reindexing under a bijection to `List.Perm`.
- `PathsBetween_permute_connectedSubPaths_perm` — proved via `map_reindex_perm`.
- `PathsFrom_permute_pathsToVertex_perm` — proved via `map_reindex_perm`.
- `PathState.permute` / `PathsFrom.permute` / `PathsBetween.permute` — action definitions.
- `calculatePathRankings_size_inv` — all 5 shape facts for the output via combined foldl
  invariant + `setBetween`/`set!` size-preservation helpers.
- `RankState.σInvariant.permute_eq_self` — structural extensionality.

### Algorithm refactor (this iteration)

The algorithm in `LeanGraphCanonizerV4.lean` was refactored to make the equivariance
proofs structurally simpler. Three changes:

  1. **`VertexType := Nat`, `EdgeType := Nat`** (was `Int`). The `Int` choice was
     arbitrary; nothing in the algorithm needs negative values. With `Nat`, the entire
     `Int.ofNat` / `Int.toNat` conversion machinery in `Tiebreak.lean` and
     `Invariants.lean` collapses, and the `0 ≤ vts[v]` half of `IsPrefixTyping` becomes
     vacuously true and is dropped from the definition.
  2. **Path-structure indices `Nat → Fin vertexCount`.** `PathSegment`, `PathsBetween`,
     `PathsFrom`, `PathState` are now parametrized by `vertexCount : Nat` and use
     `Fin vertexCount` for every vertex slot. The `PathState.vertexCount` field was
     dropped (redundant with the type-level parameter). At the algorithm level this is
     a pure typing strengthening — the runtime behavior and tests are unchanged.
  3. **Action definitions in `Equivariance.lean` simplified.** The per-element action on
     `PathSegment` is now literally `σ`-applied (`.bottom v ↦ .bottom (σ v)`) rather
     than going through a `permNat` lift on `Nat` indices. The residual `permNat`
     helper is kept for the *positional* re-indexing of `connectedSubPaths` and
     `pathsToVertex` lists (which are still `List`s, hence `Nat`-indexed by position),
     but is now used only for that residual case.

**Dense-rank migration in progress.** The fourth recommended algorithm change
(dense-rank inline in `convergeOnce`) is now being applied. See "## Sparse → Dense
Ranking Migration Notes" further down for the design, the affected proofs, and a
checklist of follow-up items to verify after the migration lands.

§5.1 and §5.2 are proved with stronger hypotheses than the original plan (see the "§5
hypothesis revisions" note below). §6 (`tiebreak_choice_independent`) is closed by
reduction to a single precisely-stated pipeline-equivariance lemma
(`runFrom_VtsInvariant_eq`), the chained §3 Stages B–D for the bounded `runFrom` loop.
The boundary lemmas (`VtsInvariant.replicate_zero`, `TypedAut_replicate_zero`,
`IsPrefixTyping.replicate_zero`, `convergeLoop_zeros_Aut_invariant`) and infrastructure
(`Fintype` instances on `Aut`/`TypedAut`, `DecidableEq` on `AdjMatrix`) are all proved.

### §5 disjunctive characterization (new)

In support of §7's `breakTie_targetPos_is_min_tied`, two reusable corollaries are added in
`Tiebreak.lean`:

```
breakTie_getD_target     : vts[w] = t₀ → output[w] = t₀ ∨ output[w] = t₀ + 1
breakTie_getD_target_ge  : vts[w] = t₀ → t₀ ≤ output[w]
```

Both are derived by picking `v_star` as the smallest target-valued index (`Nat.find`) and
applying `breakTie_getD_at_min` / `breakTie_getD_at_other`. They are useful whenever one
needs to know "the breakTie output at a target-valued vertex is either kept or promoted"
without naming the kept representative.

### §5 hypothesis revisions

During formalization of §5.1 and §5.2, two hypotheses were added beyond what the original
plan stated:

  1. **§5.1 adds `hsize : vts.size = n` and `hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts`.**
     The `hsize` hypothesis is trivially satisfied by the algorithm (all type arrays have
     size `n`); it's needed to connect `Fin n` indexing to `Array.getD`. The Aut-invariance
     hypothesis is genuinely necessary: without it, a label swap between a non-`v*` member
     of `typeClass t₀` and some position carrying value `t₀ + 1` can preserve `vts'`
     (both get value `t₀+1`) without preserving `vts`. Aut-invariance rules out this
     counterexample because such a swap would have to be an automorphism forcing the two
     positions to already agree in `vts`. In the algorithm, `vts` at each `breakTie` call
     is Aut-invariant by §4's corollary, so the hypothesis is satisfied.

  2. **§5.2 adds `hmove : ∃ σ ∈ G.TypedAut vts, σ v_star ≠ v_star`.**
     The plan's sketch claimed strict shrinking followed from "same-type vertices lie in
     a single Aut-orbit" (§4's corollary), but §4 only gives the forward direction
     (same-orbit → same-type), not the reverse. The reverse is essentially the algorithm's
     completeness — same-type vertices must be permutable — and requires a separate
     argument. We capture the minimal needed input in `hmove`: there's *some* typed
     automorphism moving `v_star`. With `hmove`, strictness is immediate from §5.1 (the
     moving automorphism is in `TypedAut vts` but not in the `v_star`-stabilizer).

### §6 restructuring

`tiebreak_choice_independent` has been revised to have two additional hypotheses beyond
the plan:

  - `hsize : vts.size = n` — as in §5.
  - `hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂` — orbit connectivity between `v₁` and `v₂`.
    This is the same "same-type ⟹ same-orbit" requirement that §5.2 needed. The plan
    implicitly invoked this from §4's corollary, but §4 only gives the forward direction;
    we make the required backward connection explicit.

With those hypotheses, §6 reduces to the *pipeline equivariance* statement:

```
runFrom_VtsInvariant_eq :
  τ ∈ G.Aut → (∀ w, arr₂[w] = arr₁[τ⁻¹ w]) → runFrom s arr₁ G = runFrom s arr₂ G
```

which is §3 (Stages B–D) chained. **`tiebreak_choice_independent` now type-checks**: it
discharges via `runFrom_VtsInvariant_eq` applied to the τ-related pair `breakTieAt vts t₀
v₁`, `breakTieAt vts t₀ v₂` (related by the τ from `hconn`). The single open obligation
in this whole chain is now `runFrom_VtsInvariant_eq` itself, stated in `Tiebreak.lean`
with `sorry`. Everything else around §6 is closed.

New deliverables in `Tiebreak.lean` supporting §6:
```
breakTieAt_size             : (breakTieAt vts t₀ keep).size = vts.size
breakTieAt_getD_of_ne       : vts[j] ≠ t₀ → (breakTieAt vts t₀ keep)[j] = vts[j]
breakTieAt_getD_keep        : (breakTieAt vts t₀ keep)[keep] = vts[keep]
breakTieAt_getD_promoted    : w ≠ keep ∧ vts[w] = t₀ → (breakTieAt vts t₀ keep)[w] = t₀ + 1
breakTieAt_VtsInvariant_eq  : [τ-equivariance under VtsInvariant τ vts]
```

--------------------------------------------------------------------------------

## Sparse → Dense Ranking Migration Notes

**Why these notes exist.** Switching `assignRanks` from sparse (rank = first-index-of-class
in sorted order) to dense (rank = number-of-classes-strictly-below) requires a coordinated
change to `breakTie`, because sparse ranks deliberately leave gaps that `breakTie`'s
"promote one tied vertex to `target + 1`" relied on for collision-freedom. With dense
ranks there is no gap, so promotion to `target + 1` would collide with the next class.
The fix is shift-then-promote: bump every value `> target` up by one to open a gap, then
do the existing promote pass into the gap.

This section catalogs everything that depends on the current sparse-rank semantics, so
each item can be re-verified against the new dense-rank semantics during the migration.
Each item is tagged `[sparse→dense]` for greppability.

### Algorithm-level changes

  **[sparse→dense]** **`assignRanks`** ([LeanGraphCanonizerV4.lean:163](LeanGraphCanonizerV4.lean#L163)).
   Currently `rank := if cmp prevItem item == .eq then prevRank else revList.length`.
   New: `rank := if cmp prevItem item == .eq then prevRank else prevRank + 1`.
   Watch for: anywhere downstream that assumed rank = "position in sorted order" rather
   than "ordinal of equivalence class". Comparisons still use `compare` on ranks, which
   is invariant under any monotone bijection — so `comparePathSegments`,
   `comparePathsBetween`, `comparePathsFrom` are all unaffected.

  **[sparse→dense]** **`getArrayRank`** ([LeanGraphCanonizerV4.lean:88](LeanGraphCanonizerV4.lean#L88)).
   Currently `arr.foldl (fun c other => if other < value then c + 1 else c) 0` per entry —
   this is "count of strictly smaller values", not dense rank. For value `v` in `[0, 1, 1, 2]`,
   the original gives `[0, 1, 1, 3]` (count of smaller); dense should give `[0, 1, 1, 2]`.
   Replace by `computeDenseRanks arr.size arr` (already in the codebase, used at the end
   of `labelEdgesAccordingToRankings`).

  **[sparse→dense]** **`breakTie`** ([LeanGraphCanonizerV4.lean:248](LeanGraphCanonizerV4.lean#L248)).
   Decompose into `shiftAbove` + `breakTiePromote` (the latter is the current `breakTie`
   body, renamed). Top-level `breakTie` first counts target-valued entries; if `< 2` it's
   a no-op (preserving denseness), else applies shift then promote. The gating matters:
   shifting unconditionally would create gaps when no promotion happens, breaking the
   prefix invariant that motivates this whole change.

### Proof-level impacts

  **[sparse→dense]** **`breakTie_getD_of_ne`** ([Tiebreak.lean:240](FullCorrectness/Tiebreak.lean#L240))
   no longer holds as stated (`vts[j] > t₀` positions get bumped). Replace with two lemmas:
   `breakTie_getD_below : vts[j] < t₀ → output[j] = vts[j]` and
   `breakTie_getD_above : vts[j] > t₀ → output[j] = vts[j] + 1`.

  **[sparse→dense]** **`breakTie_Aut_stabilizer`** ([Tiebreak.lean:528](FullCorrectness/Tiebreak.lean#L528))
   statement unchanged, proof rewrites the "non-target unchanged" case as the below/above
   split. The high-level argument (σ preserves post-vts ⇔ σ ∈ TypedAut vts ∧ σ v* = v*)
   survives because shift is a bijection on value labels and `TypedAut` depends only on
   the vertex partition, not the labels.

  **[sparse→dense]** **`breakTieAt`** ([Tiebreak.lean:750](FullCorrectness/Tiebreak.lean#L750))
   and its lemma block need the symmetric shift-then-keep treatment. Same risk profile as
   `breakTie`.

  **[sparse→dense]** **`btFold_*` infrastructure** ([Tiebreak.lean:187](FullCorrectness/Tiebreak.lean#L187)
   onward) is *not* invalidated — it now describes `breakTiePromote` (the second stage of
   the new `breakTie`). Add a small companion block of `shiftAbove_*` lemmas (size,
   below/above value characterization) and one `breakTie_eq_compose` lemma stitching them.

  **[sparse→dense]** **`breakTie_targetPos_is_min_tied`** ([Invariants.lean:107](FullCorrectness/Invariants.lean#L107))
   is already proved; the proof uses `breakTie_getD_of_ne`. Replace those uses with the
   below/above split. The "val < p" branch becomes `breakTie_getD_below`; "val = p"
   branch is unchanged.

### Downstream payoff (proofs that newly become tractable)

  **[sparse→dense]** **`convergeLoop_preserves_prefix`** ([Invariants.lean:78](FullCorrectness/Invariants.lean#L78))
   currently has the explicit "this may not hold under sparse ranks" caveat (R2 in the
   plan, and the file header). With dense `assignRanks`, `convergeOnce` writes values from
   `{0, 1, …, m−1}` directly, and the proof becomes induction on fuel + the new dense
   characterization of `assignRanks` output. **The R2 risk and the file-header caveat
   should both be removed/rewritten after the migration succeeds.**

  **[sparse→dense]** **`orderVertices_prefix_invariant`** ([Invariants.lean:173](FullCorrectness/Invariants.lean#L173))
   inductive step needs `breakTie` to preserve the prefix property when fired and be a
   no-op otherwise — both ensured by the new `breakTie` design.

  **[sparse→dense]** **`orderVertices_n_distinct_ranks`** ([Invariants.lean:187](FullCorrectness/Invariants.lean#L187))
   becomes a corollary at p = n.

### Tests to re-run / re-verify

  **[sparse→dense]** **`LeanGraphCanonizerV4Tests.lean` `#guard` checks.** Final canonical
   forms should be unchanged because `labelEdgesAccordingToRankings` already calls
   `computeDenseRanks` at the end, so any sparse-vs-dense difference in intermediate vts
   is squashed by that final pass. **But verify** by rebuilding the test target — most
   `#guard` checks are equality between two canonical forms (invariant), but a few
   compare against literal strings (e.g. the `smoke_*` block) and could regress.

  **[sparse→dense]** **`countUniqueCanonicals` checks** (OEIS A000088). These compare
   *string equality* of canonical forms across all bitmask graphs of size n. The dense
   change shouldn't affect the equality classes (same partition either way), but if it
   does, the count would go wrong. Run `countUniqueCanonicals 4 == 11` as a sanity check.

  **[sparse→dense]** **`vtPointed = #[0, 1, 1, 1, 4, 5, 6]`** ([LeanGraphCanonizerV4Tests.lean:74](LeanGraphCanonizerV4Tests.lean#L74))
   currently uses sparse-style starting types. After `getArrayRank` switches to dense,
   this densifies to `#[0, 1, 1, 1, 2, 3, 4]` at the entry point. The two `g1Pointed`/
   `g2Pointed` graphs should still produce equal canonical forms (the partition under
   the densified vts is the same: vertex 0 alone in class 0, vertices 1/2/3 in class 1,
   vertex 4 in class 2, etc.). Verify this `#guard` still passes after the migration.

### Fallback if `breakTie_Aut_stabilizer` rewrite blows up

If the proof rewrite turns out to be more than ~50 lines beyond what the current proof
spends on `breakTie_getD_of_ne`-driven case analysis, the cleaner factoring is:

  1. Keep `breakTiePromote` with the *current* `breakTie_Aut_stabilizer` proof verbatim
     (literally the existing proof, applied to `breakTiePromote` instead of `breakTie`).
  2. Prove a one-liner `shiftAbove_TypedAut_eq : TypedAut G (shiftAbove t vts) = TypedAut G vts`
     using the bijective-relabeling argument (one direction is `Array.map` preservation
     of the partition; the other direction uses that `shiftAbove t` is injective on the
     value set actually appearing in vts).
  3. Compose: `TypedAut G (breakTie vts t₀) = TypedAut G (breakTiePromote (shiftAbove t₀ vts) t₀)`
     `= [stabilizer of v_star in TypedAut G (shiftAbove t₀ vts)]` (by step 1)
     `= [stabilizer of v_star in TypedAut G vts]` (by step 2).

This factoring keeps the existing proof intact and adds ~30 lines of bijection-of-labels
plumbing instead of rewriting the case analysis.

--------------------------------------------------------------------------------

## §1  Automorphism group, vertex orbits, and permutation action

**Status: proved.** Definitions and theorems live in `Basic`, `Permutation`, `Automorphism`.

### §1.1  Permutation action on `AdjMatrix` (`Permutation.lean`)

`AdjMatrix.permute σ G` relabels the vertices of `G` by `σ`, using `σ.symm` so that
composition is a left action: `G.permute (σ * τ) = (G.permute τ).permute σ`.

Proved:
- `permute_one`                  — `G.permute 1 = G`
- `permute_mul`                  — left-action composition law
- `permute_permute_symm`         — `(G.permute σ).permute σ⁻¹ = G` (round-trip)
- `permute_symm_permute`         — `(G.permute σ⁻¹).permute σ = G`

### §1.2  Bridge to `swapVertexLabels` (`Permutation.lean`)

`swapVertexLabels_eq_permute : swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2)`

Connects the inductive `Isomorphic` generator to the abstract permutation action.
`Equiv.swap v1 v2` is self-inverse (`toFun = invFun` definitionally), which is why
`.symm` reduces by `rfl` here.

### §1.3  Automorphism subgroup (`Automorphism.lean`)

`AdjMatrix.Aut G : Subgroup (Equiv.Perm (Fin n))` — permutations σ with `G.permute σ = G`.

Proved using `permute_one` / `permute_mul` / `permute_permute_symm` for the three
subgroup axioms. Also `mem_Aut_iff_adj` for the pointwise characterization.

### §1.4–§1.6  Orbits and partition (`Automorphism.lean`)

`AdjMatrix.orbit G v := { w | ∃ σ ∈ Aut G, σ v = w }`

`AdjMatrix.orbitSetoid G : Setoid (Fin n)` packages same-orbit as an equivalence relation
(reflexive via `1 ∈ Aut G`, symmetric via inverses, transitive via composition), so the
orbits partition `Fin n` by Lean's quotient infrastructure.

`orbit_stable_under_Aut` — the forward-facing form: `σ ∈ Aut G → σ v ∈ G.orbit v`.

--------------------------------------------------------------------------------

## §2  Bridge lemma: `Isomorphic ↔ ∃ σ, H = G.permute σ`

**Status: planned.** Stub in `Isomorphic.lean`; detailed plan replicated here.

**Target statements:**
```
theorem Isomorphic_of_permute  {σ} (h : H = G.permute σ) : G ≃ H
theorem permute_of_Isomorphic  (h : G ≃ H) : ∃ σ, H = G.permute σ
theorem Isomorphic_iff_exists_permute : G ≃ H ↔ ∃ σ, H = G.permute σ
```

**Why this matters.** The inductive `Isomorphic` relation is generated by `refl`, `swap`,
and `trans`. Direct induction on it is awkward for the equivariance proofs in §3–§6.
The bridge converts `≃` into a single permutation σ, so all downstream reasoning uses
`Equiv.Perm` and its group operations rather than walking a constructor tree.

**Proof — (⟹) direction.** Induction on `h : G ≃ H`:
- `refl G`: take σ := 1; close by `permute_one`.
- `swap G v1 v2`: take σ := `Equiv.swap v1 v2`; close by `swapVertexLabels_eq_permute`.
- `trans h₁ h₂`: IHs give σ₁ with `G₂ = G₁.permute σ₁` and σ₂ with `G₃ = G₂.permute σ₂`.
  Take σ := **σ₂ * σ₁** (order forced by the left-action: `permute_mul` says
  `G.permute (σ₂ * σ₁) = (G.permute σ₁).permute σ₂`).

**Proof — (⟸) direction.** Given `H = G.permute σ`, show `G ≃ H` by induction on a
transposition decomposition of σ via Mathlib's `Equiv.Perm.swap_induction_on`.
Define `P σ := G ≃ G.permute σ`:
- `P 1`: `G ≃ G.permute 1 = G` by `Isomorphic.refl` + `permute_one`.
- `P (Equiv.swap x y * f)` from `P f`: by `permute_mul`,
  `G.permute (swap x y * f) = (G.permute f).permute (swap x y)
   = swapVertexLabels x y (G.permute f)` (by `swapVertexLabels_eq_permute`);
  use `Isomorphic.swap` then `Isomorphic.trans` with the IH.

**Risk R1.** `Equiv.Perm.swap_induction_on` may differ in name on the pinned toolchain;
fallback is induction on `σ.support` size.

**Risk R2.** Composition order (σ₂ * σ₁, not σ₁ * σ₂) must match `permute_mul`
consistently throughout.

--------------------------------------------------------------------------------

## §3  Pipeline equivariance under Aut(G)

**Goal.** For any σ ∈ `Aut G` and any vertex-type array `vts`, the canonizer pipeline
applied to the σ-permuted graph with σ-permuted types produces the σ-permuted output.

Crucially this is quantified over `σ ∈ Aut G`, **not** all of `Sym(Fin n)`. The old flat
proof quantified over all of `Sym(Fin n)`, which is false because `breakTie` is not
equivariant under arbitrary label permutations (only under automorphisms).

**Stage A — `initializePaths`.**
```
σ ∈ Aut G  →  paths in `swapVL-via-σ G` at (d, s, e)
              correspond to paths in G at (d, σ⁻¹ s, σ⁻¹ e)
```
with edge types, vertex indices, and nested `PathSegment` structures all relabeled by σ.
Proof by induction on depth; the action on `PathSegment`/`PathsBetween`/`PathsFrom` lifts
componentwise from the Fin-level action.

**Stage B — `calculatePathRankings`.** If the input `PathState` and `vertexTypes` are
σ-related, then the output ranks satisfy
```
ranks'.betweenRanks[d][s][e] = ranks.betweenRanks[d][σ⁻¹ s][σ⁻¹ e],
ranks'.fromRanks[d][s]       = ranks.fromRanks[d][σ⁻¹ s].
```
Proof by induction on depth, using that `comparePathSegments` / `comparePathsBetween` /
`comparePathsFrom` only depend on σ-invariant features (edge types and endpoint vertex
types are preserved because σ ∈ Aut G; the recursive rank references are equivariant by IH).

**Stage C — `orderVertices`.** `convergeOnce` reads `fromRanks` (equivariant by Stage B),
so it preserves the relation. `breakTie` is the interesting case — it is equivariant under
`Aut(G)` (not under `Sym(Fin n)`) *at each outer-loop iteration*, because the vertices it
chooses between are all in the same Aut(G)-orbit. See §6 for why the *choice* of which
tied vertex to promote doesn't affect the final answer.

**Stage D — `labelEdgesAccordingToRankings`.** With distinct ranks (§7), the vertex at
position p in the σ-permuted sort is σ applied to the vertex at position p in the original.
The edge at (p, q) is then `(σ·G).adj(σwₚ)(σwₙ) = G.adj wₚ wₙ` by the Aut(G) property.

**Deliverable.** Four equivariance theorems in `FullCorrectness/Equivariance.lean`:
```
initializePaths_Aut_equivariant      : σ ∈ Aut G → ...  (Stage A)
calculatePathRankings_Aut_equivariant: σ ∈ Aut G → ...  (Stage B)
orderVertices_Aut_equivariant        : σ ∈ Aut G → ...  (Stage C, modulo §6)
labelEdges_Aut_equivariant           : σ ∈ Aut G → ...  (Stage D, given §7)
```

## §4  `convergeLoop` output is Aut(G)-invariant

**Goal.**
```
σ ∈ Aut G  ∧  (∀ v, vts[σ v] = vts[v])  →  ∀ v, (convergeLoop state vts fuel)[σ v]
                                                  = (convergeLoop state vts fuel)[v]
```
i.e. if the input vertex types are Aut(G)-invariant, so is the output.

**Why.** `convergeOnce` writes `rankState.getFrom (n-1) v` into slot `v`. That value
depends only on paths-from-v; any σ ∈ Aut G bijects paths-from-v with paths-from-(σv)
preserving edge types and endpoint types (the endpoint types are Aut-invariant by the IH
on vertex-types). So the multisets fed into `comparePathsFrom` are identical, the ranks
are identical, and Aut-invariance is preserved. Induct on the fuel parameter.

**Corollary.** Starting from the all-zeros array (which is trivially Aut-invariant), after
`convergeLoop`, vertices in the same Aut(G)-orbit carry the same type.

**Deliverable.** One theorem in `FullCorrectness/Equivariance.lean`:
```
convergeLoop_Aut_invariant : σ ∈ Aut G → vts σ-invariant → convergeLoop output σ-invariant
```

## §5  `breakTie` shrinks the typed-automorphism group

Let `Aut(G, T)` := `{ σ ∈ Aut G | σ permutes T as a bijection on equal values }` be the
automorphisms preserving a given typing T. This is a subgroup of `Aut G`.

**Goal.** Let T be Aut(G)-invariant, let t₀ be the smallest value held by at least two
vertices, let V_{t₀} be its type-class, let v* := min V_{t₀} (by Fin order), and let
T' := `breakTie T t₀` (which promotes every vertex in V_{t₀} except v*). Then
```
Aut(G, T')  =  { σ ∈ Aut(G, T) | σ v* = v* }                         (stabilizer of v*)
```

**Why.** σ ∈ Aut(G, T') iff σ preserves T' iff σ sends the unique type-t₀ vertex (v*) to
itself and sends V_{t₀} \ {v*} to itself. The first condition forces σ v* = v*; the second
is then automatic given σ ∈ Aut(G, T).

**Strict shrinking.** If |V_{t₀}| ≥ 2, then v* is not Aut(G, T)-fixed (all elements of V_{t₀}
are in the same Aut(G, T)-orbit by §4's corollary, and there are ≥ 2 of them), so the
stabilizer is a proper subgroup. After each tiebreak, the typed-automorphism group strictly
shrinks; after at most n tiebreaks it is trivial (all types distinct).

**Deliverable.** Both theorems are now proved in `FullCorrectness/Tiebreak.lean`:
```
breakTie_Aut_stabilizer  : [with hsize + hAutInv]
    σ ∈ TypedAut G (breakTie vts t₀).1  ↔  (σ ∈ TypedAut G vts ∧ σ v* = v*)
breakTie_TypedAut_le     : TypedAut G (breakTie vts t₀).1 ≤ TypedAut G vts
breakTie_strict_shrink   : [with hmove] TypedAut G (breakTie vts t₀).1 < TypedAut G vts
```

Four position-by-position characterization lemmas underpin the proofs:
```
breakTie_size             : (breakTie vts t₀).1.size = vts.size
breakTie_getD_of_ne       : vts[j] ≠ t₀ → (breakTie vts t₀).1[j] = vts[j]
breakTie_getD_at_min      : v_star is min of typeClass → (breakTie vts t₀).1[v_star] = t₀
breakTie_getD_at_other    : w ≠ v_star in typeClass → (breakTie vts t₀).1[w] = t₀ + 1
```
These follow from an induction-on-the-fold argument with three helper lemmas
(`btFold_no_target`, `btFold_from_notfirst_getD`, `btFold_getD_not_mem`) tracking how
the `firstAppearance` flag flips at the first target encounter.

See the "§5 hypothesis revisions" note at the top of this file for why the proved
forms differ slightly from the original sketch (`breakTie_Aut_stabilizer` requires `vts`
to be Aut-invariant; `breakTie_strict_shrink` requires an explicit `hmove` hypothesis
rather than deriving strictness from `|V_{t₀}| ≥ 2`).

## §6  Tiebreak choice-independence (the conceptual crux)

This is the step the old flat proof did not need — because it assumed `breakTie` never
fires — and the reason the flat proof fails once tiebreaks are real.

**Goal.** Let T be Aut(G)-invariant. Let t₀ be the smallest repeated value, and let v₁, v₂
be any two vertices in V_{t₀} (so by §4 they are in the same Aut(G, T)-orbit). Let T₁ / T₂
be the result of promoting v₁ / v₂ respectively. Then
```
 Run the remainder of the canonizer pipeline (including all subsequent tiebreaks and the
 final relabel) starting from (G, T₁) vs. (G, T₂). The **final canonical matrices are equal.**
```

**Why.** Let τ ∈ Aut(G, T) with τ v₁ = v₂ (exists by same-orbit). Then the pair (G, T₂)
equals τ · (G, T₁) in the sense that G is τ-invariant (τ ∈ Aut G) and T₂ = τ · T₁ (the
promoted-type array, permuted by τ, matches the other choice). By Aut(G)-equivariance of
the remaining pipeline (§3), running on τ · (G, T₁) produces τ · (final output). But the
final output has all types distinct, so the relabel step in §8 sorts τ away, producing the
same canonical matrix.

Formally this is proved by **strong induction on |Aut(G, T)|**:

  Base: `|Aut(G, T)| = 1` → T has all types distinct → no more tiebreaks → relabel is
        deterministic, result is independent of all upstream choices.

  Step: `|Aut(G, T)| > 1` → by §5, next tiebreak further shrinks the group. Any two choices
        of promoted representative are in the same Aut(G, T)-orbit, so the promoted-type
        arrays are τ-related. Apply §3 equivariance + IH.

**Deliverable.** One theorem in `FullCorrectness/Tiebreak.lean`:
```
tiebreak_choice_independent : ∀ (two τ-related states), same final canonical output
```

## §7  "Converged types are a prefix of ℕ" invariant

`orderVertices` calls `breakTie convergedTypes targetPosition` where `targetPosition`
is the outer-loop counter `0, 1, …, n-1`, NOT the smallest tied value. For §5/§6 to
apply, we need: at iteration p, the smallest tied value is exactly p.

**Goal.**
```
∀ p ≤ n, after p outer iterations, the typing takes values exactly in {0, 1, …, p-1, k}
         where k is either the next tied value (= p, if one exists) or n (if all distinct).
```

**Why.** Initial types from `convergeLoop` form a prefix-of-ℕ ranking (this follows from
`assignRanks`, which assigns the index of the first element in each equivalence class;
after dense-rank normalization, values are exactly 0..m-1 for some m ≤ n). Each `breakTie`
with target p leaves values 0..p-1 unchanged and promotes some value-p vertices to p+1
(which may then be re-dense-ranked by the next `convergeLoop` call — verify this claim is
preserved by `convergeLoop` on a prefix typing).

**Deliverables in `FullCorrectness/Invariants.lean`:**
```
convergeLoop_preserves_prefix      : 🧱 sorry (depends on density of `assignRanks`)
breakTie_targetPos_is_min_tied     : ✅ proved (via `breakTie_getD_target` from §5)
orderVertices_prefix_invariant     : 🧱 sorry (induct on the outer fold)
orderVertices_n_distinct_ranks     : 🧱 sorry (corollary at p = n)
```

**`breakTie_targetPos_is_min_tied` is now proved.** The argument: assume by contradiction
that two distinct vertices `w₁ ≠ w₂` share an output value `val ≤ p`. By `breakTie_getD_target`,
target-valued positions land on `{p, p+1}`; since `p+1 > p`, an output `≤ p` rules out
promotion, so `output[w_i] = vts[w_i]` (preserved). Two sub-cases on `val`:
- `val < p`: by the prefix-uniqueness hypothesis at `k := val.toNat`, `w₁ = w₂`. ⊥.
- `val = p`: both `vts[w_i] = p`, so any `w_i ≠ v_star` (= the smallest target-valued
  index, found via `Nat.find`) would land on `p+1` by `breakTie_getD_at_other` — contradicting
  `output[w_i] = p`. So both `w_i = v_star`, hence equal. ⊥.

**Watch-out.** If the algorithm's rank assignment is not dense (e.g. skips values), the
remaining `convergeLoop_preserves_prefix` invariant fails, and the whole argument unravels.
Check `assignRanks` + `computeDenseRanks` carefully — or restate the invariant against the
dense-rank composition.

## §8  Assembling `run_canonical`

With §1–§7 in hand:

**(→)** Given G ≃ H. By §2, there is σ : Equiv.Perm (Fin n) with H = G.permute σ. We want
`run 0 H = run 0 G`. Decompose the pipeline:

  1. `initializePaths` + `convergeLoop` + all iterations of `breakTie`/`convergeLoop` →
     some final typing T_G (for G) / T_H (for H).
  2. `labelEdgesAccordingToRankings T_G G` / `labelEdgesAccordingToRankings T_H H`.

The pipeline applied to H = G.permute σ with the all-zeros input is related by σ to the
pipeline applied to G. For the part of σ inside Aut G, this is §3 + §4 equivariance (T_H
is σ·T_G up to tiebreak choices, and §6 says those don't matter). For the part of σ outside
Aut G… there is no "outside" — σ takes G to G.permute σ = H, and H ≃ G, so this is just
restating that G, H are isomorphic. The canonical output depends on the abstract graph,
not the labeling.

**(←)** Given `run 0 G = run 0 H`. By `run_isomorphic_to_input` (proved in §4 of the flat
file, reused here), G ≃ run 0 G and H ≃ run 0 H. Chain:
```
G ≃ run 0 G = run 0 H ≃⁻¹ H   ⟹   G ≃ H.
```
This direction re-uses the genuinely-proved §4 lemma from the old flat file.

**Deliverable.** The capstone theorem in `FullCorrectness/Main.lean`:
```
theorem run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

--------------------------------------------------------------------------------

## Risks and open invariants

**R1.** §6 strong induction requires `|Aut(G, T)|` to be a well-founded measure. Trivial
with `Fintype`, but we need to actually put a `Fintype` instance on `Aut(G, T)` (it is a
subgroup of `Sym(Fin n)` which is finite).

**R2.** ~~§7's prefix-of-ℕ invariant assumes dense ranking throughout. Verify in
`assignRanks` and `computeDenseRanks` that values are always exactly 0..m-1.~~
**Resolved by the sparse → dense ranking migration:** `assignRanks` now produces dense
ranks; `getArrayRank` densifies at the entry point; `breakTie` uses shift-then-promote
to preserve density across iterations. The `convergeLoop_preserves_prefix` and downstream
§7 sorries are now reachable (proofs pending).

**R3.** `convergeLoop` is given fuel equal to `state.vertexCount`. Correctness does not
require it to actually reach a fixed point — §4 says the output is always Aut-invariant,
fixed point or not — but we should double-check that "output is Aut-invariant at every
iteration" is what induction gives us, not the weaker "fixed point is Aut-invariant."

**R4.** §2's (⟸) direction uses Mathlib's `Equiv.Perm.swap_induction_on`; the exact name
on the pinned toolchain (`leanprover/lean4:v4.30.0-rc2` + Mathlib master) needs to be
confirmed. Fallback: induct on `σ.support` size.

**R5.** `Fin`/`Nat` bounds on `set!`, `getD`, and the array-index arithmetic throughout
will produce side conditions. Collect into a single `def` + lemmas file if they multiply.

## Suggested development order

Serial dependencies run §1 → §2 → §3 → §4 → (§5 ∥ §7) → §6 → §8. The independent
work (Mathlib-facing infrastructure: §1 done; §2 is mostly Mathlib-plumbing) can proceed
in parallel with algorithm-facing work (§3–§5 are about the specific data structures of
this canonizer).

§6 is the single hardest step and should be the budgeting focus once §3–§5 are in place.
-/
