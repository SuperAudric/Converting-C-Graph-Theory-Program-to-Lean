import FullCorrectness.Basic
import FullCorrectness.Permutation
import FullCorrectness.Automorphism
import FullCorrectness.Isomorphic
import FullCorrectness.Equivariance.Actions
import FullCorrectness.Equivariance.StageA
import FullCorrectness.Equivariance.RankStateInvariants
import FullCorrectness.Equivariance.ComparisonSort
import FullCorrectness.Equivariance.ComparePathSegments
import FullCorrectness.Equivariance.CompareEquivariant
import FullCorrectness.Equivariance.PathsAtDepthStructure
import FullCorrectness.Equivariance.ChainSetInvariant
import FullCorrectness.Equivariance.AssignListRankClosure
import FullCorrectness.Equivariance.LabelEdgesCharacterization
import FullCorrectness.Equivariance.PathEquivariance
import FullCorrectness.Equivariance.PathEquivarianceRelational
import FullCorrectness.Equivariance.ConvergeLoop
import FullCorrectness.Equivariance.ConvergeLoopRelational
import FullCorrectness.Tiebreak
import FullCorrectness.Equivariance.BreakTieRelational
import FullCorrectness.Equivariance.StageDRelational
import FullCorrectness.Equivariance.RunFromRelational
import FullCorrectness.Equivariance.MainRelationalNotes
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

| Step | Subject                                           | File                                     | Status          |
| ---- | ------------------------------------------------- | ---------------------------------------- | --------------- |
| §1   | Automorphism group, orbits, `permute` action      | `Basic`, `Permutation`, `Automorphism`   | ✅ proved       |
| §1.7 | `Fintype G.Aut` (decidability + finiteness)       | `Automorphism`                           | ✅ proved       |
| §2   | `Isomorphic ↔ ∃σ, H = G.permute σ` bridge         | `Isomorphic`                             | ✅ proved       |
| §3   | `permNat` + `PathSegment/PathsBetween/...permute` | `Equivariance.Actions`                   | ✅ defined      |
| §3A  | `initializePaths_Aut_equivariant` (Stage A)       | `Equivariance.StageA`                    | ✅ proved       |
| §3B  | `calculatePathRankings` size + `σInvariant`       | `Equivariance.RankStateInvariants`       | ✅ proved       |
| §3B  | Generic sort/`orderInsensitiveListCmp` lemmas     | `Equivariance.ComparisonSort`            | ✅ proved (`assignRanks_rank_eq_within_eq_class` + `_at_succ_when_cmp_eq` closed) |
| §3B  | `comparePathSegments_total_preorder` (Stage B)    | `Equivariance.ComparePathSegments`       | ✅ proved; `comparePathsBetween_total_preorder` ✅ proved |
| §3B  | σ-equivariance of compare/sort; Stage B assembly  | `Equivariance.PathEquivariance`          | ✅ proved (`from_assignList_σ_rank_closure`, `between_assignList_σ_rank_closure`, `calculatePathRankings_fromRanks_inv`, `calculatePathRankings_betweenRanks_inv` all closed via `calculatePathRankings_σ_cell_inv_facts` + foldl body lemma) |
| §4   | `convergeOnce`/`convergeLoop` Aut-invariance; C/D | `Equivariance.ConvergeLoop`              | ✅ proved       |
| §5   | `TypedAut G vts` (subgroup + Fintype)             | `Tiebreak`                               | ✅ defined      |
| §5.0 | `breakTie` output position-by-position            | `Tiebreak`                               | ✅ proved (4 characterization lemmas) |
| §5.1 | `breakTie` is the v*-stabilizer of `TypedAut`     | `Tiebreak`                               | ✅ proved (with `hAutInv`/`hsize`) |
| §5.2 | `breakTie` strictly shrinks `TypedAut`            | `Tiebreak`                               | ✅ proved (with `hmove`) |
| §6.0 | `breakTieAt` output + τ-equivariance              | `Tiebreak`                               | ✅ proved (3 characterization + 1 equivariance) |
| §6   | Tiebreak choice-independence (conceptual crux)    | `Tiebreak`                               | ✅ closed modulo `runFrom_VtsInvariant_eq` (see "Stage B/D gap" below) |
| §7   | `IsPrefixTyping` definition + zeros instance      | `Invariants`                             | ✅ defined + boundary proved |
| §7   | `breakTie_targetPos_is_min_tied`                  | `Invariants`                             | ✅ proved (uses §5 disjunctive characterization) |
| §7   | Other prefix invariants                           | `Invariants`                             | ✅ all proved (`getFrom_image_isPrefix_for_initializePaths`, `convergeLoop_preserves_prefix`, `n_distinct_ranks`, `orderVertices_prefix_invariant`, §7-Step 2 breakTie step, §7-Step 3 convergeLoop_preserves_lower_uniqueness) |
| §8   | Assemble `run_canonical_correctness`              | `Main`                                   | 🧱 assembled, (⟹) `sorry`; (⟸) proved |

## Open obligations (3 sorry sites)

| Sorry | Location | What's needed |
| ----- | -------- | ------------- |
| `runFrom_VtsInvariant_eq`             | `Tiebreak`                         | **Net-new infrastructure**, NOT mechanical chaining of existing Stages A–D. See "Stage B/D gap" below. |
| `runFrom_VtsInvariant_eq_strong`      | `Equivariance/RunFromRelational`   | Phase 5 joint induction (Phase 3 now closed; Phase 3.E is the leaf). |
| `run_isomorphic_eq_new` (⟹)           | `Main`                             | Assemble §3 + §4 + §6 against the σ from §2; current sketch routes through `tiebreak_choice_independent`, hence inherits the Stage B/D gap. |

**`Invariants.lean` and `Equivariance.PathEquivariance.lean` are both fully closed.**
`orderVertices_prefix_invariant`, `orderVertices_n_distinct_ranks`,
`calculatePathRankings_fromRanks_inv`, and `calculatePathRankings_betweenRanks_inv` are all
proved unconditionally.

## The Stage B/D gap blocking `runFrom_VtsInvariant_eq`

The original plan billed `runFrom_VtsInvariant_eq` as "mechanical given Stages A–D." On
inspection that is **not accurate**: the existing Stages A–D are stated in *fixed-point*
form (single σ-INVARIANT array applied to the same/permuted graph), but
`runFrom_VtsInvariant_eq` needs *relational* equivariance — TWO τ-related arrays
`arr₁, arr₂` (with `arr₂[w] = arr₁[τ⁻¹ w]`) feeding the same `G`, where neither array
is τ-fixed.

What the proven Stages give vs. what the runFrom proof needs:

| Stage | Proven form                                                                                                       | Needed (relational) form                                                                                          |
| ----- | ----------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| A     | General σ: `initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)`                              | (already general — reusable as-is)                                                                                |
| B     | σ ∈ Aut G **AND** σ-INV vts ⟹ `RankState.permute σ rs = rs` (σ-fixed point)                                       | σ ∈ Aut G, ANY vts: `calculatePathRankings (init G) (σ·vts) = RankState.permute σ (calculatePathRankings (init G) vts)` |
| C     | σ-INV form: `convergeLoop` preserves σ-INVARIANCE of a single array                                               | σ-related form: τ-related arrays produce τ-related convergeLoop outputs                                            |
| D     | `labelEdges vts (G.permute σ) = labelEdges vts G` for σ ∈ Aut G (same vts on permuted graph)                      | `labelEdges (σ·rks) G = labelEdges rks G` for σ ∈ Aut G AND tie-free rks (different rks on same graph)             |

The σ-cell-INV proof in `Equivariance.PathEquivariance` rests crucially on
`comparePathsFrom_σ_self_eq` which requires σ-INV vts (so that `cmp p (σ·p) = .eq`).
Lifting Stage B to the relational form requires redoing the foldl-induction body in a
relational form (~few hundred lines, comparable to the σ-cell-INV proof itself).

Stage D-rel is even less direct: the `denseRanks` step uses `(rank, vertex-index)`
lexicographic order. Under τ-relabeling, the secondary key `vertex-index` gets
τ-permuted, so the dense-ranks-as-permutation argument requires either tie-freeness
of `rks` at this step, or a structural theorem about `labelEdgesAccordingToRankings`
that factors through the inverse of `denseRanks`.

### Three reasonable resolutions

1. **Build the relational stages.** Mirror the σ-cell-INV machinery in relational form
   (Stage B-rel, C-rel) plus a structure theorem for `labelEdges` (Stage D-rel). Estimate:
   500–1000 lines, comparable to the work that closed `calculatePathRankings_*_inv`.
2. **Find a different proof of `run_isomorphic_eq_new`** that bypasses
   `tiebreak_choice_independent` entirely. If successful, both sorries close together
   without going through the gap. Risky — current sketch uses §6 essentially.
3. **Acknowledge `runFrom_VtsInvariant_eq` as the entry point** for canonicalization
   correctness and accept it as a "deep" lemma requiring net-new work; do not pretend it
   is downstream of the existing Stages.

The plan was to attempt path 2 first (cheaper if it works), falling back to
path 1 when no alternative proof shape presented itself.

### Refactor of Stage B (σ-INV form) — landed

Before lifting Stage B to relational form, the 2609-line `Equivariance/PathEquivariance.lean`
has been split into 5 modular files (1–2 logical concerns each). All sub-lemmas the
σ-INV proof depends on are now in dedicated modules:

| File | Lines | Content |
| ---- | ----- | ------- |
| `Equivariance/CompareEquivariant.lean`           | 523 | σ-equivariance of `comparePathSegments`/`...PathsBetween`/`...PathsFrom`; `PathsBetween_permute_connectedSubPaths_perm`, `PathsFrom_permute_pathsToVertex_perm`; bridge helpers (`betweenRankFn_σ_inv_from_cells`, `initializePaths_σInv_via_Aut`). |
| `Equivariance/PathsAtDepthStructure.lean`        | 231 | `initializePaths_pathsAtDepth_structure`, `initializePaths_pathsAtDepth_inner_structure`, `initializePaths_allBetween_pairs_facts`. |
| `Equivariance/ChainSetInvariant.lean`            | 693 | 1D and 2D chain σ-invariance preservation: `set_chain_σInvariant`, `setBetween_chain_σInvariant` and their size-preservation helpers. |
| `Equivariance/AssignListRankClosure.lean`        | 835 | σ-self-equality of compare functions; σ-rank-closure of `assignList` (`from_assignList_σ_rank_closure`, `between_assignList_σ_rank_closure`). |
| `Equivariance/PathEquivariance.lean`             | 401 | Stage B assembly only: `CalcRankingsInv`, body step, foldl induction, `calculatePathRankings_Aut_equivariant`. |

### Stage B-rel (relational form) — foundational lemmas all proved

A new module `Equivariance/PathEquivarianceRelational.lean` (~1500 lines) contains the
relational analogues of the foundational lemmas, plus auxiliary additions to
`ComparisonSort.lean`. **Status: all foundational pieces closed; only the body-step
and final Stage B-rel assembly remain.**

| Component | Status |
| --------- | ------ |
| `comparePathSegments_σ_relational`                                     | ✅ proved |
| `comparePathsBetween_σ_relational`                                     | ✅ proved |
| `comparePathsFrom_σ_relational`                                        | ✅ proved |
| `sortBy_map_pointwise_relational`                                      | ✅ proved |
| `orderInsensitiveListCmp_map_pointwise_relational`                     | ✅ proved |
| `set_chain_σRelated`                                                   | ✅ proved |
| `setBetween_chain_σRelated`                                            | ✅ proved |
| `assignRanks_map_relational` (in `ComparisonSort.lean`)                | ✅ proved (relational lift of `assignRanks_map_of_cmp_respect`) |
| `assignRanks_rank_succ_when_cmp_neq_eq` (in `ComparisonSort.lean`)     | ✅ proved (dual of `assignRanks_rank_eq_at_succ_when_cmp_eq` for the `.lt`-step case) |
| `assignRanks_rank_eq_of_sorted_perm` (in `ComparisonSort.lean`)        | ✅ proved (rank at each position is the same for sorted Perm-equivalent inputs; the missing technical gap from the previous status) |
| `pathsAtDepth_map_f_perm`                                              | ✅ proved (via `map_reindex_perm` + state σ-fixedness) |
| `allBetween_map_f_perm`                                                | ✅ proved (via `flatMap_eq_foldl` + `Perm.flatMap_left` + `pathsAtDepth_map_f_perm`) |
| `from_assignList_σ_rank_rel`                                           | ✅ proved |
| `between_assignList_σ_rank_rel`                                        | ✅ proved |
| Body step + foldl induction + `Stage B-rel` assembly                   | ✅ proved (Phase 1 landed: `calculatePathRankings_σ_equivariant_relational`) |

With both relational σ-rank-closure lemmas closed, the remaining work is to assemble:
1. A relational body step (parallel to `calculatePathRankings_body_preserves_inv` in
   `PathEquivariance.lean`) that uses `set_chain_σRelated` / `setBetween_chain_σRelated`
   with the σ-rank-rel lemmas as the σ-closure hypotheses.
2. A foldl induction over `List.range n` (parallel to `calculatePathRankings_σ_cell_inv_facts`).
3. The final `calculatePathRankings_σ_equivariant_relational` assembly.

This is mechanical given the foundational lemmas above.

--------------------------------------------------------------------------------

## Phase status snapshot (updated)

| Phase | Subject                                              | Status |
| ----- | ---------------------------------------------------- | ------ |
| 1     | Stage B-rel assembly (`calculatePathRankings_σ_equivariant_relational`) | ✅ closed |
| 2     | Stage C-rel (`convergeOnce_VtsInvariant_eq`, `convergeLoop_VtsInvariant_eq`) | ✅ closed |
| 4     | `breakTieAt_τ_related`, `shiftAbove_VtsInvariant_eq` | ✅ closed |
| 3     | Stage D-rel (cell-wise + denseRanks + assembly)      | ✅ closed (all of 3.A–3.E) |
| 5     | `runFrom_VtsInvariant_eq_strong`                     | 🟦 stated with right hypotheses + transfer helpers closed; main proof pending joint induction |
| 6     | `run_isomorphic_eq_new`                              | 🟦 documented; needs generalized stages |

### Phase 3 inner sub-decomposition (top-level relational)

**Naming convention** (avoids collision with §7-Step terminology above): the relational
Phase 3 (Stage D-rel) is sub-decomposed as Phase 3.A through Phase 3.E. Each sub-phase
has a unique single-letter suffix, and the "Phase 3.X" prefix is always used (no
abbreviation).

| Sub-phase | Lemma                                                 | File                                | Status |
| --------- | ----------------------------------------------------- | ----------------------------------- | ------ |
| Phase 3.A | `computeDenseRanks_size`                              | `LabelEdgesCharacterization.lean`   | ✅ proved |
| Phase 3.B | Cell-wise characterization (the three lemmas below)   | `LabelEdgesCharacterization.lean`   | ✅ proved |
|           |  – `labelEdges_fold_permutes` (existence of σ)        |                                     | ✅ proved |
|           |  – `labelEdges_fold_strong` (σ + `rankMap = rankMap_0 ∘ σ⁻¹`) |                             | ✅ proved |
|           |  – `rankMap_swap_step_eq` (helper)                    |                                     | ✅ proved |
|           |  – `labelEdges_terminal_rankMap_identity`             |                                     | ✅ proved |
| Phase 3.C | `computeDenseRanks_τ_shift_distinct`                  | `StageDRelational.lean`             | ✅ proved |
| Phase 3.D | `computeDenseRanks_perm_when_tieFree`                 | `StageDRelational.lean`             | ✅ proved |
| Phase 3.E | `labelEdges_VtsInvariant_eq_distinct` (assembly)      | `StageDRelational.lean`             | ✅ proved |

**All of Phase 3 is now closed.** The structural denseRanks lemmas (3.C, 3.D) use the
relational `sortBy` machinery and a `pairCmp` strict-lex characterization, plus a new
`sortBy_eq_of_perm_strict` helper added to `ComparisonSort.lean`. Phase 3.E assembles
via `labelEdges_fold_strong` + `labelEdges_terminal_rankMap_identity` and an
injectivity-of-`computeDenseRanks` lemma (no tie-freeness required for injectivity).

--------------------------------------------------------------------------------

## Plan of attack for the remaining theorems

**Top-level goal**: close `runFrom_VtsInvariant_eq` (Tiebreak.lean) and
`run_isomorphic_eq_new` (Main.lean), and the structurally-connected sub-sorries
(Phase 3.C, 3.D, 3.E; Phase 5; Phase 6).

**Dependency graph**:

```
Main.run_isomorphic_eq_new                       (Phase 6)
  ↓ uses
runFrom_VtsInvariant_eq_strong                   (Phase 5)
  ↓ uses
labelEdges_VtsInvariant_eq_distinct              (Phase 3.E)
  ↓ uses
computeDenseRanks_τ_shift_distinct               (Phase 3.C) +
computeDenseRanks_perm_when_tieFree              (Phase 3.D) +
[labelEdges_fold_strong + labelEdges_terminal_rankMap_identity]  (Phase 3.B, ✅ closed)
```

### Phase 3.C — `computeDenseRanks_τ_shift_distinct` (~120-150 lines)

**File**: `Equivariance/StageDRelational.lean`.

**Statement**:
```
∀ w : Fin n,
  (computeDenseRanks n rks₂).getD w.val 0
  = (computeDenseRanks n rks₁).getD (τ⁻¹ w).val 0
```
under hypotheses tie-freeness of both AND τ-relation `rks₂[w] = rks₁[τ⁻¹ w]`.

**Approach (preferred — direct via the fold characterization)**:

This is the substantial structural lemma. Two viable routes:

  **Route A** — characterize denseRanks as `#{u | (rks[u], u) lex < (rks[v], v)}` and
  show this counting transforms cleanly under τ. Under tie-freeness, the `(·, u)`
  secondary key is irrelevant, so denseRanks reduces to `#{u | rks[u] < rks[v]}`,
  which transforms by change of variables `u ↦ τ⁻¹ u`. Cleanest math; needs careful
  formalization with `List.countP` or `Finset.filter`.

  **Route B** — compare the two `pairs` lists step-by-step. The pairs for `rks₂` are
  the τ-image of pairs for `rks₁` (under the second component). Sort both; under
  tie-freeness, the sorts are determined by primary key alone, so the sorts are equal
  up to a τ-relabeling of second components. Then the foldl outputs differ by a τ-shift.

**Key lemmas / tools**:
  - Existing relational sortBy machinery in `PathEquivarianceRelational.lean`:
    `sortBy_map_pointwise_relational`, `assignRanks_map_relational`. These are the
    pattern; lift them to `(VertexType × Nat)` lex sort under tie-freeness.
  - `Equiv.Perm.bijective` for the change-of-variables in Route A.
  - `List.countP_filter` and `Finset.card_image_of_injective` if going via Finset.

**Risk: medium.** Route A is cleanest mathematically; Route B parallels existing
machinery (cheaper to set up, more verbose).

### Phase 3.D — `computeDenseRanks_perm_when_tieFree` (~70-100 lines)

**File**: `Equivariance/StageDRelational.lean`.

**Statement**:
```
∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks).getD w.val 0 = k.val
```
under hypotheses `rks.size = n` and `TieFree rks n`.

**Approach**:
1. Unfold `computeDenseRanks`: `pairs = (List.range n).map (fun i => (rks[i], i))`,
   `sorted = sortBy lex_cmp pairs`, then foldl writes `sortedIdx → position pairs[sortedIdx].2`.
2. Show `pairs.length = n`, hence `sorted.length = n` (via `sortBy_perm` / `Perm.length_eq`).
3. For target value `k.val`, witness vertex `w := (sorted.getD k.val (0,0)).2`. Show:
   - `w < n` because `pairs` second components ⊆ `[0, n)` and `sorted ~ pairs` (Perm).
   - The fold's set! at position `w` writes value `k.val` (the matching `sortedIdx`).
   - No subsequent set! overwrites position `w` — by Nodup of `sorted.map (·.2)` (which
     follows from Nodup of `pairs.map (·.2)` = `List.range n` + sort is a Perm).

**Key lemmas to use**:
  - `sortBy_perm` (in `ComparisonSort.lean`): the sort is a permutation of input.
  - `List.Perm.length_eq`, `List.Perm.nodup_iff`.
  - `array_set_chain_at_target_nodup` (in `RankStateInvariants.lean`): when you write to
    a list of distinct targets, reading at any specific target gives the written value.
    **This is the workhorse** — same pattern as in `set_chain_σInvariant`'s proof.

**Risk: medium-low.** Familiar pattern (set!-chain with Nodup keys); main work is the
unfold of `computeDenseRanks` and tracking the fold structure.

### Phase 3.E — `labelEdges_VtsInvariant_eq_distinct` assembly (~80-120 lines)

**File**: `Equivariance/StageDRelational.lean`.

**Statement** (already in file):
```
τ ∈ Aut G → tie-free rks₁, rks₂ → τ-related →
labelEdges rks₂ G = labelEdges rks₁ G
```

**Proof plan** (with all closed/pending lemmas named):

1. Unfold both labelEdges to `(List.finRange n).foldl (labelEdgesStep n (List.finRange n)) (G, computeDenseRanks n rks_i)`.

2. Apply `labelEdges_fold_strong` (✅) on side 1 with σ := id and rankMap_0 := computeDenseRanks rks₁:
   - get σ_1 with `output_1.1 = G.permute σ_1` and `output_1.2.getD v.val 0 = (computeDenseRanks rks₁).getD (σ_1⁻¹ v).val 0`.

3. Apply `labelEdges_fold_strong` (✅) on side 2 with σ := τ⁻¹ (using `_hτ : τ ∈ Aut G ⟹ G = G.permute τ⁻¹` via `permute_permute_symm`) and rankMap_0 := computeDenseRanks rks₁:
   - The required hypothesis `acc.2 = rankMap_0 ∘ σ⁻¹` here is
     `(computeDenseRanks rks₂).getD v.val 0 = (computeDenseRanks rks₁).getD (τ v).val 0`, which is **Phase 3.C** (with σ = τ⁻¹).
   - get σ_2 with `output_2.1 = G.permute σ_2` and `output_2.2.getD v.val 0 = (computeDenseRanks rks₁).getD (σ_2⁻¹ v).val 0`.

4. Apply `labelEdges_terminal_rankMap_identity` (✅) on both sides — the multiset hypothesis is **Phase 3.D** for each rks_i. Get:
   - `output_1.2.getD v.val 0 = v.val`.
   - `output_2.2.getD v.val 0 = v.val`.

5. Combine 2/3 with 4: `(computeDenseRanks rks₁).getD (σ_1⁻¹ v).val 0 = v.val = (computeDenseRanks rks₁).getD (σ_2⁻¹ v).val 0`.

6. By tie-freeness of rks₁ + Phase 3.D (denseRanks is a permutation), `computeDenseRanks rks₁` is injective on `Fin n`. Hence σ_1⁻¹ v = σ_2⁻¹ v, so σ_1 = σ_2.

7. Conclude `output_1.1 = G.permute σ_1 = G.permute σ_2 = output_2.1`.

**Risk: low.** Algebraic; the heavy lifting is in Phase 3.D and Phase 3.C.

### Phase 5 — `runFrom_VtsInvariant_eq_strong` joint induction (~250-300 lines)

**File**: `Equivariance/RunFromRelational.lean` (extend).

**Statement** (already in file): see `runFrom_VtsInvariant_eq_strong` with hypotheses
`(IsPrefixTyping arr₁) ∧ (UniquelyHeldBelow arr₁ s) ∧ (s ≤ n)`.

**Strategy**: joint induction on `m := n - s` together with a strengthened
`tiebreak_choice_independent_strong` (also taking the prefix hypothesis).

**Joint statement** (informal):
```
P(m) := ∀ s, n - s = m →
        (P₁) runFrom_VtsInvariant_eq_strong at this s holds, AND
        (P₂) tiebreak_choice_independent_strong at this s+1 (sub-call form) holds.
```

**Base case** (m = 0, s = n):
- foldl in `runFrom n arr G` is empty; orderedRanks = arr.
- `UniquelyHeldBelow arr n` (from hypothesis with q = n) means values 0..n-1 each
  uniquely held — i.e., `TieFree arr n`. Same for arr₂ via `UniquelyHeldBelow_τ_transfer` (✅).
- Apply `labelEdges_VtsInvariant_eq_distinct` (Phase 3.E). Done.

**Inductive step** (m = k+1):
1. **Convergence step.** ct_i := `convergeLoop (initializePaths G) arr_i n`. By Phase 2
   (`convergeLoop_VtsInvariant_eq`, ✅), ct₁, ct₂ are τ-related.
   Hypothesis preservation:
   - `IsPrefixTyping ct_i`: by `convergeLoop_preserves_prefix` (✅, in `Invariants.lean`,
     now public via the recent surgery).
   - `UniquelyHeldBelow ct_i s`: by `convergeLoop_preserves_lower_uniqueness` (✅, made
     public this session).
   - `ct_i.size = n`: by `convergeLoop_size_preserving` (✅).

2. **breakTie step.** `(arr_i', changed_i) := breakTie ct_i s`.
   Hypothesis preservation:
   - `IsPrefixTyping arr_i'` AND `UniquelyHeldBelow arr_i' (s+1)`: by
     `breakTie_step_preserves_uniqueness` (✅, made public this session).
   - `arr_i'.size = n`: via `breakTie_size`.

3. **Tiebreak choice handling.** Two sub-cases on the pair `(keep₁, keep₂)`:
   - **Case A** (keep₂ = τ keep₁): arr₁' and arr₂' are directly τ-related via
     `breakTieAt_τ_related` (✅, Phase 4) applied with the converged ct_i. Apply
     **IH-P₁** at level k to (arr₁', arr₂') — giving `runFrom (s+1) arr₁' G = runFrom (s+1) arr₂' G`.
   - **Case B** (keep₂ ≠ τ keep₁): both keep_i ∈ typeClass ct_i s (the targeted class),
     and they're in the same `TypedAut`-orbit (since τ ct₁'s typeClass equals ct₂'s
     typeClass). Use **IH-P₂** at level k to get
     `runFrom (s+1) (breakTieAt ct₂ s keep₂) G = runFrom (s+1) (breakTieAt ct₂ s (τ keep₁)) G`.
     Then `breakTieAt ct₂ s (τ keep₁)` is τ-related to `breakTieAt ct₁ s keep₁` by
     `breakTieAt_τ_related` (✅), and we apply **IH-P₁** to get equality with
     `runFrom (s+1) arr₁' G`.

4. Combining 3.A or 3.B chains the runFroms, giving `runFrom s arr₁ G = runFrom s arr₂ G`. ∎

**Key lemma names**:
  - `convergeLoop_VtsInvariant_eq` (✅ Phase 2)
  - `convergeLoop_preserves_prefix` (✅ in Invariants)
  - `convergeLoop_preserves_lower_uniqueness` (✅ now public)
  - `breakTie_step_preserves_uniqueness` (✅ now public)
  - `breakTieAt_τ_related` (✅ Phase 4)
  - `IsPrefixTyping_τ_transfer` (✅ this session)
  - `UniquelyHeldBelow_τ_transfer` (✅ this session)
  - `labelEdges_VtsInvariant_eq_distinct` (Phase 3.E pending)

**`tiebreak_choice_independent_strong`**: a strengthened version of the existing
`tiebreak_choice_independent` (in `Tiebreak.lean`), with the added prefix/uniqueness
hypotheses. Its proof reduces to `runFrom_VtsInvariant_eq_strong` at level k+1,
hence the joint induction.

**Risk: high.** Intricate joint induction; care needed in stating the IH and the
case analysis. Mitigation: state the joint statement with explicit `s` and prove
P₁ ↔ P₂ once at fixed level, then induct.

### Phase 6 — `run_isomorphic_eq_new` (~250-400 lines, including the generalized stages)

**File**: `Main.lean`. Preliminaries in `Equivariance/MainRelationalNotes.lean`
(already documents the plan).

**Statement** (in file): `G ≃ H → run zeros G = run zeros H`.

**Strategy**: by §2 obtain σ : Equiv.Perm (Fin n) with H = G.permute σ. The σ may not
be in Aut G (in general). Need to thread σ through the entire pre-labelEdges pipeline,
using that σ acts consistently on (state, vts) and on the graph G ↦ G.permute σ.

#### Required generalizations beyond Phases 1-5:

  - **Stage A (general σ)**: `initializePaths_Aut_equivariant` already holds for any σ
    (the proof in `Equivariance.StageA` doesn't use σ ∈ Aut G — only the algebraic
    structure of `Equiv.Perm`). Re-export or rename: ✅ effectively available, just
    need to confirm it's not unnecessarily restricted.

  - **Stage B-rel (general σ)**: Phase 1's `calculatePathRankings_σ_equivariant_relational`
    relies on `PathState.permute σ (initializePaths G) = initializePaths G` (true only
    for σ ∈ Aut G). For general σ, the LHS is `initializePaths (G.permute σ)` (by
    Stage A). New form needed:
    ```
    calculatePathRankings (initializePaths (G.permute σ)) (σ · vts)
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts)
    ```
    The body-step proof needs to NOT assume σ-fixedness of state. Instead, track σ
    on both state and vts simultaneously. Estimate: ~150-200 lines following the
    existing Stage B-rel structure but with a different invariant.

  - **Stage C-rel (general σ)**: direct corollary of generalized Stage B-rel.
    Estimate: ~30-50 lines.

  - **Stage D under "external σ" (i.e., G vs G.permute σ)**: use
    `labelEdges_VtsInvariant_eq_distinct` extended to `(rks_τ, G.permute σ)` →
    `(rks, G)`. Same cell-wise characterization (Phase 3 terminal rankMap identity
    + fold strong) applies — just specialize differently. Estimate: ~50 lines.

#### Phase 6 proper — assembly:

Given G ≃ H, σ with H = G.permute σ, zeros : Array VertexType:

1. `getArrayRank zeros = zeros` (since all values are 0; values stay 0; getArrayRank
   maps to dense ranks all zero too).

2. `initializePaths H = (initializePaths G).permute σ` (Stage A general).

3. `convergeLoop (initializePaths H) zeros n
      = (convergeLoop (initializePaths G) zeros n) shifted by σ`
   (Stage C general; uses zeros being trivially σ-invariant).

4. After the full breakTie loop in `runFrom 0 ... H`, the orderedRanks for H is the
   σ-shift of orderedRanks for G — modulo tiebreak choices, absorbed via Phase 5
   (the tiebreak-choice-independence built up in `runFrom_VtsInvariant_eq_strong`).

5. `labelEdges (orderedRanks_H) H = labelEdges (orderedRanks_G shifted by σ) (G.permute σ)
      = labelEdges orderedRanks_G G` (Stage D extended, with the tie-freeness from
   `orderVertices_n_distinct_ranks`).

6. Hence `run zeros H = run zeros G`. ∎

**Key lemma names beyond Phase 5**:
  - Generalized `calculatePathRankings_σ_equivariant_relational_general`: pending.
  - `convergeLoop_σ_equivariant_general`: corollary, pending.
  - `labelEdges_external_σ_eq`: extension of Phase 3.E for σ ∉ Aut G case. Pending.
  - `zeros_σ_invariant` (in `MainRelationalNotes.lean`, ✅).
  - `getArrayRank_zeros_eq_zeros`: needed; quick.

**Risk: medium-high.** Substantial work in generalizing Stage B-rel; the rest is
assembly given the generalizations.

### Total remaining-work estimate

| Sub-phase     | Description                                            | Risk        | New lines |
|---------------|--------------------------------------------------------|-------------|-----------|
| Phase 3.C     | `computeDenseRanks_τ_shift_distinct`                   | medium      | ~120-150  |
| Phase 3.D     | `computeDenseRanks_perm_when_tieFree`                  | medium-low  | ~70-100   |
| Phase 3.E     | `labelEdges_VtsInvariant_eq_distinct` assembly         | low         | ~80-120   |
| Phase 5       | `runFrom_VtsInvariant_eq_strong` joint induction       | high        | ~250-300  |
| Phase 6       | `run_isomorphic_eq_new` + generalized Stage B/C        | medium-high | ~350-500  |

**Total**: ~870–1170 lines of new Lean. Recommended order: Phase 3.D → Phase 3.C
→ Phase 3.E → Phase 5 → Phase 6. (Phase 3.D and Phase 3.C are independent; doing
Phase 3.D first is safer because it's the simpler structural fact about `computeDenseRanks`.)

### Risk-mitigation pivots

  - **3.C alternative (Route A vs B)**: if Route A's `Finset`-counting becomes hard,
    fall back to Route B's parallel-fold approach (more verbose but safer).
  - **5 fallback**: if the joint induction proves too intricate, separately strengthen
    `tiebreak_choice_independent` to take the prefix invariant, then prove
    `runFrom_VtsInvariant_eq_strong` using IT and Phase 3.E directly without the
    joint structure. Cost: ~50 extra lines of preconditions.
  - **6 simplification**: if generalizing Stage B-rel proves too costly, take a
    case-split on `σ ∈ Aut G`. The σ ∈ Aut G case reduces to existing Phase 1-5;
    the σ ∉ Aut G case can be handled via `Isomorphic.swap_induction_on`
    (in `Isomorphic.lean`) decomposing σ into transpositions, threading
    `swapVertexLabels_eq_permute` repeatedly. Cost: ~200 extra lines but avoids
    the deep generalization.

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

**Status: proved** in `Isomorphic.lean`.

```
permute_of_Isomorphic        : G ≃ H → ∃ σ, H = G.permute σ
Isomorphic_of_permute        : H = G.permute σ → G ≃ H
Isomorphic_iff_exists_permute: G ≃ H ↔ ∃ σ, H = G.permute σ
```

(⟹) is induction on the `Isomorphic` constructors using `permute_one`,
`swapVertexLabels_eq_permute`, and `permute_mul` (composition order σ₂ * σ₁ in the
`trans` case is forced by the left-action law). (⟸) is `Equiv.Perm.swap_induction_on`
followed by `permute_mul` + `swapVertexLabels_eq_permute` to fold each transposition
back into an `Isomorphic.swap`.

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

**Strict shrinking.** If some τ ∈ Aut(G, T) moves v* (the `hmove` hypothesis below), then
that τ is in `TypedAut G T` but not in the v*-stabilizer, so the stabilizer is a proper
subgroup. After each tiebreak, the typed-automorphism group strictly shrinks; after at
most n tiebreaks it is trivial (all types distinct).

**Deliverable.** Both theorems are proved in `FullCorrectness/Tiebreak.lean`:
```
breakTie_Aut_stabilizer  : [with hsize + hAutInv]
    σ ∈ TypedAut G (breakTie vts t₀).1  ↔  (σ ∈ TypedAut G vts ∧ σ v* = v*)
breakTie_TypedAut_le     : TypedAut G (breakTie vts t₀).1 ≤ TypedAut G vts
breakTie_strict_shrink   : [with hmove] TypedAut G (breakTie vts t₀).1 < TypedAut G vts
```

Four position-by-position characterization lemmas underpin the proofs:
```
breakTie_size             : (breakTie vts t₀).1.size = vts.size
breakTie_getD_below       : vts[j] < t₀ → (breakTie vts t₀).1[j] = vts[j]
breakTie_getD_above       : vts[j] > t₀ → (breakTie vts t₀).1[j] = vts[j] + 1   -- when fired
breakTie_getD_at_min      : v_star is min of typeClass → (breakTie vts t₀).1[v_star] = t₀
breakTie_getD_at_other    : w ≠ v_star in typeClass → (breakTie vts t₀).1[w] = t₀ + 1
```
The split into `_below` / `_above` (rather than a single `_of_ne`) reflects the
shift-then-promote design forced by dense ranks (see the `breakTie` docstring in
[LeanGraphCanonizerV4.lean](LeanGraphCanonizerV4.lean)).

Two reusable corollaries support §7's `breakTie_targetPos_is_min_tied`:
```
breakTie_getD_target     : vts[w] = t₀ → output[w] = t₀ ∨ output[w] = t₀ + 1
breakTie_getD_target_ge  : vts[w] = t₀ → t₀ ≤ output[w]
```
Both pick `v_star` as the smallest target-valued index (`Nat.find`) and apply
`breakTie_getD_at_min` / `breakTie_getD_at_other`.

### Hypotheses beyond the original sketch

  1. **§5.1 carries `hsize : vts.size = n` and `hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts`.**
     The Aut-invariance is genuinely necessary: without it, a label swap between a
     non-`v*` member of `typeClass t₀` and some position carrying value `t₀ + 1` can
     preserve `vts'` (both get value `t₀+1`) without preserving `vts`. Aut-invariance
     rules out this counterexample, and is satisfied at every `breakTie` call by §4's
     corollary.

  2. **§5.2 carries `hmove : ∃ σ ∈ G.TypedAut vts, σ v_star ≠ v_star`.**
     The plan's sketch derived strict shrinking from "same-type vertices lie in a single
     Aut-orbit" (§4's corollary), but §4 only gives the forward direction (same-orbit →
     same-type). The reverse is essentially the algorithm's completeness and is captured
     here as the minimal needed input.

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

### Reduction to a single pipeline-equivariance lemma

`tiebreak_choice_independent` carries two extra hypotheses beyond the plan sketch:
  - `hsize : vts.size = n` — trivially satisfied by the algorithm.
  - `hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂` — orbit connectivity. Same "same-type ⟹
    same-orbit" requirement that §5.2 needed, surfaced explicitly because §4 only gives
    the forward direction.

With those hypotheses, §6 reduces to the *pipeline equivariance* statement:

```
runFrom_VtsInvariant_eq :
  τ ∈ G.Aut → (∀ w, arr₂[w] = arr₁[τ⁻¹ w]) → runFrom s arr₁ G = runFrom s arr₂ G
```

which is §3 (Stages B–D) chained. **`tiebreak_choice_independent` type-checks** by
discharging via `runFrom_VtsInvariant_eq` applied to the τ-related pair `breakTieAt vts t₀
v₁`, `breakTieAt vts t₀ v₂` (related by the τ from `hconn`). The single open obligation in
this whole chain is `runFrom_VtsInvariant_eq` itself.

Supporting deliverables in `Tiebreak.lean`:
```
breakTieAt_size             : (breakTieAt vts t₀ keep).size = vts.size
breakTieAt_getD_of_ne       : vts[j] ≠ t₀ → (breakTieAt vts t₀ keep)[j] = vts[j]
breakTieAt_getD_keep        : (breakTieAt vts t₀ keep)[keep] = vts[keep]
breakTieAt_getD_promoted    : w ≠ keep ∧ vts[w] = t₀ → (breakTieAt vts t₀ keep)[w] = t₀ + 1
breakTieAt_VtsInvariant_eq  : [τ-equivariance under VtsInvariant τ vts]
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
the dense-rank pipeline keeps values exactly 0..m-1). Each `breakTie` with target p leaves
values 0..p-1 unchanged and promotes some value-p vertices to p+1, which the next
`convergeLoop` re-densifies.

**Deliverables in `FullCorrectness/Invariants.lean`:**
```
convergeLoop_preserves_prefix              : ✅ proved (specialized to `state := initializePaths G`;
                                              the general form is literally false — see file header)
getFrom_image_isPrefix_for_initializePaths : ✅ proved (deep core: `n = 0` boundary + `n ≥ 1` via
                                              outer/inner fold helpers + dense-rank density)
breakTie_targetPos_is_min_tied             : ✅ proved
orderVertices_prefix_invariant             : 🟡 closed conditional on §7-Step 3 sub-lemma
                                              `convergeLoop_preserves_lower_uniqueness`. Outer
                                              induction skeleton (`_strong` form) and §7-Step 2
                                              (breakTie step) ✅ proved.
orderVertices_n_distinct_ranks             : ✅ proved (corollary of `_prefix_invariant` at `p = n`
                                              via pigeonhole + `Finite.injective_iff_bijective`,
                                              now requires a `vts.size = n` hypothesis to thread
                                              through the strengthened invariant)
```

The `orderVertices_prefix_invariant` proof factors into three §7-internal steps
(named "§7-Step X" to avoid collision with the top-level relational "Phase X"):

- **§7-Step 1 — inductive skeleton** (✅): Strengthened invariant (`_strong` form) tracks
  both the prefix-typing property and the uniqueness `0..q-1`. Induction on `q` from `0`
  to `p`. The base case is vacuous. The step uses §7-Step 3 (convergeLoop preservation)
  followed by §7-Step 2 (breakTie step).

- **§7-Step 2 — breakTie step** (✅ as `breakTie_step_preserves_uniqueness`): For `T`
  prefix with `0..q-1` uniquely held and `q < n`, `(breakTie T q).1` is prefix and has
  `0..q` uniquely held. Cases on `breakTieCount T q < 2` (noop) or `≥ 2` (fires).
  Uses `breakTie_getD_below`, `breakTie_getD_at_min`, `breakTie_getD_at_other`,
  `breakTie_getD_above_or`, plus a converse to `breakTieCount_ge_two_of_distinct`
  (`exists_two_distinct_q_in_T`, derived from `List.Duplicate` + `List.Sublist`).

- **§7-Step 3 — convergeLoop preservation** (✅, closed via the sub-sub-lemmas below):
  For `T` prefix with `0..q-1` uniquely held by `v_0..v_{q-1}` (with `T[v_k] = k`),
  `convergeLoop _ T fuel` has the same property. The proof uses three weaker facts about
  `T' = convergeOnce T`: (a) `T'[v_k] < q` for unique-typed `v_k`, (b) `T'[w] ≥ q` for
  non-unique-typed `w`, (c) `k ↦ T'[v_k]` is injective. Then `{T'[v_k] | k < q} = {0..q-1}`
  and the public `∃!` follows.

  Sub-sub-lemmas (named `Step3.X` — local to §7-Step 3):
  - **Step3.1** ✅ `comparePathsFrom_eq_compare_of_start_types_ne` (different start types ⟹
    `comparePathsFrom` returns the comparison directly).
  - **Step3.B** ✅ `assignRanks_rank_le_pos` (rank at position `k` is `≤ k`). Foundational.
    Uses aux lemmas `assignRanksFoldl_lastEntry_rank_le` (lastEntry rank tracks step count)
    and `assignRanks_snoc_decompose` (snoc-decomposition with rank bound).
  - **Step3.C** ✅ `assignRanks_rank_eq_pos_when_distinct` (rank `=` position when
    consecutive cmps differ). Built on `assignRanks_strong_invariant` which simultaneously
    tracks (i) rank-at-every-position and (ii) lastEntry-rank, via `reverseRecOn`
    induction. Uses `assignRanks_snoc_decompose_strict` (sharper snoc-decomposition with
    exact rank formula) and `assignRanks_foldl_lastEntry_fst` (lastEntry's first
    component).
  - **Step3.D** ✅ `sortBy_first_q_positions_have_start_types`.
    For `T` uniquely-typed at `0..q-1`, the first `q` positions of
    `sortBy comparePathsFrom T pathsAtTop` have start types `0, 1, …, q-1` in order.
    Strategy: strong induction on position `k`, with two sub-arguments:
    (A) `V_k ≥ k` — uses uniqueness + nodup of starts in sortedList: any value `j < k`
    that V_k could take would force its start to coincide with the unique witness at
    position `j` (where `V_j = j` by IH), contradicting nodup.
    (B) `V_k ≤ k` — find the unique witness `w_k` for value `k`; locate its position
    `pos` in sortedList; trichotomy on `pos` vs `k` gives a contradiction in each case
    (`pos < k` contradicts IH, `pos = k` gives `V_k = k`, `pos > k` violates Pairwise
    via Step3.1 since `V_k > k = V_pos` would force `cmp = .gt`).
    Foundation work:
    - **`comparePathsFrom_total_preorder`** ✅ proved (by lifting from
      `comparePathsBetween_total_preorder` + the now-public `orderInsensitiveListCmp_*`
      helpers).
    - Made public: `orderInsensitiveListCmp_refl`, `orderInsensitiveListCmp_swap_lt`,
      `orderInsensitiveListCmp_swap_gt`, `orderInsensitiveListCmp_trans` in
      `ComparePathSegments.lean`; `sortBy_pairwise` in `ComparisonSort.lean`.
  - **Step3.E** ✅ `convergeOnce_preserves_lower_uniqueness` fully closed.
    Prefix + size conjuncts via `convergeOnce_writeback` +
    `getFrom_image_isPrefix_for_initializePaths`. Uniqueness conjunct via the (a)/(b)/(c)
    pattern: per-vertex chain identification + Step3.D + Step3.C-prefix + monotonicity +
    boundary-distinctness extension. Helpers added:
    - `assignRanks_rank_eq_of_prefix` (rank at k in `assignRanks (A ++ B)` equals rank
      at k in `assignRanks A` for k < A.length).
    - `assignRanks_rank_eq_pos_when_distinct_prefix` (Step3.C-prefix: rank = position for
      positions < q when only the prefix has distinct cmps).
    - `assignRanks_pairwise_rank_le` + `assignRanks_rank_monotone` (rank values
      non-decreasing along assignList; via the foldl invariant
      `revList head = lastEntry, head ≥ tail`).
    - `chain_value_at_vertex_for_assignRanks_sortBy` (per-vertex chain-rank lookup
      via `array_set_chain_at_target_nodup`).
    - **Aux** `fromRanks_at_n_minus_1_eq_chain_for_initializePaths` ✅ proved.
      Mirrors `getFrom_image_isPrefix_for_initializePaths`'s outer/inner-fold unwinding;
      witness `br` is the iteration's let-bound `updatedBetweenFn`, and after unwinding
      both sides become the same chain syntactically (closed by `rfl`).
  - **Step3.5** ✅ `convergeLoop_preserves_lower_uniqueness`: closed via fuel induction
    using Step3.E.

Closing `getFrom_image_isPrefix_for_initializePaths` (n ≥ 1) used these helpers:
- `inner_fold_slice_at_depth` (in `Equivariance.RankStateInvariants`) — strips the outer
  `fromAcc.set! depth` wrapper of the inner fold, reducing to a chain of `set!`s on the
  depth slice.
- `outer_fold_fromAcc_other_target_unchanged` (in `Invariants.lean`) — characterizes the
  outer depth loop: the `fromRanks` slot at any `target` is preserved as long as `target`
  is not in the list of remaining depths to process.
- `array_set_chain_outside_unchanged` / `array_set_chain_at_target_nodup` (in
  `Equivariance.RankStateInvariants`) — read out a `set!` chain at any target index when
  the chain's indices are `Nodup`. (Moved from `Invariants.lean` to share with
  `PathEquivariance.lean`'s σ-invariance proofs.)
- `initializePaths_pathsAtDepth_startVertices_eq_range` (in `Invariants.lean`) — for
  `state := initializePaths G`, the depth-`d` slice's `pathsFrom.startVertexIndex.val` list
  equals exactly `List.range n`.
- `chain_image_dense_of_perm_and_density` — generic image-density lemma: if the chain's
  indices are a permutation of `0..n-1` and the rank set is downward-closed, the image
  over `Fin n` is exactly `{0, …, m-1}` for some `m`.
- `chain_image_dense_for_assignRanks_sortBy` — wrapper specializing to the `assignRanks ⊕
  sortBy` form, deriving the perm/density conditions from `assignRanks_map_fst`,
  `sortBy_perm`, `assignRanks_image_dense`, and the start-vertex-list equality above.

`breakTie_targetPos_is_min_tied` proof sketch: assume by contradiction two distinct
vertices `w₁ ≠ w₂` share an output value `val ≤ p`. By `breakTie_getD_target`, target-valued
positions land on `{p, p+1}`; since `p+1 > p`, an output `≤ p` rules out promotion, so
`output[w_i] = vts[w_i]` (preserved). Two sub-cases on `val`:
- `val < p`: by the prefix-uniqueness hypothesis at `k := val`, `w₁ = w₂`. ⊥.
- `val = p`: only the smallest target-valued index keeps value `p` (others are promoted by
  `breakTie_getD_at_other`), so both `w_i` equal that index. ⊥.

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
subgroup of `Sym(Fin n)` which is finite). **Resolved:** `Fintype` instances on `Aut` and
`TypedAut` are in `Automorphism.lean` and `Tiebreak.lean`.

**R2.** §7's prefix-of-ℕ invariant assumes dense ranking throughout. **Resolved by the
sparse → dense ranking migration** (now landed in `LeanGraphCanonizerV4.lean`):
`assignRanks` produces dense ranks, `getArrayRank` densifies at the entry point, and
`breakTie` uses shift-then-promote (`shiftAbove` + `breakTiePromote`) to preserve density
across iterations. Re-verify `countUniqueCanonicals 4 == 11` and the literal-string
`#guard`s in `LeanGraphCanonizerV4Tests.lean` if the algorithm is touched again.

**R3.** `convergeLoop` is given fuel equal to `state.vertexCount`. Correctness does not
require it to actually reach a fixed point — §4 says the output is always Aut-invariant,
fixed point or not — but we should double-check that "output is Aut-invariant at every
iteration" is what induction gives us, not the weaker "fixed point is Aut-invariant."

**R4.** `Fin`/`Nat` bounds on `set!`, `getD`, and the array-index arithmetic throughout
will produce side conditions. Collect into a single `def` + lemmas file if they multiply.

## Suggested development order

Serial dependencies run §1 → §2 → §3 → §4 → (§5 ∥ §7) → §6 → §8. The independent
work (Mathlib-facing infrastructure: §1 done; §2 done) can proceed in parallel with
algorithm-facing work (§3–§5 are about the specific data structures of this canonizer).

§6 is the single hardest step and should be the budgeting focus once §3–§5 are in place.
-/
