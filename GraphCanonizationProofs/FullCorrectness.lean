/-!
# Full correctness of the graph canonizer — proof plan (docs only)

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
| §6   | Tiebreak choice-independence (conceptual crux)    | `Equivariance.RunFromRelational`         | ✅ closed (modulo `OrbitCompleteAfterConv` hypothesis discharged by Phase 6) |
| §7   | `IsPrefixTyping` definition + zeros instance      | `Invariants`                             | ✅ defined + boundary proved |
| §7   | `breakTie_targetPos_is_min_tied`                  | `Invariants`                             | ✅ proved (uses §5 disjunctive characterization) |
| §7   | Other prefix invariants                           | `Invariants`                             | ✅ all proved (`getFrom_image_isPrefix_for_initializePaths`, `convergeLoop_preserves_prefix`, `n_distinct_ranks`, `orderVertices_prefix_invariant`, §7-Step 2 breakTie step, §7-Step 3 convergeLoop_preserves_lower_uniqueness) |
| §8   | Assemble `run_canonical_correctness`              | `Main`                                   | 🧱 assembled, (⟹) `sorry`; (⟸) proved |

## Open obligations (1 sorry site)

| Sorry | Location | What's needed |
| ----- | -------- | ------------- |
| `run_swap_invariant_fwd` (σ ∉ Aut G branch) | `Main` | Pipeline σ-equivariance for general σ — specifically `orderVertices ((init G).permute σ) zeros = σ-shift of orderVertices (init G) zeros`. Reduces to Stage B-rel general σ + Stage C-rel general σ + breakTie σ-tracking through outer iterations. **Stage D-rel general σ is now closed** (`labelEdges_two_graphs_σ_related` in `StageDRelational.lean`), so once orderVertices σ-equivariance is closed, the swap case follows immediately. |

The top-level theorem `run_isomorphic_eq_new` is now structured via induction on
`Isomorphic`'s constructors: `refl` and `trans` cases close trivially, the `swap` case
delegates to `run_swap_invariant_fwd`. The σ ∈ Aut G branch is fully closed; the σ ∉ Aut G
branch is reduced to a single technical claim (orderVertices σ-equivariance under general σ).

**New in this round:** `labelEdges_two_graphs_σ_related` in `StageDRelational.lean` — Stage
D-rel for **two different graphs** related by σ (not requiring σ ∈ Aut G). Mirrors
Phase 3.E (`labelEdges_VtsInvariant_eq_distinct`) but starts the labelEdges fold on
`G.permute σ` (rather than `G`) for the second side.

**Closed in this round:**
  - `runFrom_VtsInvariant_eq_strong` (Phase 5, in `Equivariance/RunFromRelational.lean`):
    closed modulo the `OrbitCompleteAfterConv` hypothesis input.
  - `runFrom_VtsInvariant_eq` (formerly `Tiebreak.lean` sorry): now a wrapper around the
    strong theorem, in `Equivariance/RunFromRelational.lean`.
  - `tiebreak_choice_independent` (formerly modulo §3 sorry in `Tiebreak.lean`): now
    proved as a wrapper around `runFrom_VtsInvariant_eq` + `breakTieAt_VtsInvariant_eq`,
    in `Equivariance/RunFromRelational.lean`.

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
| 5     | `runFrom_VtsInvariant_eq_strong`                     | ✅ closed modulo `OrbitCompleteAfterConv` orbit hypothesis (canonizer-correctness invariant, discharged at Phase 6's call site) |
| 6     | `run_isomorphic_eq_new`                              | 🟦 documented; needs generalized stages + `OrbitCompleteAfterConv` discharge |

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
(Phase 5 inductive step Case 2; Phase 6).

**Dependency graph**:

```
Main.run_isomorphic_eq_new                       (Phase 6, pending)
  ↓ uses
runFrom_VtsInvariant_eq_strong                   (Phase 5, ✅ closed modulo OrbitCompleteAfterConv)
  ↓ uses
labelEdges_VtsInvariant_eq_distinct              (Phase 3.E, ✅ closed)
  ↓ uses
computeDenseRanks_τ_shift_distinct               (Phase 3.C, ✅ closed) +
computeDenseRanks_perm_when_tieFree              (Phase 3.D, ✅ closed) +
[labelEdges_fold_strong + labelEdges_terminal_rankMap_identity]  (Phase 3.B, ✅ closed)
```

All of Phase 3 is closed and Phase 5's strong theorem is closed modulo a single
canonizer-correctness hypothesis (`OrbitCompleteAfterConv`). The remaining gap is
Phase 6's σ-generalized stages plus discharging the orbit hypothesis there.

### Phase 3.C, 3.D, 3.E — closed

All proofs in `Equivariance/StageDRelational.lean`. Highlights:
  - 3.C uses the relational `sortBy` machinery (`sortBy_map_pointwise_relational`) plus a
    new `sortBy_eq_of_perm_strict` helper (now in `ComparisonSort.lean`) and a `pairCmp`
    strict-lex characterization (`pairCmp_le_iff`, `pairCmp_gt_iff`).
  - 3.D uses `array_set_chain_at_target_nodup` plus a `sortedPairs_seconds_perm` lemma.
  - 3.E uses `labelEdges_fold_strong` + `labelEdges_terminal_rankMap_identity` (Phase 3.B
    foundations) + a `computeDenseRanks_inj` lemma (proved structurally without tie-freeness).

### Phase 5 — `runFrom_VtsInvariant_eq_strong` (closed modulo orbit hypothesis)

**File**: `Equivariance/RunFromRelational.lean`.

**Statement**: `runFrom_VtsInvariant_eq_strong` with hypotheses
`(τ ∈ Aut G) ∧ (τ-related arr₁, arr₂) ∧ (IsPrefixTyping arr₁) ∧ (UniquelyHeldBelow arr₁ s) ∧
(s ≤ n) ∧ (OrbitCompleteAfterConv G)` — the last hypothesis is the canonizer-correctness
orbit invariant taken as input (discharged at the Phase 6 call site).

**Strategy**: induction on `m := n - s`, generalizing over `s` and over `τ` (since Case 2
applies the IH with a different τ' := σ * τ where σ is the orbit-bridging element).

**Proof structure** (all closed):
  - `runFrom_at_n`: `runFrom n arr G = labelEdgesAccordingToRankings arr G` (empty foldl).
  - `runFrom_succ`: `runFrom s arr G = runFrom (s+1) ((breakTie (convergeLoop _ arr n) s).1) G`.
  - `UniquelyHeldBelow_n_implies_TieFree`: pigeonhole via `Finite.injective_iff_surjective`.
  - `breakTieCount_τ_invariant`: closed via `breakTieCount_eq_countP` +
    `Equiv.Perm.map_finRange_perm` + `List.Perm.countP_eq` (List.Perm machinery — no
    Finset.card detour needed).
  - `typeClass_τ_image_eq`: τ⋅(typeClass arr₁ t) = typeClass arr₂ t for τ-related arrays.
  - `breakTie_min_witness`: when `breakTieCount arr t ≥ 2`, the smallest-index
    target-valued vertex exists as a `Fin n` (via `Nat.find`).
  - **Base case** (s = n): closed via Phase 3.E + `UniquelyHeldBelow_τ_transfer`.
  - **Case 1** (no fire, `breakTieCount conv₁ s < 2`): `arr_i' = conv_i` (via
    `breakTie_noop`); they are τ-related via Phase 2; IH at s+1 with the same τ.
  - **Case 2** (fire, `breakTieCount conv₁ s ≥ 2`):
    1. Extract `v₁ := min(typeClass conv₁ s)` and `v₂ := min(typeClass conv₂ s)` via
       `breakTie_min_witness`.
    2. Show `τ v₁ ∈ typeClass conv₂ s` via `typeClass_τ_image_eq`.
    3. Apply `OrbitCompleteAfterConv` to get `σ ∈ G.TypedAut conv₂` with `σ (τ v₁) = v₂`.
    4. Define `στ := σ * τ ∈ Aut G`; check pointwise via `breakTie_getD_below /
       _at_min / _at_other / _above` characterizations that `arr₁'` and `arr₂'` are
       `στ`-related (case split on `conv₂[w]` vs `s`).
    5. Apply IH at s+1 with τ' := στ.

**Discharged at the call site (Phase 6 / Main.lean)**:
  - `OrbitCompleteAfterConv G`: ∀ post-iters mid, vertices in convergeLoop(mid)
    sharing a value lie in the same `TypedAut(convergeLoop(mid))`-orbit. This is
    the canonizer-correctness invariant; for Phase 6's `run zeros G = run zeros H`
    proof under `H = G.permute σ`, the σ ∈ Aut G structure supplies the orbit bridge.

**Key lemmas used**:
  - `convergeLoop_VtsInvariant_eq` (Phase 2), `convergeLoop_preserves_prefix`,
    `convergeLoop_preserves_lower_uniqueness`, `breakTie_step_preserves_uniqueness`,
    `breakTie_noop`, `breakTie_getD_below/_above/_at_min/_at_other`,
    `IsPrefixTyping_τ_transfer`, `UniquelyHeldBelow_τ_transfer`,
    `labelEdges_VtsInvariant_eq_distinct` (Phase 3.E).

### Phase 6 — `run_isomorphic_eq_new` (~300-500 lines)

**File**: `Main.lean`. Preliminaries in `Equivariance/MainRelationalNotes.lean`
(already documents the plan).

**Statement** (in file): `G ≃ H → run zeros G = run zeros H`, where
`zeros := Array.replicate n 0`.

**Strategy**: by §2 obtain σ : `Equiv.Perm (Fin n)` with `H = G.permute σ`. The σ may
NOT be in `Aut G` in general — that's exactly what makes graphs isomorphic vs equal. So
we must thread σ through the entire pre-labelEdges pipeline as an EXTERNAL relabeling
(graph changes; vts undergoes σ-relabel in lockstep).

#### Strategy split: symmetric vs general σ

Two viable paths:

**Path A (clean) — generalize the σ-relational stages from "σ ∈ Aut G" to "general σ".**

  - **Stage A general**: `initializePaths_general_σ`: `initializePaths (G.permute σ) = (initializePaths G).permute σ`.
    Likely already available — `initializePaths_Aut_equivariant` (in `Equivariance.StageA`)
    doesn't actually use σ ∈ Aut G; just rename/re-export.
  - **Stage B-rel general**: `calculatePathRankings_σ_equivariant_general`:
    ```
    calculatePathRankings (initializePaths (G.permute σ)) (σ · vts)
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts)
    ```
    Phase 1's `calculatePathRankings_σ_equivariant_relational` relies on
    `PathState.permute σ (initializePaths G) = initializePaths G` (which uses σ ∈ Aut G).
    Generalizing requires a fresh body-step proof tracking σ on BOTH state and vts. The
    `comparePathsFrom`/`comparePathsBetween`/`comparePathSegments` σ-equivariance lemmas
    (in `CompareEquivariant.lean`) already hold without σ ∈ Aut G — they're purely
    algebraic. The σ-cell-INV `comparePathsFrom_σ_self_eq` is the obstacle (uses σ-INV
    vts). Workaround: the relational forms `comparePathSegments_σ_relational` etc.
    (already proved) generalize directly. Estimate: **~150-200 lines** following
    `PathEquivarianceRelational.lean`'s pattern with a different invariant.
  - **Stage C-rel general**: direct corollary of generalized Stage B-rel + Phase 2's
    `convergeOnce_VtsInvariant_eq` structure. Estimate: ~30-50 lines.
  - **Stage D extended** (external σ): a variant of `labelEdges_VtsInvariant_eq_distinct`
    (Phase 3.E) with G vs G.permute σ as the graph and τ-related rks. Same cell-wise
    machinery (`labelEdges_fold_strong` + `labelEdges_terminal_rankMap_identity` + Phase
    3.D) applies. Estimate: ~50-80 lines.

**Path B (case-split fallback) — handle σ ∈ Aut G and σ ∉ Aut G separately.**

  - σ ∈ Aut G case: G = G.permute σ = H, so reduces to G = H (literally), trivial.
  - σ ∉ Aut G case: decompose σ into transpositions via `Equiv.Perm.swap_induction_on`
    and apply `swapVertexLabels_eq_permute` step-by-step. Each step is one `swap` /
    `swapVertexLabels`. Cost: ~200 extra lines for the swap induction; avoids the deep
    Stage B-rel generalization.

#### Phase 6 proper — assembly (assumes Path A's generalizations)

Given `G ≃ H`, get `σ : Equiv.Perm (Fin n)` with `H = G.permute σ` via
`permute_of_Isomorphic` (✅, §2). With `zeros := Array.replicate n 0`:

1. **getArrayRank invariance**: `getArrayRank zeros = zeros` (all values 0 → dense ranks
   all 0). Helper: `getArrayRank_zeros_eq_zeros` (🟦, ~15 lines, mechanical).

2. **σ-invariance of zeros**: `zeros_σ_invariant` (✅, in `MainRelationalNotes.lean`):
   trivially `zeros[σ v] = 0 = zeros[v]`. So `zeros` is σ-INV.

3. **Stage A applied**: `initializePaths H = (initializePaths G).permute σ`
   (`initializePaths_general_σ`, ~5 lines).

4. **convergeLoop on H = σ-shift of convergeLoop on G**:
   ```
   convergeLoop (initializePaths H) zeros n
     = some-σ-shift-of (convergeLoop (initializePaths G) zeros n)
   ```
   Apply `convergeLoop_σ_equivariant_general` (Path A; 🟦) using zeros σ-INV (step 2).

5. **The breakTie loop** in `runFrom 0 ... H` produces orderedRanks_H. By Phase 5's
   `runFrom_VtsInvariant_eq_strong` (currently partial), the tiebreak choices are
   absorbed: `runFrom 0 zeros' H = runFrom 0 (σ-shift zeros') G` for the σ-shifted
   typing, where the τ in `runFrom_VtsInvariant_eq_strong` is set to σ on the
   permuted graph. This requires σ ∈ Aut(G.permute σ) = Aut H, which is automatic
   via `Aut_isomorphism_transfer` (✅ likely available, or quick derivation).

6. **labelEdges on H = labelEdges on G** (Stage D extended; 🟦): with tie-free
   orderedRanks (from `orderVertices_n_distinct_ranks`, ✅, §7) and the σ-shift
   relating H to G, Phase 3.E's pattern + `labelEdges_external_σ_eq` (🟦)
   gives `labelEdges orderedRanks_H H = labelEdges orderedRanks_G G`.

7. Hence `run zeros H = run zeros G`. ∎

**Key lemma names**:
  - `permute_of_Isomorphic` (✅, §2)
  - `Isomorphic_iff_exists_permute` (✅, §2)
  - `initializePaths_Aut_equivariant` / `initializePaths_general_σ` (✅ likely, just
    re-export — verify the proof in `StageA.lean` doesn't unnecessarily require σ ∈ Aut G).
  - `zeros_σ_invariant` (✅, in `MainRelationalNotes.lean`)
  - `orderVertices_n_distinct_ranks` (✅, §7, in `Invariants.lean`)
  - `orderVertices_prefix_invariant` (✅, §7) — provides `IsPrefixTyping (orderVertices …)`.
  - `IsPrefixTyping.replicate_zero` / `zeros_IsPrefixTyping` (✅, in `Invariants.lean`,
    boundary instance for `zeros`).
  - `runFrom_VtsInvariant_eq_strong` (Phase 5, currently partial) — this is where the
    Phase 5 work plugs in.
  - `Aut_isomorphism_transfer` (🟦, may need writing — `σ ∈ Aut(G.permute σ)` automatic).
  - `getArrayRank_zeros_eq_zeros` (🟦, ~15 lines, quick).
  - `calculatePathRankings_σ_equivariant_general` (🟦, ~150-200 lines if Path A).
  - `convergeLoop_σ_equivariant_general` (🟦, ~30-50 lines, corollary of above).
  - `labelEdges_external_σ_eq` (🟦, ~50-80 lines, variant of Phase 3.E).

**Path A → Path B fallback**: if Path A's Stage B-rel generalization is too costly,
switch to Path B (swap induction). The Path B detour adds ~200 lines but reuses the
existing σ ∈ Aut G machinery for each transposition step.

**Risk: medium-high.** Substantial work in generalizing Stage B-rel (Path A) or
threading swap-induction (Path B). Phase 5's strong theorem is closed, so Phase 6 has
a clean entry point — the only Phase 5 burden it inherits is discharging the
`OrbitCompleteAfterConv` hypothesis.

### Total remaining-work estimate

| Sub-phase     | Description                                            | Risk        | Status      | New lines |
|---------------|--------------------------------------------------------|-------------|-------------|-----------|
| Phase 3.C     | `computeDenseRanks_τ_shift_distinct`                   | medium      | ✅ closed    | done      |
| Phase 3.D     | `computeDenseRanks_perm_when_tieFree`                  | medium-low  | ✅ closed    | done      |
| Phase 3.E     | `labelEdges_VtsInvariant_eq_distinct` assembly         | low         | ✅ closed    | done      |
| Phase 5       | `runFrom_VtsInvariant_eq_strong` (modulo `OrbitCompleteAfterConv`) | medium-high | ✅ closed | done |
| Phase 6       | `run_isomorphic_eq_new` + general σ stages + `OrbitCompleteAfterConv` discharge | medium-high | 🟦 pending  | ~350-550  |
| Tiebreak.lean | Replace `runFrom_VtsInvariant_eq` sorry with strong theorem call | low | 🟦 pending  | ~30       |

**Remaining**: ~380–580 lines of new Lean. Recommended order: Tiebreak fix-up → Phase 6.

### Risk-mitigation pivots

  - **OrbitCompleteAfterConv discharge** at Phase 6 call site: the canonizer-correctness
    invariant. When Phase 6's σ ∈ Aut G connects G and H = G.permute σ, an explicit σ
    bridges any required orbit pair. The hypothesis can be discharged by the σ-threading
    structure of Phase 6 itself — no separate canonizer-completeness proof required for
    the (⟹) direction.
  - **Phase 6 simplification**: if Path A (Stage B-rel general σ) proves too costly,
    take Path B (case-split on `σ ∈ Aut G`): trivial when σ ∈ Aut G; for σ ∉ Aut G use
    `Equiv.Perm.swap_induction_on` to decompose σ into transpositions, threading
    `swapVertexLabels_eq_permute` repeatedly. Cost: ~200 extra lines but avoids
    the deep σ-relational generalization.

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
