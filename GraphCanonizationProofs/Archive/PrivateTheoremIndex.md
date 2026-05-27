# Archived Private Theorem Index — GraphCanonizationProofs

Index of private Lean theorems, lemmas, and definitions in the archived (`Archive/...`) portion of the GraphCanonizationProofs project, grouped by source file path. Active counterparts live in `../PrivateTheoremIndex.md`.

## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line.
- **Description**: A short description of what the theorem proves.
- **Notes**: `@[simp]` / `@[ext]` attributes, `private`, instances, or other special properties.

## Archive/V4/FullCorrectness/Equivariance/StageA.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `permNat_inv_fin` | 42-48 | `permNat σ⁻¹ (Fin.val i) = (σ⁻¹ i).val`; Fin-level identity for local `initializePaths` slot rewrites. | private |
| `PathsBetween_initializePaths_eq` | 50-131 | For each depth-`d` slot `(s, e)`, the permuted-state's `PathsBetween` equals the σ-relabeled `PathsBetween` from the original state. | private |
| `PathsFrom_initializePaths_eq` | 133-202 | For each depth-`d` slot `s`, the permuted-state's `PathsFrom` equals the σ-relabeled `PathsFrom` from the original state. | private |

## Archive/V4/FullCorrectness/Equivariance/RankStateInvariants.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Array_set!_getD_self` | 90-94 | `(xs.set! i v).getD i d = v` when `i < xs.size`. | private |
| `Array_set!_getD_ne` | 96-100 | `(xs.set! i v).getD j d = xs.getD j d` when `i ≠ j`. | private |
| `Array_set!_eq_self_of_size_le` | 102-105 | `xs.set! i v = xs` when `xs.size ≤ i` (out-of-bounds write is identity). | private |
| `setBetween_size` | 107-111 | `setBetween` preserves the outer-array size. | private |
| `setBetween_getD_size` | 113-123 | `setBetween` preserves the size of every depth-row. | private |
| `from_set_getD_size` | 146-155 | Folding `set!` on `fromAcc` preserves the size of every depth-row. | private |

## Archive/V4/FullCorrectness/Equivariance/ComparisonSort.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `insertSorted_map` | 44-60 | `insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f` when `f` globally preserves `cmp`. | private; Global form; pointwise variant `insertSorted_map_pointwise` is strictly stronger |
| `sorted_perm_head_class_eq` | 96-129 | Head-element lemma used in `sortedPerm_class_eq`: the head of a sorted list and the head of any Perm share the same `cmp`-class. | private |
| `insertSorted_pairwise` | 334-386 | `insertSorted cmp a L` is `Pairwise (cmp · · ≠ .gt)` when `L` is, i.e. insertion preserves sortedness. | private |
| `assignRanksStep` | 520-530 | Single foldl step for `assignRanks`: appends `(elem, rank)` to accumulator. | private |
| `assignRanks_eq_foldl` | 532-533 | `assignRanks cmp L` equals a `List.foldl` of `assignRanksStep` starting from `([], 0)`. | private |
| `assignRanksStep_fst_length` | 535-540 | `assignRanksStep` preserves the length of the accumulated first-component list. | private |
| `assignRanksStep_fst_map_fst` | 542-548 | First components after `assignRanksStep` are the original list elements in order. | private |
| `assignRanks_aux_length` | 550-569 | Length of the `assignRanks` foldl accumulator at each step. | private |
| `assignRanks_aux_map_fst` | 577-594 | First-component map of the `assignRanks` foldl accumulator reproduces the prefix. | private |
| `assignRanksStep_commutes_relational` | 629-647 | Relational commutation: `assignRanksStep` with `cmp₂` on `f`-mapped input equals `assignRanksStep` with `cmp₁` on original when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b` in processed prefix. | private |
| `assignRanks_foldl_map_f_relational` | 649-688 | Foldl of `assignRanksStep` commutes with `f`-mapping in the relational form (pointwise hypothesis on already-seen prefix). | private |
| `assignRanksStep_rank_le` | 717-757 | The rank produced by `assignRanksStep` is `≤` the position index. | private |
| `assignRanks_aux_rank_le` | 759-782 | All ranks in the foldl accumulator are `≤` their position. | private |
| `assignRanksStep_density_invariant` | 790-858 | `assignRanksStep` preserves the density invariant: every rank below the current max has a witness. | private |
| `assignRanks_aux_density` | 860-898 | Density invariant holds for the full foldl accumulator. | private |
| `assignRanksFoldl_lastEntry_rank_le` | 943-1011 | The last entry's rank in the foldl accumulator is `≤` its list-end index. | private |
| `assignRanks_snoc_decompose` | 1013-1052 | Decompose `assignRanks cmp (L ++ [a])` into `assignRanks cmp L` plus one final entry. | private |
| `assignRanks_snoc_decompose_strict` | 1054-1072 | Strict variant: final rank is `assignRanks cmp L`.length when `cmp (last L) a ≠ .eq`. | private |
| `assignRanks_foldl_lastEntry_fst` | 1074-1096 | The first component of the foldl's last entry is the last element of the input list. | private |
| `assignRanksStep_preserves_invariant` | 1141-1185 | `assignRanksStep` preserves the combined (length, map_fst, rank_le) invariant used by `assignRanks_foldl_invariant`. | private |
| `assignRanks_foldl_invariant` | 1187-1205 | The combined invariant holds for the full foldl. | private |
| `assignRanks_strong_invariant` | 1229-1436 | Strong combined invariant for `assignRanks` used to prove `rank_eq_pos_when_distinct_prefix` and `rank_eq_within_eq_class`. | private |
| `sorted_eq_of_perm_strict_aux` | 1995-2047 | Auxiliary for `sortBy_eq_of_perm_strict`: equal sorted lists under strict `cmp`. | private |

## Archive/V4/FullCorrectness/Equivariance/LabelEdgesCharacterization.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `set!_getD_self_aux` | 110-114 | `(xs.set! i v).getD i d = v` when `i < xs.size`; local helper. | private |
| `set!_getD_ne_aux` | 116-120 | `(xs.set! i v).getD j d = xs.getD j d` when `i ≠ j`; local helper. | private |
| `rankMap_swap_step_eq` | 122-167 | The rankMap double-`set!` swap step is equivalent to composing one `Equiv.swap` into the indexing permutation. | private |
| `labelEdges_fold_terminal_aux` | 253-379 | Auxiliary: after processing a Nodup sublist of `finRange n`, the terminal rankMap satisfies `rankMap[v] = v`. | private |

## Archive/V4/FullCorrectness/Tiebreak.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `btStep` | 229-239 | Single fold step for `breakTiePromote`: promotes the minimum tied vertex. | private |
| `btStep_size` | 241-245 | `btStep` preserves array size. | private |
| `breakTiePromote_eq_fold` | 247-257 | `breakTiePromote t₀ vts` is expressed as a `List.foldl` of `btStep`. | private |
| `btFold_size` | 259-265 | The `btStep` foldl preserves array size. | private |
| `btStep_getD_ne` | 267-291 | `btStep` leaves positions with type `≠ t₀` unchanged. | private |
| `btFold_getD_ne` | 293-304 | The `btStep` foldl leaves positions with type `≠ t₀` unchanged. | private |
| `btFold_no_target` | 377-395 | If no position in the fold list has type `t₀`, the foldl is the identity. | private |
| `btStep_notfirst` | 397-405 | `btStep` is the identity when the current position is not the first promoted position. | private |
| `VertexType_add_one_ne` | 407-409 | `t₀ + 1 ≠ t₀` for any vertex type `t₀`. | private |
| `btFold_from_notfirst_getD` | 411-451 | Value formula for `btFold` starting from a position past the first promoted vertex. | private |
| `btFold_getD_not_mem` | 453-472 | The `btStep` foldl leaves positions outside its list unchanged. | private |
| `shiftAbove_getD_ne_target` | 596-602 | `shiftAbove` at a position whose type differs from `t₀`. | private |
| `bTAStep` | 1053-1056 | Single fold step for `breakTieAt`. | private |
| `breakTieAt_eq_fold` | 1058-1059 | `breakTieAt vts t₀ keep` is expressed as a `List.foldl` of `bTAStep`. | private |
| `bTAStep_size` | 1061-1065 | `bTAStep` preserves array size. | private |
| `bTAFold_size` | 1067-1072 | The `bTAStep` foldl preserves array size. | private |
| `bTAStep_getD_ne` | 1080-1088 | `bTAStep` leaves all positions other than `keep` unchanged. | private |
| `bTAFold_getD_of_notin` | 1090-1102 | `bTAFold` leaves positions not in its list unchanged. | private |
| `bTAFold_getD_of_ne` | 1104-1127 | `bTAFold` leaves positions `≠ keep` unchanged. | private |
| `bTAStep_preserves_keep` | 1136-1147 | `bTAStep` preserves the value at `keep`. | private |
| `bTAFold_preserves_keep` | 1149-1154 | The `bTAStep` foldl preserves the value at `keep`. | private |
| `bTAFold_getD_promoted` | 1162-1196 | Value at positions promoted by `bTAFold`. | private |

## Archive/V4/FullCorrectness/Equivariance/ComparePathSegments.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `cmpInner_eq_lt` | 25-40 | Evaluates the inner-inner `comparePathSegments` expression to `.lt` given `yR < xR ∨ (xR = yR ∧ ye < xe)`. | private |
| `cmpInner_eq_gt` | 42-53 | Evaluates the inner-inner `comparePathSegments` expression to `.gt` given `xR < yR ∨ (xR = yR ∧ xe < ye)`. | private |
| `cmpInner_eq_eq` | 55-59 | Evaluates the inner-inner `comparePathSegments` expression to `.eq` when `xR = yR` and `xe = ye`. | private |
| `cmpInner_trichotomy` | 61-73 | Exhaustive case split: for any `(xR, xe)` and `(yR, ye)`, exactly one of the `.gt`, `.eq`, or `.lt` conditions for the inner-inner comparator holds. | private |
| `orderInsensitiveListCmp_foldl_init_preserved` | 391-412 | Once the `orderInsensitiveListCmp` foldl accumulator is non-`.eq`, all subsequent steps short-circuit and the value is preserved unchanged. Used by `_swap_lt`, `_swap_gt`, `foldl_zip_trans`, and `foldl_zip_eq_implies_pairwise_eq` to discharge "init already set" cases. | private |
| `foldl_zip_trans` | 563-677 | For equal-length lists `A`, `B`, `C`: if `(zip A B).foldl ≠ .gt` and `(zip B C).foldl ≠ .gt`, then `(zip A C).foldl ≠ .gt`. Proved by induction on the head pair `(cmp a b, cmp b c)` using antisym₁ and bilateral compat. Core of `orderInsensitiveListCmp_trans`. | private |
| `foldl_zip_eq_implies_pairwise_eq` | 754-787 | If the `orderInsensitiveListCmp` foldl over a zipped list returns `.eq`, then every element pair in that list has `cmp = .eq` pointwise. | private |

## Archive/V4/FullCorrectness/Equivariance/CompareEquivariant.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `insertSorted_map_pointwise` | 56-71 | Pointwise variant of `insertSorted_map`: requires `cmp (f a) (f b) = cmp a b` only for `b ∈ L`. | private; Pointwise form of `insertSorted_map` |

## Archive/V4/FullCorrectness/Equivariance/PathsAtDepthStructure.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `initializePaths_pathsOfLength_get_eq` | 25-45 | Explicit constructor form of the depth-`d` slice of `initializePaths G`. | private |
| `initializePaths_pathsAtDepth_inner_structure` | 106-154 | Inner structural facts: `startVertexIndex` is constant within a `PathsFrom`, and `endVertexIndex.val`s enumerate `List.range n`. | private |

## Archive/V4/FullCorrectness/Equivariance/ChainSetInvariant.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `nested_set_chain_outside_pair_unchanged` | 264-309 | A nested `set!`-chain (indexed by `(start, end)` pairs) leaves positions outside the target depth unchanged. | private |

## Archive/V4/FullCorrectness/Equivariance/AssignListRankClosure.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `orderInsensitiveListCmp_self_under_f_eq` | 29-67 | If `cmp x (f x) = .eq` for all `x ∈ L` and `cmp` respects `f` pointwise, then `orderInsensitiveListCmp cmp L (L.map f) = .eq`. | private |
| `mem_foldl_append_init_nil` | 623-647 | Membership characterization for `List.foldl (fun acc x => acc ++ f x) []`: `q ∈ result ↔ ∃ x, q ∈ f x`. | private |

## Archive/V4/FullCorrectness/Equivariance/PathEquivariance.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CalcRankingsInv` | 27-41 | Loop invariant for the depth foldl in `calculatePathRankings`: size and σ-cell-invariance conditions on the `(currentBetween, currentFrom)` accumulator. | private |
| `calculatePathRankings_body_preserves_inv` | 43-190 | One depth-step of the `calculatePathRankings` foldl preserves `CalcRankingsInv σ`; the inductive body lemma. | private |
| `calculatePathRankings_σ_cell_inv_facts` | 192-317 | Cell-level σ-invariance of `calculatePathRankings` output: both `fromRanks` and `betweenRanks` are σ-invariant at every depth. Proved by foldl induction via `calculatePathRankings_body_preserves_inv`. | private |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `insertSorted_map_pointwise_relational` | 111-128 | Relational pointwise variant of `insertSorted_map`: `cmp₂ (f a) (f b) = cmp₁ a b` for `b` in the input list. | private |
| `nodup_keys_unique_value` | 313-334 | If a `List (Nat × Nat)` has Nodup first components, the value at each key is uniquely determined. | private |
| `nodup_pair_keys_unique_value` | 336-358 | If a `List ((Nat × Nat) × Nat)` has Nodup key pairs, the value at each key pair is unique. | private |
| `mem_pathsAtDepth_under_f` | 760-805 | Membership in the `f`-mapped `pathsAtDepth` list. | private |
| `pathsAtDepth_map_f_perm` | 807-898 | The `f`-mapped `pathsAtDepth` list is a `Perm` of the original when `f` reindexes start vertices bijectively. | private |
| `mem_allBetween_under_f` | 1156-1188 | Membership in the `f`-mapped `allBetween` list. | private |
| `allBetween_map_f_perm` | 1190-1251 | The `f`-mapped `allBetween` list is a `Perm` of the original when `f` reindexes `(start, end)` pairs bijectively. | private |
| `calculatePathRankings_body_preserves_rel` | 1538-1732 | One depth-step of the relational `calculatePathRankings` foldl preserves `CalcRankingsRel`. | private |
| `calculatePathRankings_σ_cell_rel_facts` | 1734-1850 | Cell-level τ-relatedness of `calculatePathRankings` outputs on two τ-related inputs; proved by foldl induction. | private |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `pathsOfLength_two_states_at_σ_slot` | 67-147 | For two states related by Stage A (`state₂ = PathState.permute σ state₁`), reading a slot of `state₂` equals reading the σ-shifted slot of `state₁`. | private |
| `pathsAtDepth_two_states_perm` | 158-270 | The `pathsAtDepth` of state₂ is a `Perm` of the σ-mapped `pathsAtDepth` of state₁. | private |
| `mem_pathsAtDepth_two_states_under_f` | 277-289 | Membership characterization for the `f`-mapped `pathsAtDepth` across two Stage-A-related states. | private |
| `allBetween_two_states_perm` | 301-358 | The `allBetween` list of state₂ is a `Perm` of the σ-mapped `allBetween` of state₁. | private |
| `mem_allBetween_two_states_under_f` | 365-385 | Membership characterization for the `f`-mapped `allBetween` across two Stage-A-related states. | private |
| `calculatePathRankings_body_preserves_general` | 894-1155 | One depth-step of the general foldl preserves the relational invariant across two Stage-A-related states. | private |
| `calculatePathRankings_σ_cell_general_facts` | 1163-1278 | Cell-level τ-relatedness of `calculatePathRankings` across two Stage-A-related states; proved by foldl induction. | private |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoop.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_fold_outside_unchanged` | 29-52 | The `convergeOnce` fold body leaves positions `j ∉ l` unchanged through the full `l.foldl`. | private |
| `convergeOnce_fold_writeback` | 54-100 | After the fold processes position `j`, slot `j` holds `rs.getFrom (vc-1) j`. | private |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_fold_unchanged_when_not_flag` | 29-57 | If `convergeOnce`'s fold body starts with `flag = false` and reaches a `false` flag, the array is unchanged throughout. | private |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `calculatePathRankings_getFrom_σ_equivariant_general` | 24-42 | Relational `getFrom (n-1)` for general σ: the two computations run on `initializePaths G` vs `initializePaths (G.permute σ)`. | private |

## Archive/V4/FullCorrectness/Equivariance/StageDRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `τRelatedRks` | 45-49 | Predicate: `rks₂.getD v 0 = rks₁.getD (τ⁻¹ v) 0` for all `v` (τ-shifted ranks). | private |
| `pairCmp` | 53-55 | Lex comparator on `(VertexType × Nat)`: compare first by type, then by vertex index. | private |
| `pairCmp_refl` | 57-60 | `pairCmp a a = .eq`. | private |
| `pairCmp_eval_ne_fst` | 62-66 | `pairCmp a b` when `a.1 ≠ b.1` (reduces to `Nat.compare a.1 b.1`). | private |
| `pairCmp_eval_eq_fst` | 68-72 | `pairCmp a b` when `a.1 = b.1` (reduces to `Nat.compare a.2 b.2`). | private |
| `pairCmp_le_iff` | 74-103 | `pairCmp a b ≠ .gt ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)`. | private |
| `pairCmp_gt_iff` | 105-120 | `pairCmp a b = .gt ↔ b.1 < a.1 ∨ (a.1 = b.1 ∧ b.2 < a.2)`. | private |
| `pairCmp_antisym₁` | 122-131 | Antisymmetry `.lt → .gt` for `pairCmp`. | private |
| `pairCmp_antisym₂` | 133-141 | Antisymmetry `.gt → .lt` for `pairCmp`. | private |
| `pairCmp_trans` | 143-159 | Transitivity `≠ .gt` for `pairCmp`. | private |
| `pairCmp_strict` | 161-170 | `pairCmp a b ≠ .eq` when `a ≠ b`. | private |
| `pairsOf` | 174-176 | Convert `(rks : Array VertexType)` to a list of `(rks[i], i)` pairs. | private |
| `pairsOf_length` | 178-181 | `(pairsOf n rks).length = n`. | private |
| `pairsOf_seconds` | 183-193 | The second components of `pairsOf n rks` are `[0, 1, ..., n-1]`. | private |
| `sortedPairs_length` | 195-199 | The `pairCmp`-sorted pairs list has length `n`. | private |
| `sortedPairs_seconds_perm` | 201-207 | Second components of the sorted pairs are a Perm of `[0, 1, ..., n-1]`. | private |
| `sortedPairs_seconds_nodup` | 209-212 | Second components of the sorted pairs are Nodup. | private |
| `L_pairs_nodup_aux` | 219-240 | Nodup of the `(type, index)` pairs list when indices are distinct. | private |
| `computeDenseRanks_eq_zipIdx_setChain` | 242-287 | `computeDenseRanks` output equals the result of a `set!`-chain indexed by the sorted `(type, index)` pairs. | private |
| `computeDenseRanks_getD_at_pos` | 289-321 | `(computeDenseRanks n rks).getD v 0` equals the dense rank of vertex `v`. | private |
| `computeDenseRanks_inj` | 323-358 | `computeDenseRanks` is injective on vertex indices when tie-free. | private |
| `liftToNat` | 384-386 | Lift `τ : Equiv.Perm (Fin n)` to a total `Nat → Nat` function (identity outside `[0, n)`). | private |
| `pairLift` | 388-390 | Lift `τ` to act on `(VertexType × Nat)` by shifting the index component. | private |
| `liftToNat_in_range` | 392-394 | `liftToNat τ j = (τ ⟨j, _⟩).val` when `j < n`. | private |
| `pairsOf_τ_perm` | 396-469 | `pairsOf n (τ-shifted rks)` is a Perm of `pairLift τ` applied to `pairsOf n rks`. | private |
| `pairCmp_resp_lift_under_tieFree` | 471-498 | `pairCmp` respects `pairLift τ` on tie-free pairs: `pairCmp (pairLift τ a) (pairLift τ b) = pairCmp a b` when `rks` is tie-free. | private |

## Archive/V4/FullCorrectness/Invariants.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `initializePaths_pathsAtDepth_startVertices_eq_range` | 134-166 | Start vertices of depth-`d` slice of `initializePaths G` are exactly `List.range n`. | private |
| `initializePaths_pathsAtDepth_startVertices_nodup` | 168-173 | Start vertices of depth-`d` slice are Nodup. | private |
| `outer_fold_fromAcc_other_target_unchanged` | 183-234 | The outer `fromAcc` foldl leaves depth-slots other than the target depth unchanged. | private |
| `list_pair_max_exists` | 250-272 | A non-empty list of `(α × Nat)` contains an element with maximum second component. | private |
| `chain_image_dense_of_perm_and_density` | 274-378 | If the rank image is dense and the assignList is a Perm-related variant, the image remains dense. | private |
| `chain_image_dense_for_assignRanks_sortBy` | 380-409 | The rank image of `assignRanks cmp (sortBy cmp L)` is dense (downward closed). | private |
| `chain_value_at_vertex_for_assignRanks_sortBy` | 411-489 | For each vertex `v`, some entry in the `assignRanks (sortBy …)` output has first component `v`. | private |
| `comparePathsFrom_eq_compare_of_start_types_ne` | 887-900 | When two start types differ, `comparePathsFrom` reduces to comparing start types only. | private |
| `sortBy_pathsAtTop_length_eq` | 928-942 | `sortBy comparePathsFrom (pathsAtDepth)` preserves length `n`. | private |
| `sortBy_first_q_positions_have_start_types` | 944-1103 | The first `q` positions of the sorted `pathsAtDepth` list have start types `0, 1, ..., q-1`. | private |
| `fromRanks_at_n_minus_1_eq_chain_for_initializePaths` | 1105-1290 | The `fromRanks` at depth `n-1` in `calculatePathRankings (initializePaths G) vts` equals the rank of vertex `v` in the sorted list. | private |
| `convergeOnce_preserves_lower_uniqueness` | 1292-1614 | One `convergeOnce` step preserves `UniquelyHeldBelow q` when the current values below `q` are already distinct. | private |
| `prefix_unique_below_implies_value_held` | 1647-1682 | If `IsPrefixTyping vts` and `UniquelyHeldBelow q vts`, every value `< q` is held by exactly one vertex. | private |
| `exists_two_distinct_q_in_T` | 1684-1749 | If `breakTieCount t₀ vts ≥ 2`, there exist two distinct vertices with type `t₀`. | private |
| `orderVertices_prefix_invariant_strong` | 1915-1964 | Strong inductive: after `runFrom s vts G`, `UniquelyHeldBelow s` holds. | private |

## Archive/V4/FullCorrectness/Equivariance/RunFromRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Array.toList_eq_finRange_map` | 372-383 | `arr.toList = (List.finRange n).map (fun i => arr[i.val])` when `arr.size = n`. | private |

## Archive/V4/FullCorrectness/Equivariance/OrderVerticesGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeLoop_step_σ_chain_preserved_general` | 49-121 | Two-graphs convergeLoop step preservation: chains through an intermediate τ-shifted typing to decompose `σ_chain = σ * τ` (τ ∈ Aut G). | private |

## Archive/V4/FullCorrectness/Main.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `run_swap_invariant_fwd` | 83-145 | Forward direction kernel: for σ ∈ Aut G, `run zeros G = run zeros (G.permute σ)`. Used to bootstrap the (⟹) direction. | private |

## Archive/V4/FullCorrectness/V4Reused.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `swapFin_invol` | 37-45 | — | — |

## Archive/V4/LeanGraphCanonizerV4Tests.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `devSlowTests` | 8 | — | — |
| `graphFromBitmask` | 15-24 | — | — |
| `countUniqueCanonicals` | 25-36 | — | — |
| `applyNatSwaps` | 37-42 | — | — |
| `scrReverse` | 43-46 | — | — |
| `scrRotateLeft` | 47-50 | — | — |
| `scrCut` | 51-52 | — | — |
| `standardScramblers` | 54-57 | — | — |
| `isStableUnder` | 58-66 | — | — |
| `isoVerts4` | 67 | — | — |
| `isoG1` | 68 | — | — |
| `isoG2` | 69-73 | — | — |
| `vtPointed` | 74 | — | — |
| `g1Pointed` | 76-80 | — | — |
| `g2Pointed` | 81-88 | — | — |
| `k3k3` | 89-90 | — | — |
| `c6` | 92-101 | — | — |
| `q3` | 102-108 | — | — |
| `line4` | 109-110 | — | — |
| `line5` | 111-112 | — | — |
| `line6` | 113-120 | — | — |
| `spider` | 121-127 | — | — |
| `k3k3_alt` | 128-146 | — | — |
| `allScrambleStable` | 148-165 | — | — |
| `smoke_verts` | 166 | — | — |
| `smoke_edges` | 167-173 | — | — |

## Archive/V4/UniqueGraphsBySize.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `mkAdj` | 6-7 | — | — |
