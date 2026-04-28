# Lean Theorem Index — GraphCanonizationProofs

Comprehensive index of all public and private Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project.

The file requirements have recently changed, a few early tables don't follow the description guideline correctly.


## Legend

- **Uses**: Theorems/definitions directly referenced in this theorem's proof
- **Used By**: Theorems/definitions that directly reference this one
- **Description**: A short description of what the theorem proves, (not how it achieves this)
- **Notes**: Indicates `@[simp]` attributes, `@[ext]` attributes, instances, if it is stictly stronger than an existing theorem, or other special properties
- **Instance**: Marks typeclass instances that are automatically synthesized

## Basic Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `AdjMatrix.ext` | — | — | Two adjacency matrices are equal iff their adjacency functions agree pointwise. | `@[ext]` |

## Permutation Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `AdjMatrix.permute` | — | — | Relabel vertices of G by permutation σ. Uses σ.symm for left-action semantics. | — |
| `AdjMatrix.permute_adj` | `AdjMatrix.permute` | — | Simplification rule: `(G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `AdjMatrix.permute_one` | `AdjMatrix.permute`, `AdjMatrix.ext` | — | Permuting by the identity does nothing: `G.permute 1 = G`. | `@[simp]` |
| `AdjMatrix.permute_mul` | `AdjMatrix.permute`, `AdjMatrix.ext` | — | Permutation action composes as left action: `G.permute (σ * τ) = (G.permute τ).permute σ`. | — |
| `AdjMatrix.permute_permute_symm` | `AdjMatrix.permute_mul`, `AdjMatrix.permute_one` | — | Permuting by inverse undoes original: `(G.permute σ).permute σ⁻¹ = G`. | `@[simp]` |
| `AdjMatrix.permute_symm_permute` | `AdjMatrix.permute_mul`, `AdjMatrix.permute_one` | — | Inverse permute then permute: `(G.permute σ⁻¹).permute σ = G`. | `@[simp]` |
| `swapVertexLabels_eq_permute` | `AdjMatrix.permute`, `AdjMatrix.ext` | — | Bridge between concrete `swapVertexLabels` and abstract `permute` action. | — |

## Automorphism Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `AdjMatrix.Aut` | `AdjMatrix.permute`, `AdjMatrix.permute_one`, `AdjMatrix.permute_mul`, `AdjMatrix.permute_permute_symm` | — | The automorphism group of G: permutations σ with `G.permute σ = G`. Instances: `DecidableEq`, `Fintype`. | — |
| `mem_Aut_iff` | `AdjMatrix.Aut` | — | Characterization of `Aut` via permute: `σ ∈ G.Aut ↔ G.permute σ = G`. | — |
| `mem_Aut_iff_adj` | `AdjMatrix.permute`, `AdjMatrix.ext` | — | Characterization via adjacency: `σ ∈ G.Aut ↔ ∀ i j, G.adj (σ.symm i) (σ.symm j) = G.adj i j`. | — |
| `AdjMatrix.orbit` | `AdjMatrix.Aut` | — | The `Aut(G)`-orbit of vertex v: all vertices reachable from v by an automorphism. | — |
| `mem_orbit_iff` | `AdjMatrix.orbit` | — | Characterization: `w ∈ G.orbit v ↔ ∃ σ ∈ G.Aut, σ v = w`. | — |
| `AdjMatrix.mem_orbit_self` | `AdjMatrix.orbit`, `AdjMatrix.Aut.one_mem` | — | Reflexivity: `v ∈ G.orbit v`. | — |
| `AdjMatrix.mem_orbit_symm` | `AdjMatrix.orbit`, `AdjMatrix.Aut.inv_mem` | — | Symmetry: `w ∈ G.orbit v → v ∈ G.orbit w`. | — |
| `AdjMatrix.mem_orbit_trans` | `AdjMatrix.orbit`, `AdjMatrix.Aut.mul_mem` | — | Transitivity: `v ∈ G.orbit u → w ∈ G.orbit v → w ∈ G.orbit u`. | — |
| `AdjMatrix.orbitSetoid` | `AdjMatrix.mem_orbit_self`, `AdjMatrix.mem_orbit_symm`, `AdjMatrix.mem_orbit_trans` | — | Same-orbit as equivalence relation; classes are the `Aut(G)`-orbits. | — |
| `AdjMatrix.orbit_stable_under_Aut` | `AdjMatrix.orbit` | — | If `σ ∈ Aut G`, then `σ` maps each orbit to itself. | — |
| `AdjMatrix.exists_Aut_of_mem_orbit` | `AdjMatrix.orbit` | — | Extract automorphism from orbit membership (identity). | — |
| `DecidableEq (AdjMatrix n)` | `AdjMatrix.ext` | — | Instance: adjacency matrix equality is decidable. | Instance |
| `Decidable (σ ∈ G.Aut)` | `AdjMatrix.Aut`, `DecidableEq (AdjMatrix n)` | — | Instance: membership in automorphism group is decidable. | Instance |
| `Fintype G.Aut` | `DecidableEq`, `Decidable (σ ∈ G.Aut)` | — | Instance: `Aut G` is finite as a subgroup of `Equiv.Perm (Fin n)`. | Instance |

## Isomorphic Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `permute_of_Isomorphic` | `AdjMatrix.permute`, `AdjMatrix.permute_one`, `AdjMatrix.permute_mul`, `swapVertexLabels_eq_permute` | — | Extract a concrete permutation from an `Isomorphic` witness. | — |
| `Isomorphic_permute` | `AdjMatrix.permute`, `AdjMatrix.permute_one`, `AdjMatrix.permute_mul`, `swapVertexLabels_eq_permute` | — | Every permutation σ realizes isomorphism: `G ≃ G.permute σ`. Proved by swap induction. | — |
| `Isomorphic_of_permute` | `Isomorphic_permute` | — | If `H = G.permute σ`, then `G ≃ H`. | — |
| `Isomorphic_iff_exists_permute` | `permute_of_Isomorphic`, `Isomorphic_of_permute` | — | Bridge: inductive `Isomorphic ↔ ∃ σ, H = G.permute σ`. | — |

## Actions Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `permNat` | — | — | Re-index natural numbers by permutation (identity outside `[0, n)`). | — |
| `permNat_one` | `permNat` | — | Permuting by identity is the identity on naturals. | `@[simp]` |
| `permNat_lt` | `permNat` | — | Permuting a number `< n` stays `< n`. | — |
| `permNat_of_lt` | `permNat` | — | Explicit formula for `permNat σ i` when `i < n`. | — |
| `permNat_of_ge` | `permNat` | — | Permuting a number `≥ n` is unchanged. | — |
| `permNat_inv_perm` | `permNat_of_lt` | — | Applying σ then σ⁻¹ is identity on in-range naturals. | `@[simp]` |
| `permNat_perm_inv` | `permNat_of_lt` | — | Applying σ⁻¹ then σ is identity on in-range naturals. | `@[simp]` |
| `permNat_fin` | `permNat_of_lt` | — | `permNat` on a `Fin n` value equals the permuted `Fin` value. | `@[simp]` |
| `PathSegment.permute` | — | — | Relabel vertex indices inside a `PathSegment n` by permutation σ. | — |
| `PathsBetween.permute` | `PathSegment.permute`, `permNat` | — | Relabel vertex indices inside a `PathsBetween n`, respecting depth cases. | — |
| `PathsFrom.permute` | `PathsBetween.permute`, `permNat` | — | Relabel vertex indices inside `PathsFrom n`, reordering the `pathsToVertex` list. | — |
| `PathState.permute` | `PathsFrom.permute`, `permNat` | — | Relabel a full `PathState n` by σ using σ.symm semantics. | — |
| `RankState.permute` | `permNat` | — | Relabel a `RankState` by σ: slot `(d, σ⁻¹ s, σ⁻¹ e)` maps to output slot `(d, s, e)`. | — |
| `initializePaths_pathsOfLength_size` | — | — | The `pathsOfLength` array of `initializePaths G` has size `n`. | `@[simp]` |
| `PathState_permute_pathsOfLength_size` | `PathState.permute` | — | Permuting a `PathState` preserves the `pathsOfLength.size`. | `@[simp]` |
| `initializePaths_pathsOfLength_get_size` | `initializePaths_pathsOfLength_size` | — | Depth-`d` slice of `initializePaths G` is a length-`n` array. | — |

## StageA Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `permNat_inv_fin` | `permNat_of_lt` | — | `permNat σ⁻¹ (Fin.val i) = (σ⁻¹ i).val`; Fin-level identity for local `initializePaths` slot rewrites. | private |
| `PathsBetween_initializePaths_eq` | `permNat_of_lt`, `AdjMatrix.permute_adj` | — | For each depth-`d` slot `(s, e)`, the permuted-state's `PathsBetween` equals the σ-relabeled `PathsBetween` from the original state. | private |
| `PathsFrom_initializePaths_eq` | `PathsBetween_initializePaths_eq`, `permNat_of_lt` | — | For each depth-`d` slot `s`, the permuted-state's `PathsFrom` equals the σ-relabeled `PathsFrom` from the original state. | private |
| `initializePaths_Aut_equivariant` | `PathState.permute`, `initializePaths_pathsOfLength_size`, `permNat_of_lt`, `AdjMatrix.permute_adj` | — | Main Stage A theorem: `initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)` for any σ. | **Stage A** — holds for all σ, no Aut(G) hypothesis |

## RankStateInvariants Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `calculatePathRankings_fromRanks_size` | — | — | The `fromRanks` table of `calculatePathRankings` output has size `vc`. | — |
| `setBetween_getD_getD_size` | — | — | `setBetween` preserves the size of every (depth, start)-cell. | — |
| `array_set_chain_outside_unchanged` | — | — | Foldl `set!`-chain leaves untouched positions unchanged. | — |
| `array_set_chain_at_target_nodup` | `array_set_chain_outside_unchanged` | — | Foldl `set!`-chain gives target value at target index when indices are `Nodup`. | — |
| `inner_fold_slice_at_depth` | — | — | Strip the outer `set! depth` wrapper: the result's `depth`-slice equals folding on the initial slice directly. | — |
| `inner_fold_other_depth_unchanged` | — | — | Inner fold only writes to depth-slot, other depths are preserved. | — |
| `setBetween_fold_slice_at_depth` | — | — | `setBetween` fold depth-slice equals folding the depth-slice directly. | — |
| `setBetween_fold_other_depth_unchanged` | — | — | `setBetween` fold only writes to outer depth, other depths preserved. | — |
| `RankState.σInvariant` | — | — | Predicate on `rs : RankState`: size-shape and value σ-invariance conditions sufficient to conclude `RankState.permute σ rs = rs`. | **Key structure** — packages σ-invariance for extensionality |
| `RankState.σInvariant.permute_eq_self` | `RankState.σInvariant`, `RankState.permute`, `permNat_of_lt` | — | Extensionality: σ-invariance implies `RankState.permute σ rs = rs`. | **Extensionality** — σ-invariance ⟹ permute equals identity |
| `calculatePathRankings_size_inv` | `setBetween_getD_getD_size` | — | Size facts on `calculatePathRankings` output: `betweenRanks` is `vc×vc×vc`, `fromRanks` is `vc×vc`. | — |
| `Array_set!_getD_self` | — | — | `(xs.set! i v).getD i d = v` when `i < xs.size`. | private |
| `Array_set!_getD_ne` | — | — | `(xs.set! i v).getD j d = xs.getD j d` when `i ≠ j`. | private |
| `Array_set!_eq_self_of_size_le` | — | — | `xs.set! i v = xs` when `xs.size ≤ i` (out-of-bounds write is identity). | private |
| `setBetween_size` | — | — | `setBetween` preserves the outer-array size. | private |
| `setBetween_getD_size` | — | — | `setBetween` preserves the size of every depth-row. | private |
| `from_set_getD_size` | — | — | Folding `set!` on `fromAcc` preserves the size of every depth-row. | private |

## ComparisonSort Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `sortBy_map` | — | — | `sortBy cmp (L.map f) = (sortBy cmp L).map f` when `f` preserves `cmp`; instantiated with `PathSegment.permute σ` for σ-equivariance. | — |
| `perm_insertSorted` | — | — | `insertSorted cmp a L` is a `List.Perm` of `a :: L`. | — |
| `sortBy_perm` | `perm_insertSorted` | — | `sortBy cmp L` is a `List.Perm` of `L`. | — |
| `sortedPerm_class_eq` | — | — | KEY LEMMA: for sorted lists `M`, `M'` with `M.Perm M'`, the elements at position `i` of `M` and `M'` lie in the same `cmp`-equivalence class. Proved by a counting argument on sorted prefix/suffix structure. | — |
| `sortBy_pairwise` | — | — | `sortBy cmp L` is `Pairwise (cmp · · ≠ .gt)`, i.e. the output list is sorted under `cmp`. | — |
| `foldl_pointwise_eq` | — | — | If two equal-length lists agree element-wise under `f` at every accumulator value, their `List.foldl f` results are equal. | — |
| `orderInsensitiveListCmp_perm` | `sortBy_perm`, `sortBy_pairwise`, `sortedPerm_class_eq`, `foldl_pointwise_eq` | — | `orderInsensitiveListCmp cmp L₁ L₂` is invariant under permutations of `L₁` and `L₂`, given a compatible total preorder. | — |
| `assignRanks_length` | — | — | `(assignRanks cmp L).length = L.length`. | — |
| `assignRanks_map_fst` | — | — | `(assignRanks cmp L).map (·.1) = L`: first components reproduce the input list in order. | — |
| `assignRanks_getElem_fst` | `assignRanks_map_fst`, `assignRanks_length` | — | Element-wise: `((assignRanks cmp L)[i]).1 = L[i]`. | — |
| `assignRanks_map_of_cmp_respect` | — | — | `assignRanks cmp (L.map f) = (assignRanks cmp L).map (fun e => (f e.1, e.2))` when `f` preserves `cmp`; foundational for the σ-equivariance pipeline. | — |
| `assignRanks_map_relational` | — | — | Relational form: `assignRanks cmp₂ (L.map f) = (assignRanks cmp₁ L).map (fun e => (f e.1, e.2))` when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. Used by Stage B-rel. | — |
| `assignRanks_image_dense` | — | — | Rank set is downward-closed: for any entry in `assignRanks cmp L`, every `k ≤ entry.2` has a witness in the output. | — |
| `assignRanks_rank_lt_length` | — | — | Every rank in `assignRanks cmp L` is `< L.length`; bounds vertex type values produced by `convergeOnce`. | — |
| `assignRanks_rank_le_pos` | `assignRanks_length` | — | Rank at position `k` in `assignRanks cmp L` is `≤ k`. | — |
| `assignRanks_pairwise_rank_le` | — | — | Ranks in `assignRanks cmp L` are pairwise non-decreasing along the list. | — |
| `assignRanks_rank_monotone` | `assignRanks_pairwise_rank_le`, `assignRanks_length` | — | Rank at position `i` is `≤` rank at position `j` for `i ≤ j < L.length`. | — |
| `assignRanks_rank_eq_pos_when_distinct` | — | — | Rank at position `k` equals `k` when all consecutive pairs in `L` have `cmp ≠ .eq`. | — |
| `assignRanks_rank_eq_of_prefix` | `assignRanks_length` | — | Rank at position `k < A.length` in `assignRanks cmp (A ++ B)` equals rank at `k` in `assignRanks cmp A`. | — |
| `assignRanks_rank_eq_pos_when_distinct_prefix` | `assignRanks_rank_eq_of_prefix`, `assignRanks_rank_eq_pos_when_distinct` | — | Rank equals position for all `k < q` when consecutive elements in the first `q` entries have `cmp ≠ .eq`. | — |
| `assignRanks_rank_eq_at_succ_when_cmp_eq` | `assignRanks_rank_eq_of_prefix` | — | Ranks at positions `i` and `i+1` are equal when `cmp L[i] L[i+1] = .eq`. | — |
| `assignRanks_rank_eq_within_eq_class` | `assignRanks_rank_eq_at_succ_when_cmp_eq` | — | For a sorted list under a total preorder, if `cmp L[i] L[j] = .eq` and `i ≤ j`, the assigned ranks at `i` and `j` agree. | — |
| `assignRanks_rank_succ_when_cmp_neq_eq` | `assignRanks_rank_eq_of_prefix` | — | Rank at `i+1` equals rank at `i` plus 1 when `cmp L[i] L[i+1] ≠ .eq`. | — |
| `assignRanks_rank_eq_of_sorted_perm` | `assignRanks_rank_le_pos`, `sortedPerm_class_eq`, `assignRanks_rank_eq_at_succ_when_cmp_eq`, `assignRanks_rank_succ_when_cmp_neq_eq` | — | For sorted `X.Perm Y` (under a total preorder), ranks at each position `i` agree between `assignRanks cmp X` and `assignRanks cmp Y`. | — |
| `sortBy_eq_of_perm_strict` | `sortBy_perm`, `sortBy_pairwise` | — | If `X.Perm Y` and `cmp` is strict on `X` (no two distinct elements are `cmp`-equal), then `sortBy cmp X = sortBy cmp Y`. | — |
| `insertSorted_map` | — | — | `insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f` when `f` globally preserves `cmp`. | private |
| `sorted_perm_head_class_eq` | — | — | Head-element lemma used in `sortedPerm_class_eq`: the head of a sorted list and the head of any Perm share the same `cmp`-class. | private |
| `insertSorted_pairwise` | — | — | `insertSorted cmp a L` is `Pairwise (cmp · · ≠ .gt)` when `L` is, i.e. insertion preserves sortedness. | private |
| `assignRanksStep` | — | — | Single foldl step for `assignRanks`: appends `(elem, rank)` to accumulator. | private |
| `assignRanks_eq_foldl` | — | — | `assignRanks cmp L` equals a `List.foldl` of `assignRanksStep` starting from `([], 0)`. | private |
| `assignRanksStep_fst_length` | — | — | `assignRanksStep` preserves the length of the accumulated first-component list. | private |
| `assignRanksStep_fst_map_fst` | — | — | First components after `assignRanksStep` are the original list elements in order. | private |
| `assignRanks_aux_length` | — | — | Length of the `assignRanks` foldl accumulator at each step. | private |
| `assignRanks_aux_map_fst` | — | — | First-component map of the `assignRanks` foldl accumulator reproduces the prefix. | private |
| `assignRanksStep_commutes_with_f_map` | — | — | `assignRanksStep` commutes with global `f`-mapping when `f` preserves `cmp`. | private |
| `assignRanks_foldl_map_f` | — | — | Foldl of `assignRanksStep` on `L.map f` equals foldl on `L` with `f` applied to first components; global hypothesis. | private |
| `assignRanksStep_commutes_relational` | — | — | Relational commutation: `assignRanksStep` with `cmp₂` on `f`-mapped input equals `assignRanksStep` with `cmp₁` on original when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b` in processed prefix. | private |
| `assignRanks_foldl_map_f_relational` | — | — | Foldl of `assignRanksStep` commutes with `f`-mapping in the relational form (pointwise hypothesis on already-seen prefix). | private |
| `assignRanksStep_rank_le` | — | — | The rank produced by `assignRanksStep` is `≤` the position index. | private |
| `assignRanks_aux_rank_le` | — | — | All ranks in the foldl accumulator are `≤` their position. | private |
| `assignRanksStep_density_invariant` | — | — | `assignRanksStep` preserves the density invariant: every rank below the current max has a witness. | private |
| `assignRanks_aux_density` | — | — | Density invariant holds for the full foldl accumulator. | private |
| `assignRanksFoldl_lastEntry_rank_le` | — | — | The last entry's rank in the foldl accumulator is `≤` its list-end index. | private |
| `assignRanks_snoc_decompose` | — | — | Decompose `assignRanks cmp (L ++ [a])` into `assignRanks cmp L` plus one final entry. | private |
| `assignRanks_snoc_decompose_strict` | — | — | Strict variant: final rank is `assignRanks cmp L`.length when `cmp (last L) a ≠ .eq`. | private |
| `assignRanks_foldl_lastEntry_fst` | — | — | The first component of the foldl's last entry is the last element of the input list. | private |
| `assignRanksStep_preserves_invariant` | — | — | `assignRanksStep` preserves the combined (length, map_fst, rank_le) invariant used by `assignRanks_foldl_invariant`. | private |
| `assignRanks_foldl_invariant` | — | — | The combined invariant holds for the full foldl. | private |
| `assignRanks_strong_invariant` | — | — | Strong combined invariant for `assignRanks` used to prove `rank_eq_pos_when_distinct_prefix` and `rank_eq_within_eq_class`. | private |
| `sorted_eq_of_perm_strict_aux` | — | — | Auxiliary for `sortBy_eq_of_perm_strict`: equal sorted lists under strict `cmp`. | private |

## LabelEdgesCharacterization Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `computeDenseRanks_size` | — | — | `(computeDenseRanks numVertices rks).size = numVertices`. | — |
| `labelEdgesStep` | — | — | The `labelEdgesAccordingToRankings` fold body extracted as a standalone function (swap-and-update). | — |
| `set!_getD_self_aux` | — | — | `(xs.set! i v).getD i d = v` when `i < xs.size`; local helper. | private |
| `set!_getD_ne_aux` | — | — | `(xs.set! i v).getD j d = xs.getD j d` when `i ≠ j`; local helper. | private |
| `rankMap_swap_step_eq` | — | — | The rankMap double-`set!` swap step is equivalent to composing one `Equiv.swap` into the indexing permutation. | private |
| `labelEdges_fold_permutes` | `swapVertexLabels_eq_permute`, `AdjMatrix.permute_mul` | — | The `labelEdgesAccordingToRankings` foldl maintains `∃ σ', acc.1 = G.permute σ'`; weak invariant. | — |
| `labelEdges_fold_strong` | `swapVertexLabels_eq_permute`, `AdjMatrix.permute_mul`, `rankMap_swap_step_eq` | — | Strong fold invariant: tracks both the cumulative permutation σ and `acc.2.getD v 0 = rankMap₀.getD (σ⁻¹ v) 0` pointwise. | — |
| `labelEdges_fold_terminal_aux` | `rankMap_swap_step_eq` | — | Auxiliary: after processing a Nodup sublist of `finRange n`, the terminal rankMap satisfies `rankMap[v] = v`. | private |
| `labelEdges_terminal_rankMap_identity` | `labelEdges_fold_terminal_aux` | — | After the full foldl over `List.finRange n`, the terminal rankMap is the identity: `rankMap.getD v.val 0 = v.val`. | — |

## Tiebreak Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `VtsInvariant` | — | — | Predicate: `σ` maps `vts` to itself (`vts.getD (σ v).val 0 = vts.getD v.val 0` for all `v`). | — |
| `VtsInvariant.one` | — | — | The identity permutation always satisfies `VtsInvariant`. | — |
| `VtsInvariant.mul` | — | — | Composition: if σ and τ both satisfy `VtsInvariant`, so does `σ * τ`. | — |
| `VtsInvariant.inv` | — | — | Inversion: if σ satisfies `VtsInvariant`, so does `σ⁻¹`. | — |
| `AdjMatrix.TypedAut` | — | — | Subgroup of `Aut G` whose elements also satisfy `VtsInvariant vts`. | — |
| `mem_TypedAut_iff` | — | — | `σ ∈ G.TypedAut vts ↔ σ ∈ G.Aut ∧ VtsInvariant σ vts`. | — |
| `AdjMatrix.TypedAut_le_Aut` | — | — | `G.TypedAut vts` is a subgroup of `G.Aut`. | — |
| `Decidable (VtsInvariant σ vts)` | — | — | Instance: `VtsInvariant σ vts` is decidable. | Instance |
| `Decidable (σ ∈ G.TypedAut vts)` | — | — | Instance: membership in `TypedAut` is decidable. | Instance |
| `Fintype (G.TypedAut vts)` | — | — | Instance: `G.TypedAut vts` is finite. | Instance |
| `VtsInvariant.replicate_zero` | — | — | The all-zeros array satisfies `VtsInvariant σ` for any σ. | — |
| `TypedAut_replicate_zero` | — | — | `G.TypedAut (Array.replicate n 0) = G.Aut` (zeros do not constrain automorphisms beyond Aut). | — |
| `typeClass` | — | — | The set of `Fin n` vertices with vertex type exactly `t₀` in `vts`. | — |
| `shiftAbove_size` | — | — | `shiftAbove t₀ vts` preserves array size. | — |
| `shiftAbove_getD` | — | — | Value of `shiftAbove t₀ vts` at position `j`. | — |
| `shiftAbove_getD_below` | — | — | Positions with type `< t₀` are unchanged by `shiftAbove`. | — |
| `shiftAbove_getD_above` | — | — | Positions with type `> t₀` have their value incremented by 1 after `shiftAbove`. | — |
| `shiftAbove_getD_target` | — | — | Positions with type `= t₀` also have value shifted after `shiftAbove`. | — |
| `breakTieCount` | — | — | Number of vertices in `vts` with type `t₀`. | — |
| `breakTie_noop` | — | — | If `t₀` does not appear in `vts`, `breakTie t₀ vts = vts`. | — |
| `breakTie_eq_promote_shift` | — | — | `breakTie t₀ vts = shiftAbove t₀ (breakTiePromote t₀ vts)`. | — |
| `btStep` | — | — | Single fold step for `breakTiePromote`: promotes the minimum tied vertex. | private |
| `btStep_size` | — | — | `btStep` preserves array size. | private |
| `breakTiePromote_eq_fold` | — | — | `breakTiePromote t₀ vts` is expressed as a `List.foldl` of `btStep`. | private |
| `btFold_size` | — | — | The `btStep` foldl preserves array size. | private |
| `btStep_getD_ne` | — | — | `btStep` leaves positions with type `≠ t₀` unchanged. | private |
| `btFold_getD_ne` | — | — | The `btStep` foldl leaves positions with type `≠ t₀` unchanged. | private |
| `breakTiePromote_size` | — | — | `breakTiePromote t₀ vts` preserves array size. | — |
| `breakTiePromote_getD_of_ne` | — | — | `breakTiePromote` leaves positions whose type is not `t₀` unchanged. | — |
| `breakTie_size` | — | — | `breakTie t₀ vts` preserves array size. | — |
| `breakTie_getD_below` | — | — | Positions with type `< t₀` are unchanged by `breakTie`. | — |
| `breakTie_getD_above` | — | — | Positions with type `> t₀` have their value shifted up by 1 after `breakTie`. | — |
| `breakTie_getD_above_or` | — | — | Combined case: value at position `≥ t₀` after `breakTie`. | — |
| `btFold_no_target` | — | — | If no position in the fold list has type `t₀`, the foldl is the identity. | private |
| `btStep_notfirst` | — | — | `btStep` is the identity when the current position is not the first promoted position. | private |
| `VertexType_add_one_ne` | — | — | `t₀ + 1 ≠ t₀` for any vertex type `t₀`. | private |
| `btFold_from_notfirst_getD` | — | — | Value formula for `btFold` starting from a position past the first promoted vertex. | private |
| `btFold_getD_not_mem` | — | — | The `btStep` foldl leaves positions outside its list unchanged. | private |
| `breakTiePromote_getD_at_min` | — | — | Value at the minimum vertex with type `t₀` after `breakTiePromote`. | — |
| `breakTiePromote_getD_at_other` | — | — | Value at non-minimum vertices with type `t₀` after `breakTiePromote`. | — |
| `shiftAbove_getD_ne_target` | — | — | `shiftAbove` at a position whose type differs from `t₀`. | private |
| `breakTie_getD_at_min` | — | — | The minimum vertex with type `t₀` receives a unique promoted value after `breakTie`. | — |
| `breakTieCount_eq_countP` | — | — | `breakTieCount t₀ vts = vts.toList.countP (· == t₀)`. | — |
| `breakTieCount_ge_two_of_distinct` | — | — | If two distinct vertices have type `t₀`, then `breakTieCount t₀ vts ≥ 2`. | — |
| `breakTie_getD_at_other` | — | — | Non-minimum vertices with type `t₀` receive the shifted-up value after `breakTie`. | — |
| `breakTie_getD_target` | — | — | Value at arbitrary positions after `breakTie`, by type case. | — |
| `breakTie_getD_target_ge` | — | — | Every position's value after `breakTie` is `≥` its original value. | — |
| `breakTie_Aut_stabilizer` | — | — | The `breakTie` output is invariant under `G.TypedAut (breakTie t₀ vts)`. | — |
| `breakTie_TypedAut_le` | — | — | `G.TypedAut (breakTie t₀ vts) ≤ G.TypedAut vts`: breaking a tie can only shrink the typed automorphism group. | — |
| `breakTie_strict_shrink` | — | — | If `breakTieCount t₀ vts ≥ 2`, then `G.TypedAut (breakTie t₀ vts) < G.TypedAut vts` (strictly smaller). | — |
| `runFrom` | — | — | Sequential tiebreak from vertex `start` up to `n`: iterates `convergeLoop ∘ breakTie` for each tied type. | — |
| `breakTieAt` | — | — | Tiebreak that resolves only the tie at vertex `keep`, bumping all same-type vertices above it. | — |
| `bTAStep` | — | — | Single fold step for `breakTieAt`. | private |
| `breakTieAt_eq_fold` | — | — | `breakTieAt vts t₀ keep` is expressed as a `List.foldl` of `bTAStep`. | private |
| `bTAStep_size` | — | — | `bTAStep` preserves array size. | private |
| `bTAFold_size` | — | — | The `bTAStep` foldl preserves array size. | private |
| `breakTieAt_size` | — | — | `breakTieAt vts t₀ keep` preserves array size. | — |
| `bTAStep_getD_ne` | — | — | `bTAStep` leaves all positions other than `keep` unchanged. | private |
| `bTAFold_getD_of_notin` | — | — | `bTAFold` leaves positions not in its list unchanged. | private |
| `bTAFold_getD_of_ne` | — | — | `bTAFold` leaves positions `≠ keep` unchanged. | private |
| `breakTieAt_getD_of_ne` | — | — | `breakTieAt` leaves positions `≠ keep` unchanged. | — |
| `bTAStep_preserves_keep` | — | — | `bTAStep` preserves the value at `keep`. | private |
| `bTAFold_preserves_keep` | — | — | The `bTAStep` foldl preserves the value at `keep`. | private |
| `breakTieAt_getD_keep` | — | — | `breakTieAt` preserves the value at `keep`. | — |
| `bTAFold_getD_promoted` | — | — | Value at positions promoted by `bTAFold`. | private |
| `breakTieAt_getD_promoted` | — | — | Value at positions promoted by `breakTieAt`. | — |
| `breakTieAt_VtsInvariant_eq` | — | — | `breakTieAt` preserves `VtsInvariant τ` when `τ keep = keep`. | — |

## ComparePathSegments Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `cmpInner_eq_lt` | — | — | Evaluates the inner-inner `comparePathSegments` expression to `.lt` given `yR < xR ∨ (xR = yR ∧ ye < xe)`. | private |
| `cmpInner_eq_gt` | — | — | Evaluates the inner-inner `comparePathSegments` expression to `.gt` given `xR < yR ∨ (xR = yR ∧ xe < ye)`. | private |
| `cmpInner_eq_eq` | — | — | Evaluates the inner-inner `comparePathSegments` expression to `.eq` when `xR = yR` and `xe = ye`. | private |
| `cmpInner_trichotomy` | — | — | Exhaustive case split: for any `(xR, xe)` and `(yR, ye)`, exactly one of the `.gt`, `.eq`, or `.lt` conditions for the inner-inner comparator holds. | private |
| `comparePathSegments_total_preorder` | `cmpInner_eq_lt`, `cmpInner_eq_gt`, `cmpInner_eq_eq`, `cmpInner_trichotomy` | — | Proves `comparePathSegments` satisfies all four total-preorder properties: reflexivity, both antisymmetries (`.lt → .gt` and `.gt → .lt`), and ≤-transitivity (`≠ .gt`). Mixed `bottom`/`inner` cases use the fixed `bottom < inner` ordering; inner-inner cases reduce to Nat-tuple lexicographic order. | — |
| `orderInsensitiveListCmp_refl` | `sortBy_perm` | — | `orderInsensitiveListCmp cmp L L = .eq` when `cmp` is reflexive on elements of `L`. Uses `sortBy_perm` to transfer reflexivity from `L` to its sorted form. | — |
| `comparePathSegments_equivCompat` | — | — | If `comparePathSegments vts br p q = .eq`, then `p` and `q` compare identically against any third segment `r` in either argument position. The `h_compat` hypothesis required by `orderInsensitiveListCmp_trans` and `_equivCompat`. | — |
| `orderInsensitiveListCmp_foldl_init_preserved` | — | — | Once the `orderInsensitiveListCmp` foldl accumulator is non-`.eq`, all subsequent steps short-circuit and the value is preserved unchanged. Used by `_swap_lt`, `_swap_gt`, `foldl_zip_trans`, and `foldl_zip_eq_implies_pairwise_eq` to discharge "init already set" cases. | private |
| `orderInsensitiveListCmp_swap_lt` | `orderInsensitiveListCmp_foldl_init_preserved` | — | Antisymmetry-`.lt → .gt` lift: `orderInsensitiveListCmp cmp L₁ L₂ = .lt → orderInsensitiveListCmp cmp L₂ L₁ = .gt`. Handles equal-length and length-mismatch cases separately. | — |
| `orderInsensitiveListCmp_swap_gt` | `orderInsensitiveListCmp_foldl_init_preserved` | — | Antisymmetry-`.gt → .lt` lift: `orderInsensitiveListCmp cmp L₁ L₂ = .gt → orderInsensitiveListCmp cmp L₂ L₁ = .lt`. Mirror of `_swap_lt`. | — |
| `foldl_zip_trans` | `orderInsensitiveListCmp_foldl_init_preserved` | — | For equal-length lists `A`, `B`, `C`: if `(zip A B).foldl ≠ .gt` and `(zip B C).foldl ≠ .gt`, then `(zip A C).foldl ≠ .gt`. Proved by induction on the head pair `(cmp a b, cmp b c)` using antisym₁ and bilateral compat. Core of `orderInsensitiveListCmp_trans`. | private |
| `orderInsensitiveListCmp_trans` | `sortBy_perm`, `foldl_zip_trans` | — | Transitivity lift: `orderInsensitiveListCmp cmp L₁ L₂ ≠ .gt → ... L₂ L₃ ≠ .gt → ... L₁ L₃ ≠ .gt`. Equal-length case delegates to `foldl_zip_trans`; length-mismatch cases reduce to length arithmetic. | — |
| `foldl_zip_eq_implies_pairwise_eq` | `orderInsensitiveListCmp_foldl_init_preserved` | — | If the `orderInsensitiveListCmp` foldl over a zipped list returns `.eq`, then every element pair in that list has `cmp = .eq` pointwise. | private |
| `orderInsensitiveListCmp_equivCompat` | `sortBy_perm`, `foldl_pointwise_eq`, `foldl_zip_eq_implies_pairwise_eq` | — | Bilateral compat lift: if `orderInsensitiveListCmp cmp L₁ L₂ = .eq`, then `L₁` and `L₂` compare identically against any third list in either argument position. Extracts pointwise class equality via `foldl_zip_eq_implies_pairwise_eq`, then applies `foldl_pointwise_eq`. | — |
| `comparePathsBetween_total_preorder` | `comparePathSegments_total_preorder`, `comparePathSegments_equivCompat`, `orderInsensitiveListCmp_refl`, `orderInsensitiveListCmp_swap_lt`, `orderInsensitiveListCmp_swap_gt`, `orderInsensitiveListCmp_trans` | — | `comparePathsBetween` is a total preorder, assembled by lifting all four properties of `comparePathSegments_total_preorder` through the `orderInsensitiveListCmp` helpers. Compares first by `endVertexIndex` type, then by the order-insensitive list of `connectedSubPaths`. | — |

## CompareEquivariant Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `orderInsensitiveListCmp_map` | `sortBy_map`, `sortBy_perm` | — | `orderInsensitiveListCmp` is invariant under applying `f` to both lists when `f` globally preserves `cmp`. | — |
| `insertSorted_map_pointwise` | — | — | Pointwise variant of `insertSorted_map`: requires `cmp (f a) (f b) = cmp a b` only for `b ∈ L`. | private |
| `sortBy_map_pointwise` | `insertSorted_map_pointwise`, `sortBy_perm` | — | Pointwise variant of `sortBy_map`: requires `cmp (f a) (f b) = cmp a b` only for `a, b ∈ L`. | — |
| `foldl_congr_mem` | — | — | Pointwise foldl congruence: `f` and `g` agreeing on all `(acc, a)` pairs with `a ∈ L` implies equal foldl results. | private |
| `orderInsensitiveListCmp_map_pointwise` | `sortBy_map_pointwise`, `sortBy_perm`, `foldl_congr_mem` | — | Pointwise variant of `orderInsensitiveListCmp_map`: requires `cmp` respects only for pairs from `L₁ ++ L₂`. | — |
| `comparePathSegments_σ_equivariant` | `AdjMatrix.permute_adj` | — | `comparePathSegments vts br (PathSegment.permute σ p) (PathSegment.permute σ q) = comparePathSegments vts br p q` under σ-invariant `vts` and `br`. | — |
| `map_reindex_perm` | — | — | Reindex-perm lemma: σ-reindexing `L.map act` gives a `List.Perm` of `L.map act`. | — |
| `PathsBetween_permute_connectedSubPaths_perm` | `map_reindex_perm`, `permNat_of_lt` | — | `(p.permute σ).connectedSubPaths.Perm (p.connectedSubPaths.map (PathSegment.permute σ))` for depth>0 paths of length `vc`. | — |
| `PathsFrom_permute_pathsToVertex_perm` | `map_reindex_perm`, `permNat_of_lt` | — | `(p.permute σ).pathsToVertex.Perm (p.pathsToVertex.map (PathsBetween.permute σ))` for length-`vc` `pathsToVertex`. | — |
| `comparePathsBetween_σ_equivariant` | `PathsBetween_permute_connectedSubPaths_perm`, `comparePathSegments_σ_equivariant`, `orderInsensitiveListCmp_perm`, `orderInsensitiveListCmp_map` | — | `comparePathsBetween vts br (p₁.permute σ) (p₂.permute σ) = comparePathsBetween vts br p₁ p₂` under σ-invariant `vts`/`br` and length conditions. | — |
| `comparePathsBetween_equivCompat` | `orderInsensitiveListCmp_equivCompat`, `comparePathSegments_equivCompat` | — | Bilateral compat for `comparePathsBetween`: if it returns `.eq`, both arguments compare identically against any third. | — |
| `comparePathsFrom_σ_equivariant` | `PathsFrom_permute_pathsToVertex_perm`, `comparePathsBetween_σ_equivariant`, `orderInsensitiveListCmp_perm`, `orderInsensitiveListCmp_map_pointwise` | — | `comparePathsFrom vts br (p₁.permute σ) (p₂.permute σ) = comparePathsFrom vts br p₁ p₂` under σ-invariant `vts`/`br` and length conditions. | — |
| `betweenRankFn_σ_inv_from_cells` | — | — | Cell-level σ-invariance of a 3D table lifts to a σ-invariant function (the `betweenRankFn` projection). | — |
| `initializePaths_σInv_via_Aut` | `initializePaths_Aut_equivariant` | — | For σ ∈ Aut G, `initializePaths G = PathState.permute σ (initializePaths G)`. Direct corollary of Stage A. | — |

## PathsAtDepthStructure Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `initializePaths_pathsOfLength_get_eq` | `initializePaths_pathsOfLength_size` | — | Explicit constructor form of the depth-`d` slice of `initializePaths G`. | private |
| `initializePaths_pathsAtDepth_structure` | `initializePaths_pathsOfLength_get_eq`, `initializePaths_pathsOfLength_size` | — | Outer length `= n`, start-vertex enumeration `= List.range n`, inner-length conditions for a depth-`d` slice of `initializePaths G`. | — |
| `initializePaths_pathsAtDepth_inner_structure` | `initializePaths_pathsOfLength_get_eq`, `initializePaths_pathsOfLength_size` | — | Inner structural facts: `startVertexIndex` is constant within a `PathsFrom`, and `endVertexIndex.val`s enumerate `List.range n`. | private |
| `initializePaths_allBetween_pairs_facts` | `initializePaths_pathsAtDepth_structure`, `initializePaths_pathsAtDepth_inner_structure` | — | The `(start, end)` pairs of `allBetween` are Nodup and cover every `(s, e) ∈ Fin n × Fin n`. | — |

## ChainSetInvariant Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `set_chain_size_preserving` | — | — | The `set!`-chain foldl on `fromAcc` preserves the outer array size. | — |
| `set_chain_row_size_preserving` | — | — | The `set!`-chain foldl preserves each depth-row's size. | — |
| `set_chain_σInvariant` | `inner_fold_slice_at_depth`, `array_set_chain_outside_unchanged`, `array_set_chain_at_target_nodup`, `set_chain_size_preserving`, `set_chain_row_size_preserving` | — | The `fromRanks` `set!`-chain preserves σ-invariance given σ-rank-closure of the assignList and start-vertex permutation coverage. | — |
| `nested_set_chain_outside_pair_unchanged` | — | — | A nested `set!`-chain (indexed by `(start, end)` pairs) leaves positions outside the target depth unchanged. | private |
| `nested_set_chain_at_target_pair_nodup` | `nested_set_chain_outside_pair_unchanged` | — | Nested `set!`-chain at target `(d, s, e)` gives the inserted value when the `(start, end)` keys are Nodup. | — |
| `setBetween_chain_size_preserving` | — | — | The `setBetween` chain preserves the outer `betweenRanks` array size. | — |
| `setBetween_chain_row_size_preserving` | — | — | The `setBetween` chain preserves each depth-row's size. | — |
| `setBetween_chain_cell_size_preserving` | — | — | The `setBetween` chain preserves each `(depth, start)` cell's size. | — |
| `setBetween_chain_σInvariant` | `inner_fold_slice_at_depth`, `nested_set_chain_at_target_pair_nodup`, `setBetween_chain_size_preserving`, `setBetween_chain_row_size_preserving`, `setBetween_chain_cell_size_preserving` | — | The `betweenRanks` `setBetween`-chain preserves σ-invariance given σ-rank-closure of the assignList and `(start, end)`-pair Nodup coverage. | — |

## AssignListRankClosure Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `orderInsensitiveListCmp_self_under_f_eq` | `sortBy_map_pointwise`, `sortBy_perm` | — | If `cmp x (f x) = .eq` for all `x ∈ L` and `cmp` respects `f` pointwise, then `orderInsensitiveListCmp cmp L (L.map f) = .eq`. | private |
| `comparePathSegments_σ_self_eq` | — | — | `comparePathSegments vts br p (PathSegment.permute σ p) = .eq` under σ-invariant `vts` and `br`. | — |
| `comparePathsBetween_σ_self_eq` | `comparePathSegments_σ_self_eq`, `orderInsensitiveListCmp_self_under_f_eq`, `comparePathSegments_σ_equivariant` | — | `comparePathsBetween vts br p (p.permute σ) = .eq` under σ-invariant `vts`/`br` and length conditions. | — |
| `comparePathsFrom_σ_self_eq` | `comparePathsBetween_σ_self_eq`, `orderInsensitiveListCmp_self_under_f_eq`, `comparePathsBetween_σ_equivariant` | — | `comparePathsFrom vts br p (p.permute σ) = .eq` under σ-invariant `vts`/`br` and length conditions. | — |
| `state_σ_fixed_pathsOfLength_at_σ_slot` | `initializePaths_pathsOfLength_size`, `permNat_of_lt` | — | For a σ-fixed `PathState`, reading slot `s` of the depth-`d` array equals reading slot `σ s` in the original. | — |
| `comparePathsFrom_total_preorder` | `comparePathsBetween_total_preorder`, `comparePathsBetween_equivCompat`, `orderInsensitiveListCmp_refl`, `orderInsensitiveListCmp_swap_lt`, `orderInsensitiveListCmp_swap_gt`, `orderInsensitiveListCmp_trans` | — | `comparePathsFrom` satisfies all four total-preorder properties, lifted from `comparePathsBetween_total_preorder` through `orderInsensitiveListCmp`. | — |
| `from_assignList_σ_rank_closure` | `comparePathsFrom_σ_self_eq`, `comparePathsFrom_σ_equivariant`, `sortBy_perm`, `assignRanks_map_fst`, `state_σ_fixed_pathsOfLength_at_σ_slot` | — | The `fromRanks` assignList is σ-rank-closed: for each `(p, r)` in the list, `(PathsFrom.permute σ p, r)` is also in the list. | — |
| `mem_foldl_append_init_nil` | — | — | Membership characterization for `List.foldl (fun acc x => acc ++ f x) []`: `q ∈ result ↔ ∃ x, q ∈ f x`. | private |
| `mem_allBetween_iff` | `mem_foldl_append_init_nil` | — | `q ∈ allBetween ↔ ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex`. | — |
| `between_assignList_σ_rank_closure` | `comparePathsBetween_σ_self_eq`, `comparePathsBetween_σ_equivariant`, `sortBy_perm`, `assignRanks_map_fst`, `mem_allBetween_iff`, `initializePaths_allBetween_pairs_facts` | — | The `betweenRanks` assignList is σ-rank-closed: for each `(q, r)` in the list, `(PathsBetween.permute σ q, r)` is also in the list. | — |

## PathEquivariance Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `CalcRankingsInv` | — | — | Loop invariant for the depth foldl in `calculatePathRankings`: size and σ-cell-invariance conditions on the `(currentBetween, currentFrom)` accumulator. | private |
| `calculatePathRankings_body_preserves_inv` | `CalcRankingsInv`, `initializePaths_σInv_via_Aut`, `initializePaths_pathsAtDepth_structure`, `initializePaths_allBetween_pairs_facts`, `betweenRankFn_σ_inv_from_cells`, `between_assignList_σ_rank_closure`, `sortBy_perm`, `assignRanks_map_fst`, `setBetween_chain_σInvariant`, `from_assignList_σ_rank_closure`, `set_chain_σInvariant` | — | One depth-step of the `calculatePathRankings` foldl preserves `CalcRankingsInv σ`; the inductive body lemma. | private |
| `calculatePathRankings_σ_cell_inv_facts` | `CalcRankingsInv`, `calculatePathRankings_body_preserves_inv` | — | Cell-level σ-invariance of `calculatePathRankings` output: both `fromRanks` and `betweenRanks` are σ-invariant at every depth. Proved by foldl induction via `calculatePathRankings_body_preserves_inv`. | private |
| `calculatePathRankings_σInvariant_combined` | `calculatePathRankings_size_inv`, `calculatePathRankings_σ_cell_inv_facts`, `calculatePathRankings_fromRanks_size` | — | Combined `RankState.σInvariant σ` for `calculatePathRankings (initializePaths G) vts`: assembles size invariants and cell σ-invariance into the full `σInvariant` structure. | — |
| `calculatePathRankings_fromRanks_inv` | `calculatePathRankings_σInvariant_combined` | — | σ-invariance of `fromRanks` values: `(rs.fromRanks.getD d #[]).getD s.val 0 = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0`. Projection of `σInvariant_combined`. | — |
| `calculatePathRankings_betweenRanks_inv` | `calculatePathRankings_σInvariant_combined` | — | σ-invariance of `betweenRanks` values: `((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0 = ... (σ⁻¹ s) ... (σ⁻¹ e) ...`. Projection of `σInvariant_combined`. | — |
| `calculatePathRankings_σInvariant` | `calculatePathRankings_σInvariant_combined` | — | Direct alias for `calculatePathRankings_σInvariant_combined`; the canonical public name for the full σ-invariance result. | — |
| `calculatePathRankings_RankState_invariant` | `calculatePathRankings_σInvariant`, `RankState.σInvariant.permute_eq_self` | — | `RankState.permute σ` is the identity on `calculatePathRankings (initializePaths G) vts` when σ ∈ Aut G and vts is σ-invariant. | — |
| `calculatePathRankings_Aut_equivariant` | `initializePaths_Aut_equivariant`, `calculatePathRankings_RankState_invariant` | — | **Stage B**: `calculatePathRankings (PathState.permute σ (initializePaths G)) vts = RankState.permute σ (calculatePathRankings (initializePaths G) vts)`. Assembled from Stage A plus σ-invariance. | **Stage B** — requires σ ∈ Aut G |


## PathEquivarianceRelational Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `comparePathSegments_σ_relational` | `comparePathSegments_σ_equivariant` | — | Relational form: `comparePathSegments vts₂ br₂ p₁ p₂ = comparePathSegments vts₁ br₁ (f p₁) (f p₂)` when `f = PathSegment.permute σ` and the two `vts`/`br` pairs are σ-related. | — |
| `insertSorted_map_pointwise_relational` | — | — | Relational pointwise variant of `insertSorted_map`: `cmp₂ (f a) (f b) = cmp₁ a b` for `b` in the input list. | private |
| `sortBy_map_pointwise_relational` | `insertSorted_map_pointwise_relational` | — | Relational pointwise variant of `sortBy_map`: `sortBy cmp₂ (L.map f) = (sortBy cmp₁ L).map f` when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. | — |
| `orderInsensitiveListCmp_map_pointwise_relational` | `sortBy_map_pointwise_relational`, `sortBy_perm` | — | Relational pointwise variant of `orderInsensitiveListCmp_map`: `orderInsensitiveListCmp cmp₂ (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp₁ L₁ L₂` with per-element `cmp₂ (f a) (f b) = cmp₁ a b`. | — |
| `comparePathsBetween_σ_relational` | `comparePathsBetween_σ_equivariant`, `PathsBetween_permute_connectedSubPaths_perm`, `orderInsensitiveListCmp_perm`, `orderInsensitiveListCmp_map_pointwise_relational` | — | Relational form of `comparePathsBetween_σ_equivariant` for two different `vts`/`br` pairs. | — |
| `comparePathsFrom_σ_relational` | `comparePathsFrom_σ_equivariant`, `PathsFrom_permute_pathsToVertex_perm`, `orderInsensitiveListCmp_perm`, `orderInsensitiveListCmp_map_pointwise_relational` | — | Relational form of `comparePathsFrom_σ_equivariant` for two different `vts`/`br` pairs. | — |
| `nodup_keys_unique_value` | — | — | If a `List (Nat × Nat)` has Nodup first components, the value at each key is uniquely determined. | private |
| `nodup_pair_keys_unique_value` | — | — | If a `List ((Nat × Nat) × Nat)` has Nodup key pairs, the value at each key pair is unique. | private |
| `set_chain_σRelated` | `nodup_keys_unique_value`, `array_set_chain_outside_unchanged`, `array_set_chain_at_target_nodup` | — | The `fromRanks` `set!`-chain produces τ-related outputs when the two assignLists are τ-related (each entry in one maps to a τ-shifted entry of equal rank in the other). | — |
| `setBetween_chain_σRelated` | `nodup_pair_keys_unique_value`, `nested_set_chain_at_target_pair_nodup` | — | The `betweenRanks` `setBetween`-chain produces τ-related outputs when the two assignLists are τ-related. | — |
| `mem_pathsAtDepth_under_f` | — | — | Membership in the `f`-mapped `pathsAtDepth` list. | private |
| `pathsAtDepth_map_f_perm` | `mem_pathsAtDepth_under_f` | — | The `f`-mapped `pathsAtDepth` list is a `Perm` of the original when `f` reindexes start vertices bijectively. | private |
| `from_assignList_σ_rank_rel` | `comparePathsFrom_σ_relational`, `sortBy_map_pointwise_relational`, `assignRanks_map_relational`, `pathsAtDepth_map_f_perm`, `assignRanks_rank_eq_of_sorted_perm` | — | Relational σ-rank-closure for the `fromRanks` assignList: entries on the two sides are τ-related with equal ranks. | — |
| `mem_allBetween_under_f` | — | — | Membership in the `f`-mapped `allBetween` list. | private |
| `allBetween_map_f_perm` | `mem_allBetween_under_f` | — | The `f`-mapped `allBetween` list is a `Perm` of the original when `f` reindexes `(start, end)` pairs bijectively. | private |
| `between_assignList_σ_rank_rel` | `comparePathsBetween_σ_relational`, `sortBy_map_pointwise_relational`, `assignRanks_map_relational`, `allBetween_map_f_perm`, `assignRanks_rank_eq_of_sorted_perm` | — | Relational σ-rank-closure for the `betweenRanks` assignList. | — |
| `betweenRankFn_σ_rel_from_cells` | — | — | Cell-level τ-relatedness of a 3D table lifts to a τ-related `betweenRankFn`. | — |
| `CalcRankingsRel` | — | — | Loop invariant for the relational depth foldl: the two accumulators `(currentBetween₁, currentFrom₁)` and `(currentBetween₂, currentFrom₂)` are τ-related at every cell. | — |
| `calculatePathRankings_body_preserves_rel` | `CalcRankingsRel`, `betweenRankFn_σ_rel_from_cells`, `between_assignList_σ_rank_rel`, `set_chain_σRelated`, `setBetween_chain_σRelated`, `from_assignList_σ_rank_rel` | — | One depth-step of the relational `calculatePathRankings` foldl preserves `CalcRankingsRel`. | private |
| `calculatePathRankings_σ_cell_rel_facts` | `CalcRankingsRel`, `calculatePathRankings_body_preserves_rel` | — | Cell-level τ-relatedness of `calculatePathRankings` outputs on two τ-related inputs; proved by foldl induction. | private |
| `calculatePathRankings_σ_equivariant_relational` | `calculatePathRankings_σ_cell_rel_facts`, `calculatePathRankings_size_inv` | — | **Stage B-rel**: `calculatePathRankings` outputs on τ-related inputs are τ-related at every cell. Requires σ ∈ Aut G. | — |

## PathEquivarianceGeneral Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `pathsOfLength_two_states_at_σ_slot` | `initializePaths_pathsOfLength_size`, `permNat_of_lt` | — | For two states related by Stage A (`state₂ = PathState.permute σ state₁`), reading a slot of `state₂` equals reading the σ-shifted slot of `state₁`. | private |
| `pathsAtDepth_two_states_perm` | `pathsOfLength_two_states_at_σ_slot` | — | The `pathsAtDepth` of state₂ is a `Perm` of the σ-mapped `pathsAtDepth` of state₁. | private |
| `mem_pathsAtDepth_two_states_under_f` | `pathsAtDepth_two_states_perm` | — | Membership characterization for the `f`-mapped `pathsAtDepth` across two Stage-A-related states. | private |
| `allBetween_two_states_perm` | `pathsAtDepth_two_states_perm` | — | The `allBetween` list of state₂ is a `Perm` of the σ-mapped `allBetween` of state₁. | private |
| `mem_allBetween_two_states_under_f` | `allBetween_two_states_perm` | — | Membership characterization for the `f`-mapped `allBetween` across two Stage-A-related states. | private |
| `from_assignList_σ_rank_general` | `comparePathsFrom_σ_relational`, `sortBy_map_pointwise_relational`, `assignRanks_map_relational`, `pathsAtDepth_two_states_perm`, `assignRanks_rank_eq_of_sorted_perm` | — | General σ-rank-closure for the `fromRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | — |
| `between_assignList_σ_rank_general` | `comparePathsBetween_σ_relational`, `sortBy_map_pointwise_relational`, `assignRanks_map_relational`, `allBetween_two_states_perm`, `assignRanks_rank_eq_of_sorted_perm` | — | General σ-rank-closure for the `betweenRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | — |
| `calculatePathRankings_body_preserves_general` | `betweenRankFn_σ_rel_from_cells`, `between_assignList_σ_rank_general`, `set_chain_σRelated`, `setBetween_chain_σRelated`, `from_assignList_σ_rank_general` | — | One depth-step of the general foldl preserves the relational invariant across two Stage-A-related states. | private |
| `calculatePathRankings_σ_cell_general_facts` | `calculatePathRankings_body_preserves_general` | — | Cell-level τ-relatedness of `calculatePathRankings` across two Stage-A-related states; proved by foldl induction. | private |
| `calculatePathRankings_σ_equivariant_general` | `initializePaths_Aut_equivariant`, `calculatePathRankings_σ_cell_general_facts`, `calculatePathRankings_size_inv` | — | **Stage B-rel-general**: `calculatePathRankings` on `initializePaths (G.permute σ)` is σ-related to `calculatePathRankings` on `initializePaths G`, for any σ (no Aut G hypothesis). | — |

## ConvergeLoop Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `convergeOnce_fold_outside_unchanged` | — | — | The `convergeOnce` fold body leaves positions `j ∉ l` unchanged through the full `l.foldl`. | private |
| `convergeOnce_fold_writeback` | `convergeOnce_fold_outside_unchanged` | — | After the fold processes position `j`, slot `j` holds `rs.getFrom (vc-1) j`. | private |
| `convergeOnce_writeback` | `convergeOnce_fold_writeback` | — | After `convergeOnce`, every in-bounds position `i` holds `calculatePathRankings.getFrom (n-1) i`. | — |
| `RankState.getFrom_permute` | — | — | `getFrom` on `RankState.permute σ rs` reads from the `σ⁻¹`-shifted position in the original `rs`. | — |
| `calculatePathRankings_getFrom_invariant` | `calculatePathRankings_RankState_invariant`, `calculatePathRankings_fromRanks_size`, `RankState.getFrom_permute`, `permNat_of_lt` | — | σ-invariance of `getFrom (n-1)`: positions `v` and `σ v` return the same value when σ ∈ Aut(G) and `vts` is σ-invariant. | — |
| `convergeOnce_Aut_invariant` | `convergeOnce_writeback`, `calculatePathRankings_getFrom_invariant` | — | One `convergeOnce` step preserves Aut(G)-invariance: `output[σ v] = output[v]` for σ ∈ Aut(G). | — |
| `convergeOnce_size_preserving` | — | — | `convergeOnce` preserves the vertex type array size. | — |
| `convergeLoop_Aut_invariant` | `convergeOnce_Aut_invariant`, `convergeOnce_size_preserving` | — | The full convergence loop preserves Aut(G)-invariance for any fuel; proved by induction on fuel. | — |
| `convergeLoop_zeros_Aut_invariant` | `convergeLoop_Aut_invariant` | — | Corollary: starting from the all-zeros array, the convergence loop preserves Aut(G)-invariance. | — |
| `orderVertices_Aut_equivariant` | `initializePaths_Aut_equivariant` | — | Stage C: `orderVertices (PathState.permute σ (initializePaths G)) vts = orderVertices (initializePaths G) vts` for σ ∈ Aut(G). | **Stage C** |
| `labelEdges_Aut_equivariant` | — | — | Stage D: `labelEdgesAccordingToRankings vts (G.permute σ) = labelEdgesAccordingToRankings vts G` for σ ∈ Aut(G); follows immediately from `G.permute σ = G`. | **Stage D** |


## ConvergeLoopRelational Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `convergeOnce_fold_unchanged_when_not_flag` | — | — | If `convergeOnce`'s fold body starts with `flag = false` and reaches a `false` flag, the array is unchanged throughout. | private |
| `convergeOnce_unchanged_when_not_flag` | `convergeOnce_fold_unchanged_when_not_flag` | — | If `convergeOnce`'s flag output is `false`, the output array equals the input array (fixed point). | — |
| `convergeLoop_unchanged_fixedpoint` | `convergeOnce_unchanged_when_not_flag` | — | If `convergeOnce`'s flag is `false`, then `convergeLoop` is the identity at every fuel level. | — |
| `convergeLoop_succ_eq_loop_of_once` | `convergeLoop_unchanged_fixedpoint`, `convergeOnce_unchanged_when_not_flag` | — | `convergeLoop state vts (k+1) = convergeLoop state (convergeOnce state vts).1 k` regardless of the flag. | — |
| `calculatePathRankings_getFrom_VtsInvariant_eq` | `calculatePathRankings_σ_equivariant_relational` | — | Relational `getFrom (n-1)` analogue: for τ-related `vts₁`/`vts₂`, the `getFrom` values are τ-shifted. | — |
| `convergeOnce_VtsInvariant_eq` | `convergeOnce_writeback`, `calculatePathRankings_getFrom_VtsInvariant_eq` | — | One `convergeOnce` step on τ-related arrays produces τ-related outputs. Relational analogue of `convergeOnce_Aut_invariant`. | — |
| `convergeLoop_VtsInvariant_eq` | `convergeLoop_succ_eq_loop_of_once`, `convergeOnce_VtsInvariant_eq`, `convergeOnce_size_preserving` | — | The full `convergeLoop` preserves τ-relatedness for any fuel. Relational analogue of `convergeLoop_Aut_invariant`. | — |

## ConvergeLoopGeneral Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `calculatePathRankings_getFrom_σ_equivariant_general` | `calculatePathRankings_σ_equivariant_general` | — | Relational `getFrom (n-1)` for general σ: the two computations run on `initializePaths G` vs `initializePaths (G.permute σ)`. | private |
| `convergeOnce_σ_equivariant_general` | `convergeOnce_writeback`, `calculatePathRankings_getFrom_σ_equivariant_general` | — | **P6.B**: `convergeOnce` on `(initializePaths (G.permute σ), vts₂)` is σ-related to `convergeOnce` on `(initializePaths G, vts₁)` for any σ. | — |
| `convergeLoop_σ_equivariant_general` | `convergeLoop_succ_eq_loop_of_once`, `convergeOnce_σ_equivariant_general`, `convergeOnce_size_preserving` | — | **P6.B loop**: The full `convergeLoop` is σ-equivariant across the two general states for any fuel. | — |

## StageDRelational Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `TieFree` | — | — | Predicate: all `n` vertices have distinct types in `rks` (no ties). | — |
| `τRelatedRks` | — | — | Predicate: `rks₂.getD v 0 = rks₁.getD (τ⁻¹ v) 0` for all `v` (τ-shifted ranks). | private |
| `pairCmp` | — | — | Lex comparator on `(VertexType × Nat)`: compare first by type, then by vertex index. | private |
| `pairCmp_refl` | — | — | `pairCmp a a = .eq`. | private |
| `pairCmp_eval_ne_fst` | — | — | `pairCmp a b` when `a.1 ≠ b.1` (reduces to `Nat.compare a.1 b.1`). | private |
| `pairCmp_eval_eq_fst` | — | — | `pairCmp a b` when `a.1 = b.1` (reduces to `Nat.compare a.2 b.2`). | private |
| `pairCmp_le_iff` | — | — | `pairCmp a b ≠ .gt ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)`. | private |
| `pairCmp_gt_iff` | — | — | `pairCmp a b = .gt ↔ b.1 < a.1 ∨ (a.1 = b.1 ∧ b.2 < a.2)`. | private |
| `pairCmp_antisym₁` | — | — | Antisymmetry `.lt → .gt` for `pairCmp`. | private |
| `pairCmp_antisym₂` | — | — | Antisymmetry `.gt → .lt` for `pairCmp`. | private |
| `pairCmp_trans` | — | — | Transitivity `≠ .gt` for `pairCmp`. | private |
| `pairCmp_strict` | — | — | `pairCmp a b ≠ .eq` when `a ≠ b`. | private |
| `pairsOf` | — | — | Convert `(rks : Array VertexType)` to a list of `(rks[i], i)` pairs. | private |
| `pairsOf_length` | — | — | `(pairsOf n rks).length = n`. | private |
| `pairsOf_seconds` | — | — | The second components of `pairsOf n rks` are `[0, 1, ..., n-1]`. | private |
| `sortedPairs_length` | — | — | The `pairCmp`-sorted pairs list has length `n`. | private |
| `sortedPairs_seconds_perm` | `pairsOf_seconds`, `sortBy_perm` | — | Second components of the sorted pairs are a Perm of `[0, 1, ..., n-1]`. | private |
| `sortedPairs_seconds_nodup` | `sortedPairs_seconds_perm` | — | Second components of the sorted pairs are Nodup. | private |
| `L_pairs_nodup_aux` | — | — | Nodup of the `(type, index)` pairs list when indices are distinct. | private |
| `computeDenseRanks_eq_zipIdx_setChain` | `pairsOf_seconds`, `sortedPairs_seconds_nodup`, `array_set_chain_at_target_nodup` | — | `computeDenseRanks` output equals the result of a `set!`-chain indexed by the sorted `(type, index)` pairs. | private |
| `computeDenseRanks_getD_at_pos` | `computeDenseRanks_eq_zipIdx_setChain` | — | `(computeDenseRanks n rks).getD v 0` equals the dense rank of vertex `v`. | private |
| `computeDenseRanks_inj` | `computeDenseRanks_getD_at_pos` | — | `computeDenseRanks` is injective on vertex indices when tie-free. | private |
| `computeDenseRanks_perm_when_tieFree` | `computeDenseRanks_getD_at_pos`, `computeDenseRanks_inj` | — | Under `TieFree rks n`, `computeDenseRanks` output is a permutation of `[0, 1, ..., n-1]`. | — |
| `liftToNat` | — | — | Lift `τ : Equiv.Perm (Fin n)` to a total `Nat → Nat` function (identity outside `[0, n)`). | private |
| `pairLift` | — | — | Lift `τ` to act on `(VertexType × Nat)` by shifting the index component. | private |
| `liftToNat_in_range` | — | — | `liftToNat τ j = (τ ⟨j, _⟩).val` when `j < n`. | private |
| `pairsOf_τ_perm` | `liftToNat_in_range` | — | `pairsOf n (τ-shifted rks)` is a Perm of `pairLift τ` applied to `pairsOf n rks`. | private |
| `pairCmp_resp_lift_under_tieFree` | `pairCmp_eval_ne_fst`, `pairCmp_eval_eq_fst` | — | `pairCmp` respects `pairLift τ` on tie-free pairs: `pairCmp (pairLift τ a) (pairLift τ b) = pairCmp a b` when `rks` is tie-free. | private |
| `computeDenseRanks_τ_shift_distinct` | `pairsOf_τ_perm`, `pairCmp_resp_lift_under_tieFree`, `sortBy_eq_of_perm_strict`, `computeDenseRanks_getD_at_pos`, `computeDenseRanks_inj` | — | Under `TieFree` and τ-related ranks, `computeDenseRanks` on `rks₂` is the τ-shifted `computeDenseRanks` on `rks₁`. | — |
| `labelEdges_VtsInvariant_eq_distinct` | `computeDenseRanks_perm_when_tieFree`, `labelEdges_fold_strong`, `labelEdges_terminal_rankMap_identity` | — | When `rks` is tie-free, `labelEdgesAccordingToRankings rks G` is invariant under `VtsInvariant` (Aut G acts trivially). | — |
| `labelEdges_two_graphs_σ_related` | `computeDenseRanks_τ_shift_distinct`, `labelEdges_fold_strong`, `labelEdges_terminal_rankMap_identity` | — | Under τ-related tie-free ranks, `labelEdgesAccordingToRankings rks₂ G₂ = labelEdgesAccordingToRankings rks₁ G₁`. Stage D-rel. | — |

## BreakTieRelational Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `shiftAbove_VtsInvariant_eq` | — | — | `shiftAbove t₀ vts₂` at slot `w` equals `shiftAbove t₀ vts₁` at slot `τ⁻¹ w` when `vts₁`/`vts₂` are τ-related. | — |
| `shiftAbove_VtsInvariant_size_eq` | — | — | τ-related `vts₁`/`vts₂` have the same size after `shiftAbove`. | — |
| `breakTieAt_τ_related` | `shiftAbove_VtsInvariant_eq`, `shiftAbove_VtsInvariant_size_eq` | — | `breakTieAt vts₂ t₀ (τ keep)` at slot `w` equals `breakTieAt vts₁ t₀ keep` at slot `τ⁻¹ w` when inputs are τ-related. | — |
| `breakTieAt_size_eq` | — | — | τ-related `vts₁`/`vts₂` have the same size after `breakTieAt`. | — |

## Invariants Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `IsPrefixTyping` | — | — | Predicate: `vts` values form a contiguous prefix `{0, 1, ..., k}` for some `k`; i.e. every value `< vts.max` appears. | — |
| `IsPrefixTyping.replicate_zero` | — | — | The all-zeros array satisfies `IsPrefixTyping`. | — |
| `convergeLoop_size_preserving` | `convergeOnce_size_preserving` | — | `convergeLoop` preserves the vertex type array size. | — |
| `initializePaths_pathsAtDepth_startVertices_eq_range` | — | — | Start vertices of depth-`d` slice of `initializePaths G` are exactly `List.range n`. | private |
| `initializePaths_pathsAtDepth_startVertices_nodup` | `initializePaths_pathsAtDepth_startVertices_eq_range` | — | Start vertices of depth-`d` slice are Nodup. | private |
| `outer_fold_fromAcc_other_target_unchanged` | — | — | The outer `fromAcc` foldl leaves depth-slots other than the target depth unchanged. | private |
| `list_pair_max_exists` | — | — | A non-empty list of `(α × Nat)` contains an element with maximum second component. | private |
| `chain_image_dense_of_perm_and_density` | — | — | If the rank image is dense and the assignList is a Perm-related variant, the image remains dense. | private |
| `chain_image_dense_for_assignRanks_sortBy` | `assignRanks_image_dense`, `sortBy_perm` | — | The rank image of `assignRanks cmp (sortBy cmp L)` is dense (downward closed). | private |
| `chain_value_at_vertex_for_assignRanks_sortBy` | `chain_image_dense_for_assignRanks_sortBy` | — | For each vertex `v`, some entry in the `assignRanks (sortBy …)` output has first component `v`. | private |
| `getFrom_image_isPrefix_for_initializePaths` | `chain_image_dense_for_assignRanks_sortBy`, `assignRanks_rank_lt_length` | — | The image of `getFrom (n-1)` on `calculatePathRankings (initializePaths G) vts` is a prefix `{0, ..., k}`. | — |
| `convergeLoop_preserves_prefix` | `getFrom_image_isPrefix_for_initializePaths`, `convergeOnce_writeback` | — | `convergeLoop` preserves `IsPrefixTyping` from fuel 0 onward. | — |
| `breakTie_targetPos_is_min_tied` | — | — | The tiebreak target position `breakTieAt`'s `keep` argument is the minimum vertex in the tied type class. | — |
| `UniquelyHeldBelow` | — | — | Predicate: every value `< q` in `vts` is held by exactly one vertex. | — |
| `comparePathsFrom_eq_compare_of_start_types_ne` | — | — | When two start types differ, `comparePathsFrom` reduces to comparing start types only. | private |
| `_comparePathsFrom_total_preorder_legacy_unused` | — | — | Legacy total-preorder proof for `comparePathsFrom`; superseded by `comparePathsFrom_total_preorder`. | private |
| `sortBy_pathsAtTop_length_eq` | — | — | `sortBy comparePathsFrom (pathsAtDepth)` preserves length `n`. | private |
| `sortBy_first_q_positions_have_start_types` | — | — | The first `q` positions of the sorted `pathsAtDepth` list have start types `0, 1, ..., q-1`. | private |
| `fromRanks_at_n_minus_1_eq_chain_for_initializePaths` | `chain_value_at_vertex_for_assignRanks_sortBy` | — | The `fromRanks` at depth `n-1` in `calculatePathRankings (initializePaths G) vts` equals the rank of vertex `v` in the sorted list. | private |
| `convergeOnce_preserves_lower_uniqueness` | `convergeOnce_writeback`, `fromRanks_at_n_minus_1_eq_chain_for_initializePaths` | — | One `convergeOnce` step preserves `UniquelyHeldBelow q` when the current values below `q` are already distinct. | private |
| `convergeLoop_preserves_lower_uniqueness` | `convergeOnce_preserves_lower_uniqueness`, `convergeOnce_size_preserving` | — | `convergeLoop` preserves `UniquelyHeldBelow q` for any fuel. | — |
| `prefix_unique_below_implies_value_held` | — | — | If `IsPrefixTyping vts` and `UniquelyHeldBelow q vts`, every value `< q` is held by exactly one vertex. | private |
| `exists_two_distinct_q_in_T` | — | — | If `breakTieCount t₀ vts ≥ 2`, there exist two distinct vertices with type `t₀`. | private |
| `breakTie_step_preserves_uniqueness` | `breakTie_getD_at_min`, `breakTie_getD_at_other`, `breakTie_getD_target` | — | One `breakTie` step preserves `UniquelyHeldBelow` for the next level. | — |
| `orderVertices_prefix_invariant_strong` | `convergeLoop_preserves_prefix`, `convergeLoop_preserves_lower_uniqueness`, `breakTie_step_preserves_uniqueness` | — | Strong inductive: after `runFrom s vts G`, `UniquelyHeldBelow s` holds. | private |
| `orderVertices_prefix_invariant` | `orderVertices_prefix_invariant_strong` | — | `orderVertices (initializePaths G) zeros` satisfies `IsPrefixTyping`. | — |
| `orderVertices_n_distinct_ranks` | `orderVertices_prefix_invariant`, `convergeLoop_preserves_lower_uniqueness` | — | `orderVertices` produces exactly `n` distinct values `0, 1, ..., n-1`. | — |
| `getArrayRank_size` | — | — | `getArrayRank arr` preserves array size. | — |
| `getArrayRank_zeros_eq_zeros` | — | — | `getArrayRank (Array.replicate n 0) = Array.replicate n 0`. | — |
| `orderVertices_size_eq` | — | — | `orderVertices (initializePaths G) vts` preserves array size. | — |

## RunFromRelational Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `runFrom_VtsInvariant_eq` | `convergeLoop_VtsInvariant_eq`, `breakTieAt_τ_related`, `breakTieAt_size_eq` | — | Early form: for τ-related `vts₁`/`vts₂`, `runFrom s vts₂ G` is τ-related to `runFrom s vts₁ G`. | — |
| `convergeLoop_step_τ_preserved` | `convergeLoop_VtsInvariant_eq` | — | One `convergeLoop ∘ breakTieAt` step preserves τ-relatedness of the arrays. | — |
| `IsPrefixTyping_τ_transfer` | — | — | τ-relatedness transfers `IsPrefixTyping`: if `vts₁` is a prefix typing and `vts₂` is τ-related, so is `vts₂`. | — |
| `UniquelyHeldBelow_τ_transfer` | — | — | τ-relatedness transfers `UniquelyHeldBelow q`: if `vts₁` holds it and `vts₂` is τ-related, so does `vts₂`. | — |
| `runFrom_at_n` | — | — | `runFrom n vts G = vts` (base case: no vertices left to process). | — |
| `runFrom_succ` | — | — | Unfolding: `runFrom s vts G = runFrom (s+1) (convergeLoop ∘ breakTieAt s vts) G`. | — |
| `UniquelyHeldBelow_n_implies_TieFree` | — | — | `UniquelyHeldBelow n vts` implies `TieFree vts n`. | — |
| `Array.toList_eq_finRange_map` | — | — | `arr.toList = (List.finRange n).map (fun i => arr[i.val])` when `arr.size = n`. | private |
| `breakTieCount_τ_invariant` | — | — | `breakTieCount t₀ vts₂ = breakTieCount t₀ vts₁` when `vts₁`/`vts₂` are τ-related. | — |
| `typeClass_τ_image_eq` | — | — | `typeClass vts₂ t₀ = τ '' (typeClass vts₁ t₀)` when `vts₂` is τ-related to `vts₁`. | — |
| `breakTie_min_witness` | `breakTieCount_τ_invariant`, `typeClass_τ_image_eq` | — | The minimum vertex in `typeClass vts₂ t₀` is `τ` applied to the minimum in `typeClass vts₁ t₀`. | — |
| `breakTie_min_witness_in_typeClass` | `breakTie_min_witness` | — | The minimum witness vertex lies in `typeClass`. | — |
| `OrbitCompleteAfterConv` | — | — | Orbit-completeness invariant: vertices with equal converged types lie in the same `TypedAut`-orbit. | — |
| `runFrom_VtsInvariant_eq_strong` | `convergeLoop_step_τ_preserved`, `IsPrefixTyping_τ_transfer`, `UniquelyHeldBelow_τ_transfer`, `breakTie_min_witness`, `OrbitCompleteAfterConv`, `UniquelyHeldBelow_n_implies_TieFree`, `labelEdges_VtsInvariant_eq_distinct` | — | Strong relational theorem: `runFrom s vts₂ G = runFrom s vts₁ G` (not just τ-related, equal) given `OrbitCompleteAfterConv` and `UniquelyHeldBelow s`. | — |
| `runFrom_VtsInvariant_eq` | `runFrom_VtsInvariant_eq_strong` | — | Corollary of the strong form: `runFrom 0 zeros G = runFrom 0 (τ-shifted zeros) G`. | — |
| `tiebreak_choice_independent` | `runFrom_VtsInvariant_eq` | — | The canonical `orderVertices` output is independent of which tied vertex is chosen for tiebreaking; proved from `runFrom_VtsInvariant_eq`. | — |

## OrderVerticesGeneral Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `OrbitCompleteAfterConv_general` | — | — | Two-graphs variant of `OrbitCompleteAfterConv`: orbit-completeness for `convergeLoop (initializePaths (G.permute σ)) mid n`. | — |
| `convergeLoop_step_σ_chain_preserved_general` | `convergeLoop_VtsInvariant_eq`, `convergeLoop_σ_equivariant_general` | — | Two-graphs convergeLoop step preservation: chains through an intermediate τ-shifted typing to decompose `σ_chain = σ * τ` (τ ∈ Aut G). | private |
| `runFrom_VtsInvariant_eq_strong_general` | `convergeLoop_step_σ_chain_preserved_general`, `IsPrefixTyping_τ_transfer`, `UniquelyHeldBelow_τ_transfer`, `OrbitCompleteAfterConv_general`, `UniquelyHeldBelow_n_implies_TieFree`, `labelEdges_two_graphs_σ_related` | — | **P6.C**: `runFrom s vts₁ G = runFrom s vts₂ (G.permute σ)` given `OrbitCompleteAfterConv_general` and σ-relatedness of the arrays. | — |

## MainRelationalNotes Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `zeros_σ_invariant` | — | — | The all-zeros array is σ-invariant for any σ: `(Array.replicate n 0).getD (σ v) 0 = (Array.replicate n 0).getD v 0 = 0`. | — |

## Main Module

| Name | Uses | Used By | Description | Notes |
|------|------|---------|-------------|-------|
| `run_swap_invariant_fwd` | `permute_of_Isomorphic`, `initializePaths_Aut_equivariant`, `convergeLoop_zeros_Aut_invariant`, `labelEdges_Aut_equivariant` | — | Forward direction kernel: for σ ∈ Aut G, `run zeros G = run zeros (G.permute σ)`. Used to bootstrap the (⟹) direction. | private |
| `run_isomorphic_eq_new` | `permute_of_Isomorphic`, `runFrom_VtsInvariant_eq_strong_general`, `OrbitCompleteAfterConv_general`, `zeros_σ_invariant` | — | **(⟹) direction**: `G ≃ H → run zeros G = run zeros H`. Assembled from Stage A + Stage B-rel-general + P6.B/C + Stage D-rel. | — |
| `run_canonical_correctness` | `run_isomorphic_eq_new` | — | **Main theorem**: `G ≃ H ↔ run zeros G = run zeros H`. Combines both directions. | — |

---

