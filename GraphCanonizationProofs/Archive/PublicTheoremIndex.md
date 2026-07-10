# Archived Public Theorem Index — GraphCanonizationProofs

Index of public Lean theorems, lemmas, and definitions in the archived (`Archive/...`) portion of the GraphCanonizationProofs project, grouped by source file path. Active counterparts live in `../PublicTheoremIndex.md`.

## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line.
- **Description**: A short description of what the theorem proves.
- **Notes**: `@[simp]` / `@[ext]` attributes, `private`, instances, or other special properties.

## Archive/V4/FullCorrectness/Basic.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ext` | 18-22 | — | — |
| `AdjMatrix.ext` | 18-22 | Two adjacency matrices are equal iff their adjacency functions agree pointwise. | — |

## Archive/V4/FullCorrectness/Permutation.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AdjMatrix.permute` | 21-28 | Relabel vertices of G by permutation σ. Uses σ.symm for left-action semantics. | Definition |
| `AdjMatrix.permute_adj` | 30-32 | Simplification rule: `(G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j)`. | — |
| `AdjMatrix.permute_one` | 34-39 | Permuting by the identity does nothing: `G.permute 1 = G`. | — |
| `AdjMatrix.permute_mul` | 41-47 | Permutation action composes as left action: `G.permute (σ * τ) = (G.permute τ).permute σ`. | — |
| `AdjMatrix.permute_permute_symm` | 49-53 | Permuting by inverse undoes original: `(G.permute σ).permute σ⁻¹ = G`. | — |
| `AdjMatrix.permute_symm_permute` | 55-58 | Inverse permute then permute: `(G.permute σ⁻¹).permute σ = G`. | — |
| `swapVertexLabels_eq_permute` | 62-72 | Bridge between concrete `swapVertexLabels` and abstract `permute` action. | — |

## Archive/V4/FullCorrectness/Automorphism.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AdjMatrix.Aut` | 22-41 | The automorphism group of G: permutations σ with `G.permute σ = G`. Instances: `DecidableEq`, `Fintype`. | Definition |
| `mem_Aut_iff` | 43-44 | Characterization of `Aut` via permute: `σ ∈ G.Aut ↔ G.permute σ = G`. | — |
| `mem_Aut_iff_adj` | 46-56 | Characterization via adjacency: `σ ∈ G.Aut ↔ ∀ i j, G.adj (σ.symm i) (σ.symm j) = G.adj i j`. | — |
| `AdjMatrix.orbit` | 60-62 | The `Aut(G)`-orbit of vertex v: all vertices reachable from v by an automorphism. | Definition |
| `mem_orbit_iff` | 64-65 | Characterization: `w ∈ G.orbit v ↔ ∃ σ ∈ G.Aut, σ v = w`. | — |
| `AdjMatrix.mem_orbit_self` | 69-70 | Reflexivity: `v ∈ G.orbit v`. | — |
| `AdjMatrix.mem_orbit_symm` | 72-77 | Symmetry: `w ∈ G.orbit v → v ∈ G.orbit w`. | — |
| `AdjMatrix.mem_orbit_trans` | 79-84 | Transitivity: `v ∈ G.orbit u → w ∈ G.orbit v → w ∈ G.orbit u`. | — |
| `AdjMatrix.orbitSetoid` | 86-93 | Same-orbit as equivalence relation; classes are the `Aut(G)`-orbits. | Definition |
| `AdjMatrix.orbit_stable_under_Aut` | 97-101 | If `σ ∈ Aut G`, then `σ` maps each orbit to itself. | — |
| `AdjMatrix.exists_Aut_of_mem_orbit` | 103-104 | Extract automorphism from orbit membership (identity). | — |
| `DecidableEq (AdjMatrix n)` | — | Instance: adjacency matrix equality is decidable. | Instance |
| `Decidable (σ ∈ G.Aut)` | — | Instance: membership in automorphism group is decidable. | Instance |
| `Fintype G.Aut` | — | Instance: `Aut G` is finite as a subgroup of `Equiv.Perm (Fin n)`. | Instance |

## Archive/V4/FullCorrectness/Isomorphic.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `permute_of_Isomorphic` | 19-35 | Extract a concrete permutation from an `Isomorphic` witness. | — |
| `Isomorphic_permute` | 39-55 | Every permutation σ realizes isomorphism: `G ≃ G.permute σ`. Proved by swap induction. | — |
| `Isomorphic_of_permute` | 57-61 | If `H = G.permute σ`, then `G ≃ H`. | — |
| `Isomorphic_iff_exists_permute` | 65-68 | Bridge: inductive `Isomorphic ↔ ∃ σ, H = G.permute σ`. | — |

## Archive/V4/FullCorrectness/Equivariance/Actions.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `permNat` | 20-21 | Re-index natural numbers by permutation (identity outside `[0, n)`). | Definition |
| `permNat_one` | 23-24 | Permuting by identity is the identity on naturals. | `@[simp]` |
| `permNat_lt` | 26-28 | Permuting a number `< n` stays `< n`. | — |
| `permNat_of_lt` | 30-32 | Explicit formula for `permNat σ i` when `i < n`. | — |
| `permNat_of_ge` | 34-36 | Permuting a number `≥ n` is unchanged. | — |
| `permNat_inv_perm` | 38-42 | Applying σ then σ⁻¹ is identity on in-range naturals. | `@[simp]` |
| `permNat_perm_inv` | 44-48 | Applying σ⁻¹ then σ is identity on in-range naturals. | `@[simp]` |
| `permNat_fin` | 50-52 | `permNat` on a `Fin n` value equals the permuted `Fin` value. | `@[simp]` |
| `PathSegment.permute` | 62-65 | Relabel vertex indices inside a `PathSegment n` by permutation σ. | Definition |
| `PathsBetween.permute` | 67-87 | Relabel vertex indices inside a `PathsBetween n`, respecting depth cases. | Definition |
| `PathsFrom.permute` | 89-102 | Relabel vertex indices inside `PathsFrom n`, reordering the `pathsToVertex` list. | Definition |
| `PathState.permute` | 104-116 | Relabel a full `PathState n` by σ using σ.symm semantics. | Definition |
| `RankState.permute` | 118-132 | Relabel a `RankState` by σ: slot `(d, σ⁻¹ s, σ⁻¹ e)` maps to output slot `(d, s, e)`. | Definition |
| `initializePaths_pathsOfLength_size` | 136-139 | The `pathsOfLength` array of `initializePaths G` has size `n`. | `@[simp]` |
| `PathState_permute_pathsOfLength_size` | 141-146 | Permuting a `PathState` preserves the `pathsOfLength.size`. | `@[simp]` |
| `initializePaths_pathsOfLength_get_size` | 148-154 | Depth-`d` slice of `initializePaths G` is a length-`n` array. | — |

## Archive/V4/FullCorrectness/Equivariance/StageA.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `initializePaths_Aut_equivariant` | 204-287 | Main Stage A theorem: `initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)` for any σ. | — |

## Archive/V4/FullCorrectness/Equivariance/RankStateInvariants.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `calculatePathRankings_fromRanks_size` | 22-82 | The `fromRanks` table of `calculatePathRankings` output has size `vc`. | — |
| `setBetween_getD_getD_size` | 125-144 | `setBetween` preserves the size of every (depth, start)-cell. | — |
| `array_set_chain_outside_unchanged` | 164-180 | Foldl `set!`-chain leaves untouched positions unchanged. | — |
| `array_set_chain_at_target_nodup` | 182-223 | Foldl `set!`-chain gives target value at target index when indices are `Nodup`. | — |
| `inner_fold_slice_at_depth` | 225-254 | Strip the outer `set! depth` wrapper: the result's `depth`-slice equals folding on the initial slice directly. | — |
| `inner_fold_other_depth_unchanged` | 256-275 | Inner fold only writes to depth-slot, other depths are preserved. | — |
| `setBetween_fold_slice_at_depth` | 277-310 | `setBetween` fold depth-slice equals folding the depth-slice directly. | — |
| `setBetween_fold_other_depth_unchanged` | 312-332 | `setBetween` fold only writes to outer depth, other depths preserved. | — |
| `RankState.σInvariant` | 344-359 | Predicate on `rs : RankState`: size-shape and value σ-invariance conditions sufficient to conclude `RankState.permute σ rs = rs`. | Structure |
| `RankState.σInvariant.permute_eq_self` | 361-409 | Extensionality: σ-invariance implies `RankState.permute σ rs = rs`. | — |
| `calculatePathRankings_size_inv` | 411-544 | Size facts on `calculatePathRankings` output: `betweenRanks` is `vc×vc×vc`, `fromRanks` is `vc×vc`. | — |

## Archive/V4/FullCorrectness/Equivariance/ComparisonSort.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `sortBy_map` | 62-73 | `sortBy cmp (L.map f) = (sortBy cmp L).map f` when `f` preserves `cmp`; instantiated with `PathSegment.permute σ` for σ-equivariance. | — |
| `perm_insertSorted` | 75-85 | `insertSorted cmp a L` is a `List.Perm` of `a :: L`. | — |
| `sortBy_perm` | 87-94 | `sortBy cmp L` is a `List.Perm` of `L`. | — |
| `sortedPerm_class_eq` | 131-332 | KEY LEMMA: for sorted lists `M`, `M'` with `M.Perm M'`, the elements at position `i` of `M` and `M'` lie in the same `cmp`-equivalence class. Proved by a counting argument on sorted prefix/suffix structure. | — |
| `sortBy_pairwise` | 388-401 | `sortBy cmp L` is `Pairwise (cmp · · ≠ .gt)`, i.e. the output list is sorted under `cmp`. | — |
| `foldl_pointwise_eq` | 403-423 | If two equal-length lists agree element-wise under `f` at every accumulator value, their `List.foldl f` results are equal. | — |
| `orderInsensitiveListCmp_perm` | 425-504 | `orderInsensitiveListCmp cmp L₁ L₂` is invariant under permutations of `L₁` and `L₂`, given a compatible total preorder. | — |
| `assignRanks_length` | 571-575 | `(assignRanks cmp L).length = L.length`. | — |
| `assignRanks_map_fst` | 596-600 | `(assignRanks cmp L).map (·.1) = L`: first components reproduce the input list in order. | — |
| `assignRanks_getElem_fst` | 602-616 | Element-wise: `((assignRanks cmp L)[i]).1 = L[i]`. | — |
| `assignRanks_map_relational` | 690-709 | Relational form: `assignRanks cmp₂ (L.map f) = (assignRanks cmp₁ L).map (fun e => (f e.1, e.2))` when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. Used by Stage B-rel. | — |
| `assignRanks_image_dense` | 900-915 | Rank set is downward-closed: for any entry in `assignRanks cmp L`, every `k ≤ entry.2` has a witness in the output. | — |
| `assignRanks_rank_lt_length` | 917-935 | Every rank in `assignRanks cmp L` is `< L.length`; bounds vertex type values produced by `convergeOnce`. | — |
| `assignRanks_rank_le_pos` | 1098-1129 | Rank at position `k` in `assignRanks cmp L` is `≤ k`. | — |
| `assignRanks_pairwise_rank_le` | 1207-1213 | Ranks in `assignRanks cmp L` are pairwise non-decreasing along the list. | — |
| `assignRanks_rank_monotone` | 1215-1227 | Rank at position `i` is `≤` rank at position `j` for `i ≤ j < L.length`. | — |
| `assignRanks_rank_eq_pos_when_distinct` | 1438-1446 | Rank at position `k` equals `k` when all consecutive pairs in `L` have `cmp ≠ .eq`. | — |
| `assignRanks_rank_eq_of_prefix` | 1448-1485 | Rank at position `k < A.length` in `assignRanks cmp (A ++ B)` equals rank at `k` in `assignRanks cmp A`. | — |
| `assignRanks_rank_eq_pos_when_distinct_prefix` | 1487-1520 | Rank equals position for all `k < q` when consecutive elements in the first `q` entries have `cmp ≠ .eq`. | — |
| `assignRanks_rank_eq_at_succ_when_cmp_eq` | 1534-1638 | Ranks at positions `i` and `i+1` are equal when `cmp L[i] L[i+1] = .eq`. | — |
| `assignRanks_rank_eq_within_eq_class` | 1647-1776 | For a sorted list under a total preorder, if `cmp L[i] L[j] = .eq` and `i ≤ j`, the assigned ranks at `i` and `j` agree. | — |
| `assignRanks_rank_succ_when_cmp_neq_eq` | 1785-1884 | Rank at `i+1` equals rank at `i` plus 1 when `cmp L[i] L[i+1] ≠ .eq`. | — |
| `assignRanks_rank_eq_of_sorted_perm` | 1895-1987 | For sorted `X.Perm Y` (under a total preorder), ranks at each position `i` agree between `assignRanks cmp X` and `assignRanks cmp Y`. | — |
| `sortBy_eq_of_perm_strict` | 2049-2077 | If `X.Perm Y` and `cmp` is strict on `X` (no two distinct elements are `cmp`-equal), then `sortBy cmp X = sortBy cmp Y`. | — |

## Archive/V4/FullCorrectness/Equivariance/LabelEdgesCharacterization.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `computeDenseRanks_size` | 50-74 | `(computeDenseRanks numVertices rks).size = numVertices`. | — |
| `labelEdgesStep` | 82-96 | The `labelEdgesAccordingToRankings` fold body extracted as a standalone function (swap-and-update). | Definition |
| `labelEdges_fold_strong` | 169-242 | Strong fold invariant: tracks both the cumulative permutation σ and `acc.2.getD v 0 = rankMap₀.getD (σ⁻¹ v) 0` pointwise. | — |
| `labelEdges_terminal_rankMap_identity` | 381-397 | After the full foldl over `List.finRange n`, the terminal rankMap is the identity: `rankMap.getD v.val 0 = v.val`. | — |

## Archive/V4/FullCorrectness/Tiebreak.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `VtsInvariant` | 39-41 | Predicate: `σ` maps `vts` to itself (`vts.getD (σ v).val 0 = vts.getD v.val 0` for all `v`). | Definition |
| `VtsInvariant.one` | 43-44 | The identity permutation always satisfies `VtsInvariant`. | — |
| `VtsInvariant.mul` | 46-51 | Composition: if σ and τ both satisfy `VtsInvariant`, so does `σ * τ`. | — |
| `VtsInvariant.inv` | 53-60 | Inversion: if σ satisfies `VtsInvariant`, so does `σ⁻¹`. | — |
| `AdjMatrix.TypedAut` | 62-77 | Subgroup of `Aut G` whose elements also satisfy `VtsInvariant vts`. | Definition |
| `mem_TypedAut_iff` | 79-81 | `σ ∈ G.TypedAut vts ↔ σ ∈ G.Aut ∧ VtsInvariant σ vts`. | — |
| `AdjMatrix.TypedAut_le_Aut` | 83-87 | `G.TypedAut vts` is a subgroup of `G.Aut`. | — |
| `VtsInvariant.replicate_zero` | 107-112 | The all-zeros array satisfies `VtsInvariant σ` for any σ. | — |
| `TypedAut_replicate_zero` | 114-119 | For any `G`, every automorphism is in `TypedAut G (Array.replicate n 0)` — the typed-automorphism group with all-zeros types coincides with the full automorphism group. | — |
| `typeClass` | 142-144 | The set of `Fin n` vertices with vertex type exactly `t₀` in `vts`. | Definition |
| `shiftAbove_size` | 168-170 | `shiftAbove t₀ vts` preserves array size. | — |
| `shiftAbove_getD` | 172-182 | Value of `shiftAbove t₀ vts` at position `j`. | — |
| `shiftAbove_getD_below` | 184-189 | Positions with type `< t₀` are unchanged by `shiftAbove`. | — |
| `shiftAbove_getD_above` | 191-195 | Positions with type `> t₀` have their value incremented by 1 after `shiftAbove`. | — |
| `shiftAbove_getD_target` | 197-200 | Positions with type `= t₀` also have value shifted after `shiftAbove`. | — |
| `breakTieCount` | 204-207 | Number of vertices in `vts` with type `t₀`. | Definition |
| `breakTie_noop` | 209-216 | If `t₀` does not appear in `vts`, `breakTie t₀ vts = vts`. | — |
| `breakTie_eq_promote_shift` | 218-226 | `breakTie t₀ vts = shiftAbove t₀ (breakTiePromote t₀ vts)`. | — |
| `breakTiePromote_size` | 306-310 | `breakTiePromote t₀ vts` preserves array size. | — |
| `breakTiePromote_getD_of_ne` | 312-317 | `breakTiePromote` leaves positions whose type is not `t₀` unchanged. | — |
| `breakTie_size` | 319-325 | `breakTie t₀ vts` preserves array size. | — |
| `breakTie_getD_below` | 327-339 | Positions with type `< t₀` are unchanged by `breakTie`. | — |
| `breakTie_getD_above` | 341-355 | Positions with type `> t₀` have their value shifted up by 1 after `breakTie`. | — |
| `breakTie_getD_above_or` | 357-366 | Combined case: value at position `≥ t₀` after `breakTie`. | — |
| `breakTiePromote_getD_at_min` | 474-534 | Value at the minimum vertex with type `t₀` after `breakTiePromote`. | — |
| `breakTiePromote_getD_at_other` | 536-583 | Value at non-minimum vertices with type `t₀` after `breakTiePromote`. | — |
| `breakTie_getD_at_min` | 604-618 | The minimum vertex with type `t₀` receives a unique promoted value after `breakTie`. | — |
| `breakTieCount_eq_countP` | 620-638 | `breakTieCount t₀ vts = vts.toList.countP (· == t₀)`. | — |
| `breakTieCount_ge_two_of_distinct` | 640-718 | If two distinct vertices have type `t₀`, then `breakTieCount t₀ vts ≥ 2`. | — |
| `breakTie_getD_at_other` | 720-742 | Non-minimum vertices with type `t₀` receive the shifted-up value after `breakTie`. | — |
| `breakTie_getD_target` | 744-767 | Value at arbitrary positions after `breakTie`, by type case. | — |
| `breakTie_getD_target_ge` | 769-777 | Every position's value after `breakTie` is `≥` its original value. | — |
| `breakTie_Aut_stabilizer` | 779-908 | §5.1: characterizes `TypedAut G (breakTie vts t₀)` as the `v_star`-stabilizer subgroup of `TypedAut G vts`, where `v_star := min (typeClass vts t₀)`. Requires `vts` to be `Aut(G)`-invariant. | — |
| `breakTie_TypedAut_le` | 910-924 | `G.TypedAut (breakTie t₀ vts) ≤ G.TypedAut vts`: breaking a tie can only shrink the typed automorphism group. | — |
| `breakTie_strict_shrink` | 926-960 | §5.2: Strict inclusion `G.TypedAut (breakTie vts t₀) < G.TypedAut vts`, given an `hmove` witness — some σ ∈ TypedAut(G,vts) with σ v_star ≠ v_star. | — |
| `runFrom` | 1007-1019 | "Remainder of the pipeline" referenced in §6: feed an intermediate typing in, run the remaining `orderVertices` outer iterations and the final `labelEdgesAccordingToRankings`, and produce the canonical matrix. | Definition |
| `breakTieAt` | 1029-1038 | The "what if we had kept vertex `keep` instead of `min (typeClass vts t₀)`" alternative to `breakTie`. Promotes every vertex with value `t₀` except `keep` to `t₀ + 1`. | Definition |
| `breakTieAt_size` | 1074-1078 | `breakTieAt vts t₀ keep` preserves array size. | — |
| `breakTieAt_getD_of_ne` | 1129-1134 | `breakTieAt` leaves positions `≠ keep` unchanged. | — |
| `breakTieAt_getD_keep` | 1156-1160 | `breakTieAt` preserves the value at `keep`. | — |
| `breakTieAt_getD_promoted` | 1198-1206 | Value at positions promoted by `breakTieAt`. | — |
| `breakTieAt_VtsInvariant_eq` | 1208-1248 | `breakTieAt` preserves `VtsInvariant τ` when `τ keep = keep`. | — |
| `Decidable (VtsInvariant σ vts)` | — | Instance: `VtsInvariant σ vts` is decidable. | Instance |
| `Decidable (σ ∈ G.TypedAut vts)` | — | Instance: membership in `TypedAut` is decidable. | Instance |
| `Fintype (G.TypedAut vts)` | — | Instance: `G.TypedAut vts` is finite. | Instance |

## Archive/V4/FullCorrectness/Equivariance/ComparePathSegments.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `comparePathSegments_total_preorder` | 75-275 | Proves `comparePathSegments` satisfies all four total-preorder properties: reflexivity, both antisymmetries (`.lt → .gt` and `.gt → .lt`), and ≤-transitivity (`≠ .gt`). Mixed `bottom`/`inner` cases use the fixed `bottom < inner` ordering; inner-inner cases reduce to Nat-tuple lexicographic order. | — |
| `orderInsensitiveListCmp_refl` | 284-317 | `orderInsensitiveListCmp cmp L L = .eq` when `cmp` is reflexive on elements of `L`. Uses `sortBy_perm` to transfer reflexivity from `L` to its sorted form. | — |
| `comparePathSegments_equivCompat` | 319-387 | If `comparePathSegments vts br p q = .eq`, then `p` and `q` compare identically against any third segment `r` in either argument position. The `h_compat` hypothesis required by `orderInsensitiveListCmp_trans` and `_equivCompat`. | — |
| `orderInsensitiveListCmp_swap_lt` | 414-489 | Antisymmetry-`.lt → .gt` lift: `orderInsensitiveListCmp cmp L₁ L₂ = .lt → orderInsensitiveListCmp cmp L₂ L₁ = .gt`. Handles equal-length and length-mismatch cases separately. | — |
| `orderInsensitiveListCmp_swap_gt` | 491-561 | Antisymmetry-`.gt → .lt` lift: `orderInsensitiveListCmp cmp L₁ L₂ = .gt → orderInsensitiveListCmp cmp L₂ L₁ = .lt`. Mirror of `_swap_lt`. | — |
| `orderInsensitiveListCmp_trans` | 679-752 | Transitivity lift: `orderInsensitiveListCmp cmp L₁ L₂ ≠ .gt → ... L₂ L₃ ≠ .gt → ... L₁ L₃ ≠ .gt`. Equal-length case delegates to `foldl_zip_trans`; length-mismatch cases reduce to length arithmetic. | — |
| `orderInsensitiveListCmp_equivCompat` | 789-902 | Bilateral compat lift: if `orderInsensitiveListCmp cmp L₁ L₂ = .eq`, then `L₁` and `L₂` compare identically against any third list in either argument position. Extracts pointwise class equality via `foldl_zip_eq_implies_pairwise_eq`, then applies `foldl_pointwise_eq`. | — |
| `comparePathsBetween_total_preorder` | 904-1048 | `comparePathsBetween` is a total preorder, assembled by lifting all four properties of `comparePathSegments_total_preorder` through the `orderInsensitiveListCmp` helpers. Compares first by `endVertexIndex` type, then by the order-insensitive list of `connectedSubPaths`. | — |

## Archive/V4/FullCorrectness/Equivariance/CompareEquivariant.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `orderInsensitiveListCmp_map` | 25-54 | `orderInsensitiveListCmp` is invariant under applying `f` to both lists when `f` globally preserves `cmp`. | — |
| `sortBy_map_pointwise` | 73-89 | Pointwise variant of `sortBy_map`: requires `cmp (f a) (f b) = cmp a b` only for `a, b ∈ L`. | — |
| `comparePathSegments_σ_equivariant` | 91-130 | `comparePathSegments vts br (PathSegment.permute σ p) (PathSegment.permute σ q) = comparePathSegments vts br p q` under σ-invariant `vts` and `br`. | — |
| `map_reindex_perm` | 138-172 | Reindex-perm lemma: σ-reindexing `L.map act` gives a `List.Perm` of `L.map act`. | — |
| `PathsBetween_permute_connectedSubPaths_perm` | 174-216 | `(p.permute σ).connectedSubPaths.Perm (p.connectedSubPaths.map (PathSegment.permute σ))` for depth>0 paths of length `vc`. | — |
| `PathsFrom_permute_pathsToVertex_perm` | 218-256 | `(p.permute σ).pathsToVertex.Perm (p.pathsToVertex.map (PathsBetween.permute σ))` for length-`vc` `pathsToVertex`. | — |
| `comparePathsBetween_σ_equivariant` | 258-299 | `comparePathsBetween vts br (p₁.permute σ) (p₂.permute σ) = comparePathsBetween vts br p₁ p₂` under σ-invariant `vts`/`br` and length conditions. | — |
| `comparePathsBetween_equivCompat` | 301-352 | Bilateral compat for `comparePathsBetween`: if it returns `.eq`, both arguments compare identically against any third. | — |
| `betweenRankFn_σ_inv_from_cells` | 389-411 | Cell-level σ-invariance of a 3D table lifts to a σ-invariant function (the `betweenRankFn` projection). | — |
| `initializePaths_σInv_via_Aut` | 413-421 | For σ ∈ Aut G, `initializePaths G = PathState.permute σ (initializePaths G)`. Direct corollary of Stage A. | — |

## Archive/V4/FullCorrectness/Equivariance/PathsAtDepthStructure.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `initializePaths_pathsAtDepth_structure` | 47-104 | Outer length `= n`, start-vertex enumeration `= List.range n`, inner-length conditions for a depth-`d` slice of `initializePaths G`. | — |
| `initializePaths_allBetween_pairs_facts` | 156-228 | The `(start, end)` pairs of `allBetween` are Nodup and cover every `(s, e) ∈ Fin n × Fin n`. | — |

## Archive/V4/FullCorrectness/Equivariance/ChainSetInvariant.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `set_chain_size_preserving` | 34-49 | The `set!`-chain foldl on `fromAcc` preserves the outer array size. | — |
| `set_chain_row_size_preserving` | 51-91 | The `set!`-chain foldl preserves each depth-row's size. | — |
| `set_chain_σInvariant` | 93-256 | The `fromRanks` `set!`-chain preserves σ-invariance given σ-rank-closure of the assignList and start-vertex permutation coverage. | — |
| `nested_set_chain_at_target_pair_nodup` | 311-393 | Nested `set!`-chain at target `(d, s, e)` gives the inserted value when the `(start, end)` keys are Nodup. | — |
| `setBetween_chain_size_preserving` | 395-410 | The `setBetween` chain preserves the outer `betweenRanks` array size. | — |
| `setBetween_chain_row_size_preserving` | 412-462 | The `setBetween` chain preserves each depth-row's size. | — |
| `setBetween_chain_cell_size_preserving` | 464-485 | The `setBetween` chain preserves each `(depth, start)` cell's size. | — |
| `setBetween_chain_σInvariant` | 487-689 | The `betweenRanks` `setBetween`-chain preserves σ-invariance given σ-rank-closure of the assignList and `(start, end)`-pair Nodup coverage. | — |

## Archive/V4/FullCorrectness/Equivariance/AssignListRankClosure.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `comparePathSegments_σ_self_eq` | 69-90 | `comparePathSegments vts br p (PathSegment.permute σ p) = .eq` under σ-invariant `vts` and `br`. | — |
| `comparePathsBetween_σ_self_eq` | 92-127 | `comparePathsBetween vts br p (p.permute σ) = .eq` under σ-invariant `vts`/`br` and length conditions. | — |
| `comparePathsFrom_σ_self_eq` | 129-164 | `comparePathsFrom vts br p (p.permute σ) = .eq` under σ-invariant `vts`/`br` and length conditions. | — |
| `state_σ_fixed_pathsOfLength_at_σ_slot` | 191-268 | For a σ-fixed `PathState`, reading slot `s` of the depth-`d` array equals reading slot `σ s` in the original. | — |
| `comparePathsFrom_total_preorder` | 270-444 | `comparePathsFrom` satisfies all four total-preorder properties, lifted from `comparePathsBetween_total_preorder` through `orderInsensitiveListCmp`. | — |
| `from_assignList_σ_rank_closure` | 446-621 | The `fromRanks` assignList is σ-rank-closed: for each `(p, r)` in the list, `(PathsFrom.permute σ p, r)` is also in the list. | — |
| `mem_allBetween_iff` | 649-656 | `q ∈ allBetween ↔ ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex`. | — |
| `between_assignList_σ_rank_closure` | 658-833 | The `betweenRanks` assignList is σ-rank-closed: for each `(q, r)` in the list, `(PathsBetween.permute σ q, r)` is also in the list. | — |

## Archive/V4/FullCorrectness/Equivariance/PathEquivariance.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `calculatePathRankings_σInvariant_combined` | 319-339 | Combined `RankState.σInvariant σ` for `calculatePathRankings (initializePaths G) vts`: assembles size invariants and cell σ-invariance into the full `σInvariant` structure. | — |
| `calculatePathRankings_fromRanks_inv` | 341-350 | σ-invariance of `fromRanks` values: `(rs.fromRanks.getD d #[]).getD s.val 0 = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0`. Projection of `σInvariant_combined`. | — |
| `calculatePathRankings_betweenRanks_inv` | 352-361 | σ-invariance of `betweenRanks` values: `((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0 = ... (σ⁻¹ s) ... (σ⁻¹ e) ...`. Projection of `σInvariant_combined`. | — |
| `calculatePathRankings_σInvariant` | 363-370 | Direct alias for `calculatePathRankings_σInvariant_combined`; the canonical public name for the full σ-invariance result. | — |
| `calculatePathRankings_RankState_invariant` | 372-382 | `RankState.permute σ` is the identity on `calculatePathRankings (initializePaths G) vts` when σ ∈ Aut G and vts is σ-invariant. | — |
| `calculatePathRankings_Aut_equivariant` | 384-398 | **Stage B**: `calculatePathRankings (PathState.permute σ (initializePaths G)) vts = RankState.permute σ (calculatePathRankings (initializePaths G) vts)`. Assembled from Stage A plus σ-invariance. | — |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `comparePathSegments_σ_relational` | 67-103 | Relational form: `comparePathSegments vts₂ br₂ p₁ p₂ = comparePathSegments vts₁ br₁ (f p₁) (f p₂)` when `f = PathSegment.permute σ` and the two `vts`/`br` pairs are σ-related. | — |
| `sortBy_map_pointwise_relational` | 130-148 | Relational pointwise variant of `sortBy_map`: `sortBy cmp₂ (L.map f) = (sortBy cmp₁ L).map f` when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. | — |
| `orderInsensitiveListCmp_map_pointwise_relational` | 150-203 | Relational pointwise variant of `orderInsensitiveListCmp_map`: `orderInsensitiveListCmp cmp₂ (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp₁ L₁ L₂` with per-element `cmp₂ (f a) (f b) = cmp₁ a b`. | — |
| `comparePathsBetween_σ_relational` | 205-252 | Relational form of `comparePathsBetween_σ_equivariant` for two different `vts`/`br` pairs. | — |
| `comparePathsFrom_σ_relational` | 254-305 | σ-equivariance of `comparePathsFrom` across two different `vts`/`br` pairs. | — |
| `set_chain_σRelated` | 360-521 | The `fromRanks` `set!`-chain produces τ-related outputs when the two assignLists are τ-related (each entry in one maps to a τ-shifted entry of equal rank in the other). | — |
| `setBetween_chain_σRelated` | 523-734 | The `betweenRanks` `setBetween`-chain produces τ-related outputs when the two assignLists are τ-related. | — |
| `from_assignList_σ_rank_rel` | 900-1154 | Relational σ-rank-closure for the `fromRanks` assignList: entries on the two sides are τ-related with equal ranks. | — |
| `between_assignList_σ_rank_rel` | 1253-1485 | Relational σ-rank-closure for the `betweenRanks` assignList. | — |
| `betweenRankFn_σ_rel_from_cells` | 1494-1510 | Cell-level τ-relatedness of a 3D table lifts to a τ-related `betweenRankFn`. | — |
| `CalcRankingsRel` | 1512-1536 | Loop invariant for the relational depth foldl: the two accumulators `(currentBetween₁, currentFrom₁)` and `(currentBetween₂, currentFrom₂)` are τ-related at every cell. | Definition |
| `calculatePathRankings_σ_equivariant_relational` | 1852-1871 | **Stage B-rel**: `calculatePathRankings` outputs on τ-related inputs are τ-related at every cell. Requires σ ∈ Aut G. | — |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `from_assignList_σ_rank_general` | 397-633 | General σ-rank-closure for the `fromRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | — |
| `between_assignList_σ_rank_general` | 642-880 | General σ-rank-closure for the `betweenRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | — |
| `calculatePathRankings_σ_equivariant_general` | 1280-1298 | **Stage B-rel-general**: `calculatePathRankings` on `initializePaths (G.permute σ)` is σ-related to `calculatePathRankings` on `initializePaths G`, for any σ (no Aut G hypothesis). | — |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoop.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_writeback` | 102-113 | After `convergeOnce`, every in-bounds position `i` holds `calculatePathRankings.getFrom (n-1) i`. | — |
| `RankState.getFrom_permute` | 115-142 | `getFrom` on `RankState.permute σ rs` reads from the `σ⁻¹`-shifted position in the original `rs`. | — |
| `calculatePathRankings_getFrom_invariant` | 144-177 | σ-invariance of `getFrom (n-1)`: positions `v` and `σ v` return the same value when σ ∈ Aut(G) and `vts` is σ-invariant. | — |
| `convergeOnce_Aut_invariant` | 179-196 | One `convergeOnce` step preserves Aut(G)-invariance: `output[σ v] = output[v]` for σ ∈ Aut(G). | — |
| `convergeOnce_size_preserving` | 198-222 | `convergeOnce` preserves the vertex type array size. | — |
| `convergeLoop_Aut_invariant` | 224-250 | The full convergence loop preserves Aut(G)-invariance for any fuel; proved by induction on fuel. | — |
| `convergeLoop_zeros_Aut_invariant` | 252-260 | Corollary: starting from the all-zeros array, the convergence loop preserves Aut(G)-invariance. | — |
| `orderVertices_Aut_equivariant` | 264-275 | Stage C: `orderVertices (PathState.permute σ (initializePaths G)) vts = orderVertices (initializePaths G) vts` for σ ∈ Aut(G). | — |
| `labelEdges_Aut_equivariant` | 279-287 | Stage D: `labelEdgesAccordingToRankings vts (G.permute σ) = labelEdgesAccordingToRankings vts G` for σ ∈ Aut(G); follows immediately from `G.permute σ = G`. | — |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_unchanged_when_not_flag` | 59-66 | If `convergeOnce`'s flag output is `false`, the output array equals the input array (fixed point). | — |
| `convergeLoop_unchanged_fixedpoint` | 68-83 | If `convergeOnce`'s flag is `false`, then `convergeLoop` is the identity at every fuel level. | — |
| `convergeLoop_succ_eq_loop_of_once` | 85-104 | `convergeLoop state vts (k+1) = convergeLoop state (convergeOnce state vts).1 k` regardless of the flag. | — |
| `calculatePathRankings_getFrom_VtsInvariant_eq` | 108-125 | Relational `getFrom (n-1)` analogue: for τ-related `vts₁`/`vts₂`, the `getFrom` values are τ-shifted. | — |
| `convergeOnce_VtsInvariant_eq` | 129-152 | One `convergeOnce` step on τ-related arrays produces τ-related outputs. Relational analogue of `convergeOnce_Aut_invariant`. | — |
| `convergeLoop_VtsInvariant_eq` | 154-183 | The full `convergeLoop` preserves τ-relatedness for any fuel. Relational analogue of `convergeLoop_Aut_invariant`. | — |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_σ_equivariant_general` | 44-69 | **P6.B**: `convergeOnce` on `(initializePaths (G.permute σ), vts₂)` is σ-related to `convergeOnce` on `(initializePaths G, vts₁)` for any σ. | — |
| `convergeLoop_σ_equivariant_general` | 71-103 | **P6.B loop**: The full `convergeLoop` is σ-equivariant across the two general states for any fuel. | — |

## Archive/V4/FullCorrectness/Equivariance/StageDRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `TieFree` | 40-43 | Predicate: all `n` vertices have distinct types in `rks` (no ties). | Definition |
| `computeDenseRanks_perm_when_tieFree` | 362-380 | Under `TieFree rks n`, `computeDenseRanks` output is a permutation of `[0, 1, ..., n-1]`. | — |
| `computeDenseRanks_τ_shift_distinct` | 500-569 | Under `TieFree` and τ-related ranks, `computeDenseRanks` on `rks₂` is the τ-shifted `computeDenseRanks` on `rks₁`. | — |
| `labelEdges_VtsInvariant_eq_distinct` | 573-653 | When `rks` is tie-free, `labelEdgesAccordingToRankings rks G` is invariant under `VtsInvariant` (Aut G acts trivially). | — |
| `labelEdges_two_graphs_σ_related` | 663-721 | Under τ-related tie-free ranks, `labelEdgesAccordingToRankings rks₂ G₂ = labelEdgesAccordingToRankings rks₁ G₁`. Stage D-rel. | — |

## Archive/V4/FullCorrectness/Equivariance/BreakTieRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `shiftAbove_VtsInvariant_eq` | 33-52 | `shiftAbove t₀ vts₂` at slot `w` equals `shiftAbove t₀ vts₁` at slot `τ⁻¹ w` when `vts₁`/`vts₂` are τ-related. | — |
| `shiftAbove_VtsInvariant_size_eq` | 54-57 | τ-related `vts₁`/`vts₂` have the same size after `shiftAbove`. | — |
| `breakTieAt_τ_related` | 68-105 | `breakTieAt vts₂ t₀ (τ keep)` at slot `w` equals `breakTieAt vts₁ t₀ keep` at slot `τ⁻¹ w` when inputs are τ-related. | — |
| `breakTieAt_size_eq` | 107-111 | τ-related `vts₁`/`vts₂` have the same size after `breakTieAt`. | — |

## Archive/V4/FullCorrectness/Invariants.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `IsPrefixTyping` | 72-76 | A typing `vts` is a prefix of ℕ: its value set equals `{0, 1, …, m-1}` for some `m`. | Definition |
| `IsPrefixTyping.replicate_zero` | 78-97 | The all-zeros array satisfies `IsPrefixTyping`. | — |
| `convergeLoop_size_preserving` | 101-117 | `convergeLoop` preserves the vertex type array size. | — |
| `getFrom_image_isPrefix_for_initializePaths` | 491-700 | The image of `getFrom (n-1)` on `calculatePathRankings (initializePaths G) vts` is a prefix `{0, ..., k}`. | — |
| `convergeLoop_preserves_prefix` | 702-739 | `convergeLoop` preserves `IsPrefixTyping` from fuel 0 onward. | — |
| `breakTie_targetPos_is_min_tied` | 743-832 | The tiebreak target position `breakTieAt`'s `keep` argument is the minimum vertex in the tied type class. | — |
| `UniquelyHeldBelow` | 849-855 | Predicate: every value `< q` in `vts` is held by exactly one vertex. The algorithmic hypothesis (Phase 5) that values `0..q-1` are already uniquely held, so remaining foldl iterations can finish breaking ties. | Definition |
| `convergeLoop_preserves_lower_uniqueness` | 1616-1643 | `convergeLoop` preserves `UniquelyHeldBelow q` for any fuel. | — |
| `breakTie_step_preserves_uniqueness` | 1751-1913 | One `breakTie` step preserves `UniquelyHeldBelow` for the next level. | — |
| `orderVertices_prefix_invariant` | 1966-1977 | `orderVertices (initializePaths G) zeros` satisfies `IsPrefixTyping`. | — |
| `orderVertices_n_distinct_ranks` | 1979-2043 | `orderVertices` produces exactly `n` distinct values `0, 1, ..., n-1`. | — |
| `getArrayRank_size` | 2051-2085 | `getArrayRank arr` preserves array size. | — |
| `getArrayRank_zeros_eq_zeros` | 2087-2225 | `getArrayRank (Array.replicate n 0) = Array.replicate n 0`. | — |
| `orderVertices_size_eq` | 2227-2250 | `orderVertices (initializePaths G) vts` preserves array size. | — |

## Archive/V4/FullCorrectness/Equivariance/RunFromRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeLoop_step_τ_preserved` | 187-204 | One `convergeLoop ∘ breakTieAt` step preserves τ-relatedness of the arrays. | — |
| `IsPrefixTyping_τ_transfer` | 214-232 | τ-relatedness transfers `IsPrefixTyping`: if `vts₁` is a prefix typing and `vts₂` is τ-related, so is `vts₂`. | — |
| `UniquelyHeldBelow_τ_transfer` | 234-258 | τ-relatedness transfers `UniquelyHeldBelow q`: if `vts₁` holds it and `vts₂` is τ-related, so does `vts₂`. | — |
| `runFrom_at_n` | 262-267 | `runFrom n vts G = vts` (base case: no vertices left to process). | — |
| `runFrom_succ` | 269-309 | Unfolding: `runFrom s vts G = runFrom (s+1) (convergeLoop ∘ breakTieAt s vts) G`. | — |
| `UniquelyHeldBelow_n_implies_TieFree` | 311-368 | `UniquelyHeldBelow n vts` implies `TieFree vts n`. | — |
| `breakTieCount_τ_invariant` | 385-409 | `breakTieCount t₀ vts₂ = breakTieCount t₀ vts₁` when `vts₁`/`vts₂` are τ-related. | — |
| `typeClass_τ_image_eq` | 413-435 | `typeClass vts₂ t₀ = τ '' (typeClass vts₁ t₀)` when `vts₂` is τ-related to `vts₁`. | — |
| `breakTie_min_witness` | 437-473 | The minimum vertex in `typeClass vts₂ t₀` is `τ` applied to the minimum in `typeClass vts₁ t₀`. | — |
| `breakTie_min_witness_in_typeClass` | 475-483 | The minimum witness vertex lies in `typeClass`. | — |
| `OrbitCompleteAfterConv` | 502-512 | Orbit-completeness: for `mid` an intermediate algorithm state, vertices with equal values in `convergeLoop(initializePaths G) mid n` lie in the same `TypedAut`-orbit of that converged array. | Definition |
| `runFrom_VtsInvariant_eq_strong` | 514-707 | Strong relational theorem: `runFrom s vts₂ G = runFrom s vts₁ G` (not just τ-related, equal) given `OrbitCompleteAfterConv` and `UniquelyHeldBelow s`. | — |
| `runFrom_VtsInvariant_eq` | 720-737 | Corollary of the strong form: `runFrom 0 zeros G = runFrom 0 (τ-shifted zeros) G`. | — |
| `tiebreak_choice_independent` | 739-775 | The canonical `orderVertices` output is independent of which tied vertex is chosen for tiebreaking; proved from `runFrom_VtsInvariant_eq`. | — |

## Archive/V4/FullCorrectness/Equivariance/OrderVerticesGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `OrbitCompleteAfterConv_general` | 34-45 | Two-graphs variant of `OrbitCompleteAfterConv`: orbit-completeness for `convergeLoop (initializePaths (G.permute σ)) mid n`. | Definition |
| `runFrom_VtsInvariant_eq_strong_general` | 131-377 | **P6.C**: `runFrom s vts₁ G = runFrom s vts₂ (G.permute σ)` given `OrbitCompleteAfterConv_general` and σ-relatedness of the arrays. | — |

## Archive/V4/FullCorrectness/Equivariance/MainRelationalNotes.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `zeros_σ_invariant` | 91-97 | The all-zeros array is σ-invariant for any σ: `(Array.replicate n 0).getD (σ v) 0 = (Array.replicate n 0).getD v 0 = 0`. | — |

## Archive/V4/FullCorrectness/Main.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `run_isomorphic_eq_new` | 147-157 | **(⟹) direction**: `G ≃ H → run zeros G = run zeros H`. Assembled from Stage A + Stage B-rel-general + P6.B/C + Stage D-rel. | — |
| `run_canonical_correctness` | 167-185 | **Main theorem**: `G ≃ H ↔ run zeros G = run zeros H`. Combines both directions. | — |

## Archive/V4/FullCorrectness/V4Reused.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `swapVertexLabels_self_inverse` | 47-49 | — | — |
| `swapVertexLabels_comm` | 51-55 | — | — |
| `AdjMatrix.Isomorphic.symm` | 59-70 | Symmetry of `OrbitPartition` (via permutation inverse). | — |
| `labelEdgesAccordingToRankings_isomorphic` | 74-126 | — | — |
| `run_isomorphic_to_input` | 128-131 | — | — |
| `run_eq_implies_iso` | 135-146 | — | — |

## Archive/V4/LeanGraphCanonizerV4.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `VertexType` | 5 | — | `abbrev` |
| `EdgeType` | 6 | — | `abbrev` |
| `Graph.AdjMatrix` | 10-11 | Self-contained adjacency matrix on `Fin n`, wrapping a `Fin n → Fin n → Nat` field. | Structure |
| `swapVertexLabels` | 17-21 | — | Definition |
| `Isomorphic` | 23-34 | — | Inductive |
| `adjToString` | 36-41 | — | Definition |
| `PathSegment` | 56-60 | — | Inductive |
| `PathsBetween` | 62-67 | — | Structure |
| `PathsFrom` | 69-73 | — | Structure |
| `PathState` | 75-76 | — | Structure |
| `RankState` | 78-80 | — | Structure |
| `RankState.getBetween` | 82-83 | — | Definition |
| `RankState.getFrom` | 85-86 | — | Definition |
| `insertSorted` | 90-92 | — | Definition |
| `sortBy` | 94-96 | — | Definition |
| `orderInsensitiveListCmp` | 98-103 | — | Definition |
| `comparePathSegments` | 107-125 | — | Definition |
| `comparePathsBetween` | 127-135 | — | Definition |
| `comparePathsFrom` | 137-145 | — | Definition |
| `initializePaths` | 149-165 | — | Definition |
| `assignRanks` | 175-186 | — | Definition |
| `setBetween` | 188-192 | — | Definition |
| `calculatePathRankings` | 194-224 | — | Definition |
| `convergeOnce` | 228-240 | — | Definition |
| `convergeLoop` | 241-245 | — | Definition |
| `shiftAbove` | 264-266 | — | Definition |
| `breakTiePromote` | 268-282 | — | Definition |
| `breakTie` | 284-290 | — | Definition |
| `orderVertices` | 292-297 | — | Definition |
| `computeDenseRanks` | 301-318 | — | Definition |
| `getArrayRank` | 320-343 | — | Definition |
| `labelEdgesAccordingToRankings` | 345-361 | — | Definition |
| `run` | 365-369 | — | Definition |

## Archive/V4/UniqueGraphsBySize.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `size2` | 9-12 | — | Definition |
| `size3` | 14-19 | — | Definition |
## Archive/ChainDescent-scratch/ScratchBM3Bridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BM3Bridge.encV` | 15 | The computable base-3 digit equiv `Fin 4 → ZMod 3 ≃ Fin 81` (`finFunctionFinEquiv`) transporting the abstract vector space to `Nat`-codes. | `abbrev` |
| `BM3Bridge.Qvo` | 17-18 | The concrete unbundled VO⁻₄(3) minus-form `y₀y₁ + y₂² + y₃²` over `ZMod 3`. | Definition |
| `BM3Bridge.co` | 20-21 | The `i`-th base-3 digit of a `Nat` code, indexed to match `encV`. | Definition |
| `BM3Bridge.Qc` | 22 | The minus-form `Qvo` evaluated directly on a `Nat` code's digits, reduced mod 3. | Definition |
| `BM3Bridge.Qsh` | 23-28 | The shifted (basepoint-translated) minus-form value on `Nat` codes — the incidence value `Qvo(y − (b − v))` in pure-`Nat` form. | Definition |
| `BM3Bridge.co_encV` | 30-34 | **Foundational.** The `Nat` digit-decode `co` of a code recovers the corresponding coordinate's `ZMod 3` `val`. | — |
| `BM3Bridge.val_zero` | 36-37 | A `ZMod 3` element is zero iff its `val` is zero. | — |
| `BM3Bridge.coord_id` | 38-39 | The `val` of `x − z + w` in `ZMod 3` as an explicit `Nat` `%3` expression. | — |
| `BM3Bridge.QvoVal` | 41-46 | `(Qvo w).val` written as a flat `Nat` polynomial mod 3 over the coordinate `val`s. | — |
| `BM3Bridge.Qc_encV` | 48-50 | The `Nat`-code form `Qc` at a code equals `(Qvo ·).val` of the decoded vector. | — |
| `BM3Bridge.coord_sub` | 52-56 | The shifted coordinate `((y − (b − v)) i).val` as an explicit `Nat` `%3` expression. | — |
| `BM3Bridge.Qsh_encV` | 58-63 | The `Nat`-code shifted form `Qsh` at codes equals `(Qvo (y − (b − v))).val`, the shifted incidence value. | — |
| `BM3Bridge.encV_zero` | 65-66 | `encV` sends the zero vector to the zero code. | — |
| `BM3Bridge.encV_val_zero` | 68-70 | A code has `val = 0` iff its decoded vector is zero. | — |
| `BM3Bridge.restrictedF` | 72-75 | The kernel-fast restricted isotropy count: a pure-`Nat`-predicate `card` over `Finset (Fin 81)` (nonzero, isotropic, and vanishing at two shifted bases). | Definition |
| `BM3Bridge.restricted_bridge` | 77-104 | **THE BRIDGE.** The abstract VO⁻₄(3) restricted isotropy count (over `Fin 4 → ZMod 3`, the Lemma-B object) equals the `Nat`-predicate count `restrictedF` at the codes of `v, b₁, b₂`. | — |
| `BM3Bridge.fam` | 106-107 | The 6 base-pair codes (as `Nat` pairs) making up the T₉ separating family. | Definition |
| `BM3Bridge.sigF` | 108 | The separating signature of a code: the list of `restrictedF` counts over the `fam` base-pairs. | Definition |
| `BM3Bridge.sigF_injective` | 110-111 | **THE DECIDED INJECTIVITY** (kernel `decide`, no `native_decide`). `sigF` is injective — the T₉ family separates all basepoints. | — |

## Archive/ChainDescent-scratch/ScratchBM3Glue.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Bil` | 17-23 | The VO⁻₄(3) bilinear form `B(x,y) = x₀y₁ + x₂y₂ + x₃y₃` (with `B x x = Qvo x`). | Definition, `noncomputable` |
| `Qbun` | 25-26 | The bundled VO⁻₄(3) minus-form `QuadraticForm` over `ZMod 3`, from `Bil`. | Definition, `noncomputable` |
| `Qbun_apply` | 28-29 | The bundled `Qbun` agrees pointwise with the concrete minus-form `Qvo`. | `@[simp]` |
| `Bv` | 31-34 | The 9 base vectors of T₉ in vector form (codes `[0,1,3,9,27,54,40,70,10]`). | Definition |
| `T₉` | 36-37 | The size-9 base on the scheme, the image of `Bv` under `affineE`. | Definition, `noncomputable` |
| `hcard9` | 39-41 | `T₉` has cardinality at most 9. | — |
| `Sij_subset` | 43-50 | Each base-pair 2-subset `{affineE (Bv i), affineE (Bv j)}` lies in `T₉`. | — |
| `vcount_eq` | 52-64 | **B-M1.** The incidence isotropy count for base-pair `{Bv i, Bv j}` at basepoint `w` equals the bridged `Nat`-predicate count `restrictedF` at the codes. | — |
| `comp_eq` | 66-79 | Per base-pair, the fine isotropy-count antecedent forces the bridged `restrictedF` counts at `u` and `u'` to agree. | — |
| `isoSep` | 81-117 | **B-M3 — the seal's Gauss target.** `IsotropySeparatesAtBase Qbun T₉`: the fine isotropy-count antecedent forces `u = u'`. | — |
| `vo4minus_seal` | 119-122 | **THE VO⁻₄(3) SEAL** (mod cited `{G3}`). The Witt-free capstone instantiated at the minus-form `Qbun` and base `T₉`, carrying no `hSmallAutThin` and no Witt. | Definition |

## Archive/ChainDescent-scratch/ScratchBaseAug.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BaseAug.IsoSetEq` | 37-41 | The base-augmentation observable: `u, u'` have the same isotropic set in the plane `W` (what `Obs_aug` delivers once `C^∞` pins `W`). | Definition |
| `BaseAug.sameExactGram_of_triple` | 43-53 | Packages the three Gram equalities `(Q u = Q u', polar u a = polar u' a, polar u b = polar u' b)` as `Wall.SameExactGram` over `{a,b}`. | — |
| `BaseAug.sameExactGram_of_isoSetEq_generic` | 55-73 | **★** Step B generic branch: on an anisotropic base at the generic level (`Z(u)` spans), `IsoSetEq ⟹ SameExactGram` to `{a,b}` — no counting. | — |
| `BaseAug.eq_wComp_of_isotropic_of_anisotropic` | 75-91 | (ii)-glue: on an anisotropic plane with isotropic complement component, `Z(u) = {u_W}` (the unique isotropic-in-`W` point). | — |
| `BaseAug.sameExactGram_of_isoSetEq_singleton_anis` | 93-116 | **★** Step B singleton branch: on an anisotropic plane in the singleton locus, `IsoSetEq` alone forces the `W`-components to match, then `SameExactGram` follows — the match is derived, not carried. | — |

## Archive/ChainDescent-scratch/ScratchBoundedBranching.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BoundedBranching.BTree` | 50-52 | **Phase 1 (recovery route T0).** A finitely-branching rooted tree (rose tree); a childless node is a leaf. The abstract carrier of the `leaves ≤ Bᴸ` combinatorics. | Inductive |
| `BoundedBranching.BTree.leaves` | 56-59 | Leaf count of a `BTree`: `1` for a childless node, else the sum over children. | Definition |
| `BoundedBranching.BTree.branchDepth` | 61-66 | The `L` in `leaves ≤ Bᴸ`: the max, over root→leaf paths, of the number of nodes with `≥ 2` children (genuine forks) — NOT the total depth. | Definition |
| `BoundedBranching.BTree.BoundedDeg` | 68-70 | Every node of the tree has `≤ B` children (the per-node branching bound `bᵢ ≤ B`). | Definition |
| `BoundedBranching.BTree.leaves_nil` | 72 | `leaves (node []) = 1` (a leaf has one leaf). | `@[simp]` |
| `BoundedBranching.BTree.leaves_cons` | 73-74 | `leaves (node (c::cs)) = Σ` child leaves (the non-leaf unfolding). | `@[simp]` |
| `BoundedBranching.BTree.le_foldr_max` | 76-81 | A list element is `≤` the list's `foldr max 0` (the running maximum). | — |
| `BoundedBranching.BTree.sum_map_const` | 83-88 | Sum of a constant map equals length × constant. | — |
| `BoundedBranching.BTree.leaves_le_pow` | 90-127 | **★ Key theorem (D3, the `leaves ≤ Bᴸ` core).** A tree with every node of degree `≤ B` has `≤ B ^ branchDepth` leaves — the recovery route's poly-leaf-count arithmetic. Forms-graph-free, reusable. | — |
| `BoundedBranching.BTree.leaves_le_one_of_boundedDeg_one` | 129-133 | `B = 1` (no node branches) ⟹ `leaves ≤ 1` — the tree-level single-path corner. | — |
| `BoundedBranching.SelectedCellOrbitsLE` | 147-154 | **Phase 1 predicate.** The selected cell at base `S` is covered by `≤ B` `Stab(S)`-orbits — the `B`-bounded generalization of `SelectedCellIsOrbit` (`bᵢ ≤ B`). | Definition |
| `BoundedBranching.BoundedBranchingDisposition` | 156-161 | The bridge-keyed hypothesis: every base's selected cell has `≤ B` orbits (`∀ S, SelectedCellOrbitsLE`). Generalizes `SinglePathDisposition` (the `B = 1` case). | Definition |
| `BoundedBranching.SelectedCellOrbitsLE.mono` | 163-169 | Monotone in `B`: a `≤ B`-orbit cover is a `≤ B'`-cover for `B ≤ B'`. | — |
| `BoundedBranching.BoundedBranchingDisposition.mono` | 171-175 | Monotone in `B` (pointwise from `SelectedCellOrbitsLE.mono`). | — |
| `BoundedBranching.selectedCellOrbitsLE_one_of_isOrbit` | 177-194 | The `B = 1` corner: a monochromatic single-orbit cell (`SelectedCellIsOrbit`) is a `≤ 1`-orbit cover. | — |
| `BoundedBranching.CertifiedBoundedTree` | 203-214 | **Phase 1 poly object (T0).** Bundles the disposition (`≤ B` orbits/cell) with an abstract descent tree's degree/depth bounds; exports `leaves ≤ Bᴸ`. The bounded-branching analogue of `CertifiedSinglePath`. | Structure |
| `BoundedBranching.CertifiedBoundedTree.leafBound` | 216-222 | **★ The exported poly leaf bound `leaves ≤ Bᴸ`**, from `BTree.leaves_le_pow` composed with `branchDepth ≤ L`. | — |
| `BoundedBranching.certifiedBoundedTree_of_disposition` | 224-236 | **★ The Phase-1 bridge capstone.** The bounded-branching disposition plus a descent tree realizing `≤ B` branching within `≤ L` levels ⟹ `CertifiedBoundedTree` (hence `leaves ≤ Bᴸ`). Generalizes `certifiedSinglePath_of_disposition`. | — |
| `BoundedBranching.leaves_le_one_of_certifiedBoundedTree_one` | 238-245 | The `B = 1` corner: a certified bounded tree with `B = 1` has a single leaf (recovers the single path). | — |

## Archive/ChainDescent-scratch/ScratchBoundedMultLeaves.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BoundedBranching.depth` | 32-35 | Total depth (levels) of a `BTree`, counting every node — the range of the per-level product below. | Definition |
| `BoundedBranching.depth_nil` | 37 | The empty node has depth `0`. | `@[simp]` |
| `BoundedBranching.depth_cons` | 38-39 | Depth of a non-empty node unfolds to `1 + ` the max child depth. | — |
| `BoundedBranching.BoundedDegAt` | 41-45 | **Per-level branching bound.** A node at depth `k` has `≤ b k` children (recursively) — the level-dependent generalisation of `BoundedDeg` the recovery route needs, where `bᵢ` varies sharply by level. | Definition |
| `BoundedBranching.leaves_le_prod` | 47-91 | **★ Per-level leaf bound.** Under a per-level branching bound `b` (each `b j ≥ 1`), `leaves ≤ ∏_{j<depth} b(k+j)`; a level with `b j = 1` contributes factor `1`, so branching concentrated at a few levels yields a tight product. | — |
| `BoundedBranching.leaves_le_prod_concentrated` | 93-107 | **★ Concentration corollary — branching confined to a level set `J`.** If `b j = 1` off a finite level set `J`, then `leaves ≤ ∏_{j∈J} b j` — the recovery route's `concentrated branching ⟹ poly leaves` (single span-dim-1 level, `b = q(q−1)/2`). | — |
| `BoundedBranching.leaves_le_pow_of_prod` | 109-114 | **`leaves_le_pow` recovered (sanity).** The constant bound `b ≡ B` gives back the uniform `leaves ≤ B^depth`, confirming `leaves_le_prod` is a genuine generalisation. | — |

## Archive/ChainDescent-scratch/ScratchBranchDepth.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BranchDepth.spanning_sameExactGram_determines` | 60-79 | **The spanning determiner (generalised `coords_determineK`).** With nondegenerate polar form, the exact Gram profile to a base whose span is `⊤` determines the vertex; generalises the standard-frame determiner to an arbitrary spanning base. | — |
| `BranchDepth.stabOrbit_singleton_of_spanning` | 81-92 | **★ Orbit-singletons at a spanning anisotropic base.** At a base that spans `V` and carries an anisotropic vector, every `Stab(S)`-orbit is a singleton — the geometric backbone of `an O(d) base rigidifies the forms graph`. | — |
| `BranchDepth.branchLevels_le_finrank` | 96-104 | **★ The `O(d)` branch-depth ceiling (arithmetic).** An independent family of `L` branch-level vectors has `L ≤ finrank K V`; feeds Phase 1's depth bound. | — |
| `BranchDepth.branchLevels_le_dim_forms` | 106-112 | **The forms-graph specialisation `L ≤ d`.** On `V = Fin d → K` an independent branch-level family numbers `≤ d`, i.e. `L = O(d)` — the recovery route's second poly factor, modulo the span-growth seam. | — |
| `BranchDepth.stab_fixes_span` | 129-138 | **The fixed-point kernel.** A similitude fixing `S` pointwise is linear, hence fixes all of `span S` pointwise — the source of every orbit-triviality fact below. | — |
| `BranchDepth.stabOrbit_trivial_of_mem_span` | 140-145 | **A vertex in `span S` is a singleton `Stab(S)`-orbit** — it cannot be moved, since every `S`-fixing similitude fixes `span S`. | — |
| `BranchDepth.notMem_span_of_stabOrbit_ne` | 147-152 | **Non-trivial orbit ⟹ outside the span (span-growth kernel).** A vertex with a non-trivial `Stab(S)`-orbit is not in `span S` — what makes a genuine fork add a new dimension. | — |
| `BranchDepth.span_lt_span_insert_of_stabOrbit_ne` | 154-164 | **★ A fork into a non-trivial orbit strictly grows the span:** individualizing a non-trivial-orbit vertex enlarges `span` — the step that drives the `L ≤ d` count. | — |
| `BranchDepth.strictChain_le_finrank` | 166-181 | **The strict-chain count.** A strictly increasing chain of `L+1` subspaces has `L ≤ finrank K V` steps — the dimension ceiling behind `L = O(d)`. | — |
| `BranchDepth.nontrivialForks_le_finrank` | 183-193 | **★ Span-growth, solved: non-trivial-orbit forks are `≤ d`.** A chain of bases whose spans strictly increase at every level has `≤ finrank K V` levels; the residual singleton-orbit forks are exactly the cell-discretisation gap (the shared open WL-orbit defect). | — |

## Archive/ChainDescent-scratch/ScratchBranchingBound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `BranchingBound.gramProfile` | 40-43 | **Phase 2.** The exact-Gram profile of `t` relative to a finite base `S`: `(Q t, (polar Q t s)_{s∈S})`. Orbits inject into these profiles (mod Witt). | Definition |
| `BranchingBound.gramProfile_eq_iff` | 45-56 | Equal Gram profiles ⟺ `SameExactGram` (same exact Gram data to `S`). | — |
| `BranchingBound.card_gramProfiles_le` | 58-65 | The number of distinct exact-Gram profiles relative to `S` is `≤ |K|^{|S|+1}`. | — |
| `BranchingBound.stabOrbit_cover_card_le` | 67-94 | **★ Key theorem (Phase 2 foundation, the a-priori branching bound).** Modulo Witt (`WittExtendsToOrbit`), the whole space is covered by `≤ |K|^{|S|+1}` `Stab(S)`-orbit representatives (orbits ↪ exact-Gram profiles) — discharges the Phase-1 `degBound` at the **quasipoly** tier; the polynomial target sharpens `B` to `poly(q)` per cell. | — |

## Archive/ChainDescent-scratch/ScratchComplementFactor.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ComplementFactor.map_add_of_polar_zero` | 44-50 | **Orthogonal vectors add in `Q`:** `polar Q x y = 0` ⟹ `Q(x+y) = Q x + Q y` — the pure-algebra core of the split. | — |
| `ComplementFactor.polar_zero_of_mem_orthogonal` | 52-58 | **The complement kills the polar pairing:** for `x ∈ W` and `y ∈ Wᗮ`, `polar Q x y = 0`. | — |
| `ComplementFactor.map_add_split` | 60-64 | **The orthogonal split (sum form):** for `x ∈ W`, `y ∈ Wᗮ`, `Q(x+y) = Q x + Q y`. | — |
| `ComplementFactor.map_sub_split` | 66-79 | **★ The orthogonal split (difference form) — the count-factoring foundation.** For `v = v₁+v₂`, `u = u₁+u₂` split across `W ⊕ Wᗮ`, the difference norm splits: `Q((v₁+v₂)−(u₁+u₂)) = Q(v₁−u₁) + Q(v₂−u₂)`, separating local Gram data from the complement datum. | — |
| `ComplementFactor.exists_decomp_of_isCompl` | 81-89 | **Decomposition into `W ⊕ Wᗮ`:** from `IsCompl W Wᗮ`, every vertex splits as `v = v₁ + v₂` with `v₁ ∈ W`, `v₂ ∈ Wᗮ` — feeds `map_sub_split`. | — |

## Archive/ChainDescent-scratch/ScratchComplementFactorK.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ComplementFactorK.levelset_count_factors_through_chiDet` | 38-100 | **★ The `d`-cancellation (increment 2, reused).** For two same-size configs with nondegenerate Gram whose discriminant characters `χ(det G)` agree, the scaled homogeneous level-set counts are equal uniformly in `d` — the `d`-dependent factors cancel, so isotropy counts factor through the local config invariant with the complement contributing only the common Gauss factor. | — |

## Archive/ChainDescent-scratch/ScratchConfinementResidual.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementResidual.residual_pred` | 77-83 | — | — |
| `ConfinementResidual.residualRestrict` | 85-90 | — | Definition |
| `ConfinementResidual.residualRestrict_apply` | 92-94 | — | `@[simp]` |
| `ConfinementResidual.residualRestrictHom` | 96-101 | — | Definition |
| `ConfinementResidual.residualRestrict_injective` | 103-115 | — | — |
| `ConfinementResidual.residualRestrictHom_injective` | 117-119 | — | — |
| `ConfinementResidual.residualRange_pretransitive` | 128-137 | — | — |
| `ConfinementResidual.residualCard` | 148-149 | — | Definition, `noncomputable` |
| `ConfinementResidual.residualEquivFin` | 151-154 | — | Definition, `noncomputable` |
| `ConfinementResidual.residualGroupFin` | 156-161 | — | Definition, `noncomputable` |
| `ConfinementResidual.residualGroupFin_card` | 163-174 | — | — |
| `ConfinementResidual.residualGroupFin_pretransitive` | 185-197 | — | — |
| `ConfinementResidual.ResidualSchemeModel` | 199-208 | — | Structure |
| `ConfinementResidual.residualSchemeModel_of_group` | 210-242 | — | Definition, `noncomputable` |

## Archive/ChainDescent-scratch/ScratchConfinementX3Reconcile.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3Reconcile.oneStepColouring_refines_indiv` | 105-124 | — | — |
| `ConfinementX3Reconcile.oneStep_cell_refines_setIndiv` | 126-135 | — | — |

## Archive/ChainDescent-scratch/ScratchConicCount.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConicCount.card_prod_eq` | 23-43 | The hyperbola count `#{(u,v) : u·v = a} = q − 1` for `a ≠ 0`. | — |
| `ConicCount.card_sq_sub_eq` | 45-63 | The difference-of-squares count `#{(x,z) : x²−z² = a}` equals the hyperbola count via `(x,z) ↦ (x−z, x+z)`. | — |
| `ConicCount.sum_quadraticChar_sq_sub` | 65-98 | **★** The crux character sum `∑ₓ χ(x² − a) = −1` (`a ≠ 0`, char ≠ 2) — proved elementarily, no additive Gauss sums. | — |
| `ConicCount.card_binary_form` | 100-150 | **★** The binary-conic count `#{w₁x² + w₂y² = c} = q − χ(−w₁w₂⁻¹)` for a nondegenerate diagonal form and `c ≠ 0` — Gauss-sum-free. | — |
| `ConicCount.card_sq_eq_le_two` | 152-170 | A quadratic `y² = k` has at most two roots in a field. | — |
| `ConicCount.exists_both_nonzero_solution` | 172-247 | **★** For `q ≥ 7`, a nondegenerate diagonal binary form has a level-`c` solution with both coordinates nonzero — yielding the three non-collinear points that discharge `hspan`. | — |

## Archive/ChainDescent-scratch/ScratchConicSpan.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConicSpan.map_ortho_comb` | 33-41 | The plane form is diagonal: for an orthogonal pair, `Q(x•a + y•b) = x²·Q a + y²·Q b`. | — |
| `ConicSpan.indep_smul_pair` | 43-52 | Scaling by nonzero scalars preserves pair linear independence. | — |
| `ConicSpan.exists_three_indep_levelset` | 54-88 | Three non-collinear points of the plane `Q`-level set `{v : Q v = c}` (orthogonal anisotropic pair, `c ≠ 0`, `q ≥ 7`) — the geometric input `hspan_of_two_indep` needs. | — |
| `ConicSpan.hspan_of_conic` | 90-149 | The `hspan` transport capstone (generic `c ≠ 0` case): for a vertex with anisotropic complement component, its isotropic set `Z(u)` affinely spans the plane `W` — the `hspan` hypothesis of `exactGram_of_sameWProfile`. | — |
| `ConicSpan.exists_orthogonal_decomp` | 151-187 | Every vertex splits as `u = u_W + u_⊥` (`u_W ∈ W`, `u_⊥ ∈ Wᗮ`) via the explicit diagonal projection — no `IsCompl`/restrict machinery. | — |
| `ConicSpan.hspan_or_singleton` | 189-208 | The `hspan` dichotomy for a bare vertex: either `u`'s complement component is isotropic (the singleton locus) or `Z(u)` affinely spans `W`. | — |
| `ConicSpan.exactGram_of_isotropic_complement` | 210-245 | Singleton-locus recovery: two isotropic-complement vertices with the same `W`-component have the same exact Gram to `{a,b}` — no spanning needed. | — |

## Archive/ChainDescent-scratch/ScratchCountTight.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `int_char_pointwise_tight` | 23-30 | **Tight per-element χ-inequality.** For `ca, cb ∈ {−1,0,1}`: `2·[ca=cb] ≤ 1 + [ca=0] + ca·cb`, coefficient `1` on `[ca=0]` (vs `2` in `int_char_pointwise`) — the pointwise seed of the tight small-q count. | — |
| `counting_identity_tight` | 32-55 | **Tight c₀ counting identity (ℤ).** `2·#{χ(a)=χ(b)} ≤ #{a=0} + |V| + ∑ χ(a)χ(b)` — strictly tighter than `counting_identity` (one copy of the zero count, not two). | — |
| `card_agree_le_tight` | 57-74 | **Tight count controlled by the magnitude (ℝ).** `2·#{χ(a)=χ(b)} ≤ #{a=0} + |V| + ‖T‖` — the small-q-tail replacement for `card_agree_le`, with a single `z_u`. | — |

## Archive/ChainDescent-scratch/ScratchDominatorForms.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `DominatorForms.polar_eq_qSub` | 52-59 | **The polar↔`Q`-value identity:** `polar Q x s = Q x + Q s − Q(x−s)` — the bridge between exact Gram data and the affine isometry scheme's `Q`-value-of-difference relation. | — |
| `DominatorForms.spanning_exactQ_determines` | 61-73 | **★ Full-base forced-triangle pinning (exact-`Q` form).** At a base spanning `⊤` with nondegenerate polar form, the exact `Q`-value profile (`Q t = Q t'` and `Q(t−s)=Q(t'−s)` for all `s ∈ S`) pins the vertex — the δ′-closure completion re-expressed in the scheme's own relation. | — |
| `DominatorForms.twoPoint_insufficient_unless_spans` | 75-85 | **The two-point premise is a projection of the full-base one.** The δ′ step's two-point data is the `S={α,β}` instance; when `{α,β}` does not span (always for `d ≥ 3`), `hspan` fails — the formal shadow of the dimensional wall (two constraints vs `d`). | — |

## Archive/ChainDescent-scratch/ScratchGramStratCharSum.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.gramStratCount_charsum` | 35-94 | **Off critical path (Piece 1b, raw expansion).** `gramStratCount u g · |K|⁴` as the four-fold Fourier sum of the count's four defining constraints (`Q z = g₀`, `polar z a = g₁`, `polar z b = g₂`, `Q(u−z)=0`), via Brick Aₖ. | — |
| `GramStrat.gramStrat_inner_normalize` | 96-110 | **Off critical path (Piece 1b).** Rewrites the inner z-exponent into the `Q`-plus-linear normal form `(r₀+r₃)·Qz + polar z (r₁•a+r₂•b−r₃•u) + r₃·Qu`, ready for the D1 Gauss bricks (with `u` inside the quadratic and phase). | — |
| `GramStrat.gramStratCount_charsum_normalized` | 112-125 | **Off critical path (Piece 1b, combined).** `gramStratCount · |K|⁴` as a Fourier sum whose inner z-sum is in the D1-ready normal form — the endpoint of Piece 1b feeding the fibre-sum route. | — |

## Archive/ChainDescent-scratch/ScratchGramStratConeEval.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.associated_separatingLeft_of_polarBilin_nondeg` | 37-46 | `(associated Q).SeparatingLeft` follows from `polarBilin` nondegeneracy (char ≠ 2, since `polarBilin = 2•associated`). | — |
| `GramStrat.isoConeSum_eval_even` | 48-143 | **Key theorem.** The even-dimension closed form of the isotropic-cone sum: `|K|·isoConeSum Q ψ y = |V|·𝟙[y=0] + G₁·(|K|·𝟙[Qy=0] − 1)` with `G₁ = ∑_x ψ(Q x)` (char ≠ 2, `Q` nondegenerate, even `finrank`). | — |
| `GramStrat.isoConeSum_ne_zero` | 145-194 | **Key theorem.** At even ambient dimension the cone sum `isoConeSum Q ψ y ≠ 0` for every `y` (char zero) — the non-vanishing that makes the factored transform separate the Gram. | — |

## Archive/ChainDescent-scratch/ScratchGramStratConeSep.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.isoConeSumSeparatesGram` | 38-183 | **Key theorem — the cone non-degeneracy, discharged.** `IsoConeSumSeparatesGram Q a b` holds (char ≠ 2, `2` invertible, finite-dimensional): the factored-transform equality determines the exact Gram to `{a,b}` and the plane flag. | — |
| `GramStrat.gramCountsEq_iff_stabOrbit_wittOnly` | 185-194 | **Capstone — `bᵢ=1` modulo only the Witt citation.** With the cone non-degeneracy proved, `SameGramStratCounts u u' ↔ StabOrbit` at a `GoodBase` of even dimension, carrying only `RefinedWittExtends`; the analytic content is axiom-clean and `ψ` is constructed internally. | — |

## Archive/ChainDescent-scratch/ScratchGramStratCount.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.gramK` | 44-46 | `u`'s exact Gram to the base `{a,b}` — the triple `(Q u, polar Q u a, polar Q u b)` that stratifies `z` in the round-3 count. | Definition |
| `GramStrat.gramStratCount` | 48-52 | The round-3 gram-stratified observable `T(u;g) = #{z : gramK z = g ∧ Q(u−z)=0}` — count of `z` isotropic-to-`u` in Gram-stratum `g`. Uses a genuine (non-`Classical`) `DecidablePred` so its filter shares the `GaussCount` toolkit's decidability instance. | Definition, `noncomputable` |
| `GramStrat.SameGramStratCounts` | 54-56 | The round-3 observable relation: `u, u'` have equal gram-stratified count profiles. | Definition |
| `GramStrat.polar_isometry` | 58-63 | A `μ=1` similitude (isometry) preserves the polar form. | — |
| `GramStrat.gramK_isometry` | 65-76 | A base-fixing isometry preserves `gramK` (it fixes `a, b` and preserves `Q` and `polar`). | — |
| `GramStrat.sameGramStratCounts_of_stabOrbit` | 78-106 | **Soundness (free).** `Stab({a,b})`-orbit-related vertices share the round-3 count profile (a base-fixing similitude is an isometry that reindexes the count), so the observable's cells are unions of orbits. | — |
| `GramStrat.GramCountsRecoverOrbit` | 108-113 | **The crux (K-non-degeneracy).** The predicate that equal round-3 count profiles recover the `Stab({a,b})`-orbit — the open Gauss content of Route A, probe-true and form-independent. | Definition |
| `GramStrat.gramCountsEq_iff_stabOrbit` | 115-121 | **Capstone (Piece 1a).** Soundness + the K-non-degeneracy crux give `SameGramStratCounts u u' ↔ StabOrbit` (`bᵢ=1`), targeting the orbit directly with no `SameExactGram`/Witt detour. | — |

## Archive/ChainDescent-scratch/ScratchGramStratEval.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.gramStrat_inner_eval_ne` | 34-54 | **Off critical path (Piece 1c(i), bulk `r₀+r₃≠0`).** Completes the square in the inner z-sum via Gauss Brick D1: `u` factors into the phase `ψ(r₃·Qu)` and the completed-square constant `Q(r₁•a+r₂•b−r₃•u)`. | — |
| `GramStrat.gramStrat_inner_eval_zero` | 55-76 | **Off critical path (Piece 1c(i), boundary `r₀+r₃=0`).** The quadratic part drops; the inner sum is the linear character sum, evaluating to `|V|` when the functional `polar Q · wᵣ` is zero (i.e. `wᵣ = 0` for nondegenerate `Q`), else `0`. | — |

## Archive/ChainDescent-scratch/ScratchGramStratGauss.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.countHat` | 55-58 | The `g`-Fourier transform of the round-3 count profile, `∑_g ψ(⟨t,g⟩)·gramStratCount u g`. Works over any `CommRing` and any `ψ` (no Gauss brick, no primitivity). | Definition, `noncomputable` |
| `GramStrat.isoConeSum` | 60-64 | **The isotropic-cone character sum** `∑_{w : Q w = 0} ψ(polar Q w y)` — the classical finite-field Gauss object carrying the remaining non-degeneracy. | Definition, `noncomputable` |
| `GramStrat.countHat_eq_of_sameGramStratCounts` | 66-73 | Trivial direction: equal count profiles give equal `countHat` transforms (`countHat` is `R'`-linear in the count). | — |
| `GramStrat.countHat_eq_isoSum` | 75-105 | The transform is the isotropy-stratified character sum `∑_{z : Q(u−z)=0} ψ(⟨t, gramK z⟩)` (pull the count into the sum fibrewise over `gramK`). | — |
| `GramStrat.countHat_factor` | 107-142 | **Key theorem — the factorization (analytic core of `GramCountsRecoverGram`).** `countHat u t = ψ(⟨t, gramK u⟩) · isoConeSum Q ψ (t₀•u + t₁•a + t₂•b)`: `u`'s exact Gram sits in the phase, the complement/flag data in the cone sum. | — |

## Archive/ChainDescent-scratch/ScratchGramStratGaussReduce.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.gramK_eq_iff_sameExactGram` | 42-60 | `gramK u = gramK u'` iff `SameExactGram Q {a,b} u u'` — the observable's Gram triple is exactly the exact-Gram data to `{a,b}`. | — |
| `GramStrat.IsoConeSumSeparatesGram` | 62-75 | **The honest single open Gauss statement.** At a `GoodBase`, equality of the factored transforms `ψ(⟨t,gramK u⟩)·isoConeSum(…)` for all `t` forces `gramK u = gramK u'` and the plane flag — stated purely via the classical `isoConeSum`, no `gramStratCount`. | Definition |
| `GramStrat.gramCountsRecoverGram_of_isoConeSep` | 77-103 | **The reduction (primitive character discharged).** The cone non-degeneracy `IsoConeSumSeparatesGram` discharges `GramCountsRecoverGram`; a primitive additive character `ψ` is constructed internally (Mathlib `FiniteField.primitiveChar`), so no `hψ` is carried. | — |
| `GramStrat.gramCountsEq_iff_stabOrbit_of_isoConeSep` | 105-113 | **Capstone.** `SameGramStratCounts u u' ↔ StabOrbit` at a `GoodBase` of even dimension, modulo the classical `IsoConeSumSeparatesGram` and the carried `RefinedWittExtends`. | — |

## Archive/ChainDescent-scratch/ScratchGramStratInvert.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.gsum_orthogonality` | 40-88 | **Off critical path.** `K³` character orthogonality: `∑_g ψ(⟨t,g⟩) = |K|³` if `t = 0`, else `0`. | — |
| `GramStrat.innerZ` | 90-95 | **Off critical path.** The surviving inner z-sum of the round-3 character sum at dual variable `r` (the fibre-sum route's 1c(i) inner sum, kept opaque as a `def`). | Definition, `noncomputable` |
| `GramStrat.gramStrat_transform_eval` | 97-126 | **Off critical path (fibre-sum route).** The evaluated `g`-transform: `g`-orthogonality collapses the `(r₀,r₁,r₂)`-sum onto the fibre `r₀₁₂ = s`, leaving only the `innerZ` fibre sum weighted by `|K|³`, with `u` living entirely in `innerZ`. | — |
| `GramStrat.sameGramStratCounts_transform` | 128-143 | **Off critical path.** Equal round-3 count profiles give equal `innerZ` fibre sums for every `s` — the Gauss-sum equality the fibre-sum inversion would consume. | — |

## Archive/ChainDescent-scratch/ScratchGramStratOrbit.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.stabOrbit_imp_span_iff` | 55-72 | The plane-membership flag `u ∈ span{a,b}` is orbit-sound: `Stab({a,b})`-orbit-related vertices agree on it (either membership forces `u = u'`), making `RefinedWittExtends`'s flag hypothesis the tight converse of soundness. | — |
| `GramStrat.GoodBase` | 74-82 | The good span-dim-2 base conditions: `a, b` orthogonal anisotropic, char ≠ 2, and `Q.polarBilin` nondegenerate. Carried as the antecedent of both reduction predicates (without it the bare `∀ Q a b` forms are false). | Definition |
| `GramStrat.GramCountsRecoverGram` | 84-92 | **The open Gauss content (probe-true).** At a `GoodBase`, the round-3 count profile determines the exact Gram to `{a,b}` and the plane-membership flag. | Definition |
| `GramStrat.RefinedWittExtends` | 94-103 | **The carried, known-true Witt content.** At a `GoodBase`, exact Gram to `{a,b}` plus the plane flag give the same `Stab({a,b})`-orbit — Witt extension on the nondegenerate `W^⊥`, cited only in this true `GoodBase` form. | Definition |
| `GramStrat.gramCountsRecoverOrbit_of` | 105-113 | **The reduction.** `GramCountsRecoverGram` (Gauss) + `RefinedWittExtends` (Witt) compose to the crux `GramCountsRecoverOrbit` at a `GoodBase`. | — |
| `GramStrat.gramCountsEq_iff_stabOrbit_refined` | 115-122 | **Capstone.** `SameGramStratCounts u u' ↔ StabOrbit` at a `GoodBase`, modulo the two isolated pieces `GramCountsRecoverGram` and `RefinedWittExtends`. | — |

## Archive/ChainDescent-scratch/ScratchGramStratWLBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GramStrat.ColorRefinesGramK` | 41-44 | The (necessary) fineness hypothesis of the WL bridge: the colouring `C` refines `gramK` (equal colour forces equal exact Gram to `{a,b}`). Weaker than `C∞ = orbits`; this is the open WL-dimension residual. | Definition |
| `GramStrat.sameGramStratCounts_of_sameClassCounts` | 46-102 | **Piece 2 — the WL bridge.** If `C` refines `gramK`, equal 1-WL class-count profiles give equal gram-stratified count profiles. | — |
| `GramStrat.colorEq_iff_stabOrbit_wittOnly` | 104-122 | **Capstone (assembly).** At a `GoodBase` of even dimension, for a refinement-invariant, 1-WL-stable colouring refining `gramK`, the WL colour equality is exactly the orbit relation: `C u = C u' ↔ StabOrbit`, modulo `{ColorRefinesGramK, IsWLStable, ObsInvariant, RefinedWittExtends}`. The whole Gauss/analytic content is discharged axiom-clean. | — |

## Archive/ChainDescent-scratch/ScratchJointCountInvariant.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `JointCountInvariant.isoClassK_similitude` | 37-49 | **A similitude preserves the isotropy class:** `isoClassK Q (g w) = isoClassK Q w`. | — |
| `JointCountInvariant.isoClassK_similitude_symm` | 51-58 | **The inverse form:** `isoClassK Q (g⁻¹ w) = isoClassK Q w`. | — |
| `JointCountInvariant.jointIsoCountK_similitude_fix` | 59-93 | **★ Soundness — a base-fixing similitude preserves the joint isotropy count:** if `g` fixes every point of `S` then `jointIsoCountK Q (g u) S = jointIsoCountK Q u S`. | — |
| `JointCountInvariant.jointCountProfile` | 94-101 | **The sub-config joint-count profile observable:** `u ↦ (S' ↦ jointIsoCountK Q u S')` over sub-configs `S' ⊆ S₀` — the richer profile route A separates on at a span-dim-2 base. | Definition, `noncomputable` |
| `JointCountInvariant.obsInvariant_jointCountProfile` | 102-115 | **★ `ObsInvariant` for the joint-count profile.** The sub-config joint-count profile is `Stab(S₀)`-invariant, discharging the FREE half of `obsEq_iff_stabOrbit` and reducing route A at a span-dim-2 base to `WallKernelFor (jointCountProfile Q S₀ ·) Q ↑S₀`. | — |

## Archive/ChainDescent-scratch/ScratchOrbitBaseCase.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `OrbitBaseCase.Similitude` | 42-48 | A similitude of `Q`: a linear equiv `g` with `Q (g x) = mult · Q x`, `mult ≠ 0`. An isometry is `mult = 1`. | Structure |
| `OrbitBaseCase.affinePolar_empty_base_one_orbit` | 50-53 | **Depth 0** — the whole vertex set is one orbit (translations): `∀ v w, ∃ t, v + t = w`. `CellsAreOrbits` at `S = ∅`, free. | — |
| `OrbitBaseCase.mult_eq_one_of_fixes_anisotropic` | 55-63 | **The delimiter.** A similitude fixing an anisotropic vector (`Q v ≠ 0`) has `mult = 1`. Once an anisotropic vector is pinned, residual similitudes are isometries. | — |
| `OrbitBaseCase.mult_eq_one_of_fixes_span_anisotropic` | 65-77 | Delimiter, span form: fixing a set whose span contains an anisotropic vector forces `mult = 1` — so multiplier freedom in `Stab(S)` requires `span S` totally isotropic. | — |
| `OrbitBaseCase.WittConeTransitive` | 79-83 | **Isolated Witt input**: isometries act transitively on nonzero isotropic vectors. Discharged (mod the residual) in `ScratchWittCone`. | Definition |
| `OrbitBaseCase.neighborSphere_zero_eq_isotropic` | 85-88 | The graph-neighbours of `0` are exactly the nonzero isotropic vectors (`Q(v−0)=0 ⟺ Q v = 0`). | — |
| `OrbitBaseCase.depth1_isotropic_sphere_one_orbit` | 90-97 | **Depth 1** — the isotropic neighbour sphere is one isometry-orbit, given `WittConeTransitive`. The second base rung. | — |
| `OrbitBaseCase.scalarEquiv` | 108-112 | The scalar automorphism `x ↦ l • x` (`l ≠ 0`) as a linear equiv, and its apply lemma. | Definition |
| `OrbitBaseCase.scalarEquiv_apply` | 114-116 | — | `@[simp]` |
| `OrbitBaseCase.scalarSimilitude` | 118-125 | The scalar similitude `x ↦ l • x`, multiplier `l²`, fixing the origin — realizes every square multiplier in `Stab(0)` with no Witt input. | Definition |
| `OrbitBaseCase.StabOrbit` | 127-129 | The `Stab(S)`-orbit relation: `w'` reachable from `w` by a similitude fixing `S` pointwise. | Definition |
| `OrbitBaseCase.stabOrbit_preserves_norm_of_anisotropic_base` | 131-142 | **Wall side (orbit level).** At an anisotropic base, every `Stab(S)`-orbit preserves the exact norm `Q` (`mult = 1`) — orbits are norm-fine, strictly finer than square-class cells. The open core located at the orbit level. | — |
| `OrbitBaseCase.stabOrbit_zero_base_scales` | 144-157 | **Free side at the origin (no Witt).** `l • w` is in the `Stab({0})`-orbit of `w` with `Q(l•w) = l²·Q w` — origin-base orbits are square-class-coarse, matching refinement. | — |
| `OrbitBaseCase.TotallyIsotropic` | 169-171 | A base `S` is totally isotropic when `Q` vanishes on `span S`. | Definition |
| `OrbitBaseCase.MultiplierRealizable` | 173-176 | `Stab(S)` realizes every nonzero multiplier (the multiplier freedom the free prefix runs on). | Definition |
| `OrbitBaseCase.WittRealizes` | 178-182 | **Carried Witt-decomposition input (W-dec)**: over every totally-isotropic base, all multipliers are realizable. | Definition |
| `OrbitBaseCase.stabOrbit_realizable_base_scales` | 184-194 | **Increment 2** — free-prefix orbit coarsening: given `MultiplierRealizable Q S`, the `Stab(S)`-orbit of `w` reaches norm `μ·Q w` for every `μ ≠ 0`. | — |
| `OrbitBaseCase.not_multiplierRealizable_of_anisotropic` | 196-206 | The delimiter at predicate level: `MultiplierRealizable Q S` fails once `S` carries an anisotropic vector (with a `μ ≠ 0, 1` witness). The free/​wall boundary. | — |
| `OrbitBaseCase.stabOrbit_totallyIsotropic_scales` | 208-215 | **Increment 2 capstone** — free-prefix orbit coarsening over any totally-isotropic base, modulo the carried `WittRealizes`. | — |

## Archive/ChainDescent-scratch/ScratchPencilBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `finrank_polarRad_eq_finrankKer` | 26-73 | **The corank bridge.** The `finrank` of the polar-radical of `G` equals the `finrank` of the kernel of its Gram matrix's `mulVecLin` — reconciling the `|radical|` magnitude with the corank-stratified `sum_finrankKer_le` budget. | — |

## Archive/ChainDescent-scratch/ScratchPencilCorank.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `pencilPoly` | 43-45 | The matrix pencil `A + X·B` packaged as a single matrix over `K[X]` (each entry `C(A i j) + X·C(B i j)`); the object whose determinant carries the corank-multiplicity data. | Definition, `noncomputable` |
| `pencilPoly_mul_map` | 47-51 | Right-multiplying the pencil `pencilPoly A B` by a constant matrix `Q` yields the pencil of the products, `pencilPoly (A*Q) (B*Q)`. | — |
| `pow_card_dvd_pencilDet_of_cols` | 53-101 | **The column-factoring core.** If `Q` is invertible with its `S`-columns in `ker(A + t₀·B)`, then `(X − C t₀)^|S|` divides `det(pencilPoly A B)` — the divisibility that converts corank into a root of the pencil determinant. | — |
| `exists_cols_ker` | 103-142 | Builds an invertible matrix `Q` and index set `S` of size `finrank ker(M₀)` whose `S`-columns lie in `ker(M₀.mulVecLin)` (kernel basis plus a complement), supplying the input to `pow_card_dvd_pencilDet_of_cols`. | — |
| `finrankKer_le_rootMult` | 144-152 | **CORANK ≤ ROOT-MULTIPLICITY** (the corank-tightening crux). For the pencil `A + X·B` with nonzero determinant, the corank `finrank ker(A + t₀·B)` is at most the multiplicity of `t₀` as a root of `det(A + X·B)`. | — |
| `pencilDet_natDegree_le` | 154-159 | The pencil determinant `det(A + X·B)` has degree at most `d`. | — |
| `sum_finrankKer_le` | 161-179 | **∑ corank ≤ d** (the corank-stratified budget). Over any finite set of ratios `t`, the total corank `∑ finrank ker(A + t·B)` is at most `d` — the fact that breaks the uniform-bucket `d` factor. | — |
| `pencilPoly_det_eval` | 181-189 | Evaluating the pencil determinant at `t₀` recovers `det(A + t₀·B)`. | — |
| `pencilPoly_det_ne_zero` | 191-216 | **Good anchor ⟹ pencil determinant nonzero.** If some ratio makes `y•A + z•B` nonsingular, then `det(A + X·B)` is not the zero polynomial (the hypothesis needed to apply the corank lemmas). | — |
| `pow_sum_mul_bound` | 218-249 | **Multiplicative bound** (`s ≥ 2`): a sum of `s`-powers with exponents `≥ 1` is at most `s` raised to the sum of the exponents. | — |
| `concentration_bound` | 251-277 | **CONCENTRATION** (the bucket arithmetic). With `s ≥ 2`, exponents `1 ≤ c t ≤ D−1`, and `∑ c t ≤ D`, gives `∑ s^(c t) ≤ 2·s^(D−1)` — turning the corank-`(d−1)` worst case into a constant factor rather than a `d`-fold one. | — |

## Archive/ChainDescent-scratch/ScratchPencilCorank2.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `polar_pairForm` | 23-35 | The polar of `pairForm Q a`, expanded as `4·Q a·polar Q x h − 2·polar Q x a·polar Q h a`. | — |
| `polar_pencil_pairForm` | 37-49 | The polar of the pencil `F = y•pairForm Q a + z•pairForm Q b`, fully expanded in terms of `polar Q`. | — |
| `pencil_polarRad_finrank_le` | 51-231 | **The geometric corank cap.** For the pencil `y•pairForm Q a + z•pairForm Q b` with `a, b` linearly independent, `y, z ≠ 0`, nondegenerate `Q.polarBilin` (char ≠ 2, `finrank V ≥ 4`), the polar-radical has corank at least 2: `finrank (polarRad F) ≤ finrank V − 2`. | — |
| `single_polarRad_finrank_le` | 233-277 | **The single-form corank-1 cap (the `z_u` sibling of the pencil cap).** For nondegenerate `Q.polarBilin` and non-isotropic anchor `Q a ≠ 0`, `polarRad (pairForm Q a) ⊆ span{a}` so `finrank ≤ 1` — tightening the `z_u` zero-count term from `n/√q` to `√n·√q` and its threshold from `q ≥ 256` to `q ≥ 16`. | — |

## Archive/ChainDescent-scratch/ScratchPencilRegroup.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ker_smul_mulVecLin` | 25-30 | Scaling a matrix by a nonzero constant preserves the kernel of its `mulVecLin`. | — |
| `finrankKer_ratio` | 32-39 | **Scale-invariance of the corank along a ratio.** For `y ≠ 0`, the corank of the pencil member `y•A + z•B` equals that of the normalized member `A + (z/y)•B`. | — |
| `radicalCard_eq_pow` | 41-57 | **The radical cardinality as a corank power.** The radical-count of the pencil member `y•P + z•R` equals `|K|^{corank}` of the normalized Gram matrix `A + (z/y)•B` — connecting the `ScratchTBound` magnitude to the ratio corank. | — |
| `corank_ratio_eq` | 59-66 | The normalized-Gram corank at a ratio equals the polar-radical dimension `finrank (polarRad (y•P + z•R))` (finrank form of `radicalCard_eq_pow`). | — |
| `sum_comp_ratio_le` | 68-81 | **Fiber-collapse bound.** For a nonneg `h` factoring through `ρ`, the sum of `h ∘ ρ` over `S` is at most `N` times the ratio-sum, where `N` bounds each fiber's size. | — |
| `fiber_fst_card_le` | 83-98 | Every ratio-fiber `{x ∈ S : x.2/x.1 = t}` (nonzero first coordinates) has at most `|K|` elements, injecting into `K` via the first coordinate. | — |
| `sqrt_natpow` | 100-104 | `√(a^c) = (√a)^c` for `a ≥ 0`. | — |
| `pencilDet_ne_zero_of_good` | 106-119 | **Good anchor ⟹ pencil determinant nonzero (the `hgood → hp` bridge).** A nondegenerate pencil member (`polarRad (y•P + z•R) = ⊥`) makes the Gram-matrix pencil determinant nonzero, supplying the `deg_bucket_le`/corank hypotheses. | — |
| `deg_bucket_le` | 121-232 | **The corank-stratified degenerate bucket bound (A-assembly).** The `ScratchTBound` degenerate-bucket sum `∑ √(|V|·|radical|)` is at most `2·|K|·(|V|/√|K|)` — the `d`-free bound that drops `ScratchBucket.c0_le`'s `hq2` threshold on `q`. | — |

## Archive/ChainDescent-scratch/ScratchPlanePin.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `PlanePin.zSet` | 38-41 | The `zSet` observable `zSet Q W u = {w ∈ W : Q(u−w)=0}` — `u`'s isotropic set in the plane `W`; the observable route A separates on. | Definition |
| `PlanePin.zSet_eq_iff_isoSetEq` | 43-60 | `zSet u = zSet u' ↔ IsoSetEq` — the observable's equality relation is exactly same-isotropic-set-in-`W`. | — |
| `PlanePin.zSet_invariant` | 62-80 | `zSet` is `Stab({a,b})`-invariant (`ObsInvariant`) — soundness, free. | — |
| `PlanePin.isoSetEq_symm` | 82-84 | `IsoSetEq` is symmetric. | — |
| `PlanePin.sameExactGram_symm` | 86-89 | `SameExactGram` is symmetric. | — |
| `PlanePin.wallKernel_zSet_anisotropic` | 91-114 | On an anisotropic plane, `WallKernelFor zSet` holds (`zSet u = zSet u' ⟹ SameExactGram` to `{a,b}`), composing both Step-B branches with no counting. | — |
| `PlanePin.zSetEq_iff_stabOrbit_anisotropic` | 116-128 | The `zSet`-observable capstone: on an anisotropic plane, `zSet u = zSet u' ↔ StabOrbit` (`bᵢ=1` for `zSet`), isolating the whole open route-A content as "1-WL-stable refines `zSet`". | — |

## Archive/ChainDescent-scratch/ScratchPlanePinInduction.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `PlanePinInduction.SeparatedBy` | 52-60 | One-round `χ(pairForm)` separation of two plane points via an anchor pair drawn from a pinned set `P` — the inner body of `ChiProfileSeparatesPlane` with anchors ranging over a set rather than a fixed base. Part of the plane-pinning line (SUPERSEDED; only the `WLWiring` core survives). | Definition |
| `PlanePinInduction.SeparatedBy.mono` | 62-66 | `SeparatedBy` is monotone in the anchor set `P` — more pinned anchors only help. | — |
| `PlanePinInduction.SeparatedBy.symm` | 68-73 | `SeparatedBy` is symmetric in the two plane points, using the same anchors. | — |
| `PlanePinInduction.seed` | 75-76 | The pinning-closure seed — the span-dim-2 base `{0,a,b}`, pinned by individualisation. | Definition |
| `PlanePinInduction.mem_seed_iff` | 78-79 | Membership in `seed a b` unfolds to `x = 0 ∨ x = a ∨ x = b`. | — |
| `PlanePinInduction.pinStep` | 81-85 | One round of pinning — adjoin every `w ∈ W` that `SeparatedBy P` distinguishes from every other plane point. | Definition |
| `PlanePinInduction.pinIter` | 87-91 | The `ℕ`-indexed pinning closure (`pinIter 0 = {0,a,b}`; each round applies `pinStep`), monotone increasing. | Definition |
| `PlanePinInduction.PinClosure` | 93-95 | `x` is pinned if it enters `pinIter` at some round. | Definition |
| `PlanePinInduction.PlanePinnable` | 97-102 | The inductive Step-C target: the pinning closure reaches all of the plane `W`. The plane-pinnability predicate — plane-pinning line SUPERSEDED/REFUTED by probe. | Definition |
| `PlanePinInduction.pinClosure_of_mem_pinIter` | 104-107 | Membership in any `pinIter n` implies `PinClosure`. | — |
| `PlanePinInduction.sep_of_mem_pinIter` | 109-123 | A pinned non-seed point carries its separation certificate: at some round it was `SeparatedBy (pinIter m)` from every other plane point. | — |
| `PlanePinInduction.chiProfileSeparatesPlane_of_pinnable` | 125-166 | Composition: `PlanePinnable` (plus base-pair side conditions and `S₀ ⊇ pinned`) yields the one-shot `ChiProfileSeparatesPlane Q S₀ W`. | — |
| `PlanePinInduction.count_profile_separates_of_pinnable` | 168-189 | End-to-end (count level): `PlanePinnable` makes distinct plane points differ in `jointIsoCountK` at some base pair. | — |

## Archive/ChainDescent-scratch/ScratchPlaneSep.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `PlaneSep.plane_count_sep` | 34-51 | **★** Per-round separator: plane points with differing `χ(pairForm)` to a base pair `{t,t₀}` have different joint isotropy counts — the seal's per-pair lever fires for plane-point pinning. | — |
| `PlaneSep.ChiProfileSeparatesPlane` | 53-66 | The accumulation kernel: the `χ(pairForm)`-profile over base pairs separates the plane (distinct plane points differ at some pair). The sole route-A obligation of the plane-pinning line (OPEN; that line since SUPERSEDED/REFUTED by probe). | Definition |
| `PlaneSep.count_profile_separates_of_kernel` | 68-84 | **★** Reduction: `ChiProfileSeparatesPlane` makes the joint-count observable injective on `W` (distinct plane points differ in `jointIsoCountK` at some base pair). | — |

## Archive/ChainDescent-scratch/ScratchRoute2.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `chi_norm_le` | 24-31 | `‖χ y‖ ≤ [y ≠ 0]` for the ℂ-valued quadratic character — the χ-weight vanishes on zero and is `≤ 1` elsewhere. | — |
| `sum_chi_indicator` | 33-40 | `∑_y [y ≠ 0] = |K| − 1` — the row/column count feeding the `(q−1)²` factor of the triangle bound. | — |
| `normT_triangle` | 48-132 | **Route 2 triangle `T`-bound (piece 2).** For a good anchor (`t₀−u, t₀−v` independent, `Q` nondegenerate, `d ≥ 4`): `q·T ≤ (q−1)²·q^{d−1}`, i.e. `T ≤ (1−1/q)²·|V|`, with NO threshold `hq3`. | — |
| `c0_le_route2` | 134-222 | **Route 2 tail capstone (piece 4).** For a good anchor (`d ≥ 4`, `|K| ≥ 3` odd) the agreement count satisfies `4q²·NS ≤ (4q²−1)·|V|`, i.e. `NS ≤ (1 − 1/(4q²))·|V| < |V|` — closing the odd-char small-q tail uniformly with NO threshold. | — |

## Archive/ChainDescent-scratch/ScratchRoute2Arith.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `c0_route2_arith` | 5-51 | **Route 2 tail arithmetic.** From the tight count, the corank-1 zero-count, the triangle `T·q² ≤ (q−1)²·n`, and `q⁴ ≤ n`, `q ≥ 3`, derives `4q²·NS ≤ (4q²−1)·n` — the clean `δ = 1/(4q²)` gap with `√` only internal. | — |

## Archive/ChainDescent-scratch/ScratchSimilitudeCap.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SimilitudeCap.quad_smul_apply` | 48-51 | Scaling the form scales its values: `(c • Q) x = c * Q x`. | `@[simp]` |
| `SimilitudeCap.polar_smul` | 53-56 | Scaling the form scales its polar: `polar (c • Q) s a = c * polar Q s a`. | — |
| `SimilitudeCap.adj_smul_iff` | 58-61 | **The similitude cap (T1).** The affine-polar adjacency `Q x = 0` is unchanged by scaling the form (`c ≠ 0`). | — |
| `SimilitudeCap.affinePolarAdj_smul_eq` | 63-68 | **The graph is identical for `Q` and `c•Q`.** The adjacency relation `(x,y) ↦ Q(x−y)=0` is *literally equal*, so the graph determines `Q` only up to scaling — any isomorphism-invariant of a vertex pair must be invariant under `Q ↦ c•Q`. | — |
| `SimilitudeCap.pairForm_smul_apply` | 70-75 | The pair invariant scales by `c²`: `pairForm (c•Q) a s = c² · pairForm Q a s`. | — |
| `SimilitudeCap.chi_sq_mul` | 77-85 | `χ(c² · v) = χ(v)` for `c ≠ 0` — the square multiplier is invisible to the quadratic character. | — |
| `SimilitudeCap.chi_pairForm_smul` | 87-92 | **The square class is a graph invariant (T2).** `χ(det G₂) = χ(pairForm)` is unchanged by scaling the form (`c²` killed by `χ`) — why the canonizer's pair observable is well-defined on the graph (= on the scaling class of `Q`). | — |
| `SimilitudeCap.chi_singleton_smul` | 94-99 | **The singleton square class is NOT a graph invariant (T3a).** `χ((c•Q) a) = χ(c)·χ(Q a)` flips by `χ(c)` — the formal proof of the empirical "singleton `Z_u({t})` is binary" finding (only the `χ(c)`-invariant fact `Q=0` survives). | — |
| `SimilitudeCap.pairForm_value_not_invariant` | 101-106 | **The exact value is NOT a graph invariant (T3b).** The exact pair value scales by `c²`, so presentations `Q`, `c•Q` of the *same graph* disagree on it whenever `c² ≠ 1` — no isomorphism-invariant procedure (refinement of any dimension, or Route C) recovers the exact form value, only its square class. | — |

## Archive/ChainDescent-scratch/ScratchSpanDim2Geom.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SpanDim2Geom.map_sub_eq` | 34-39 | `Q(u − w) = Q u + Q w − polar Q u w`. | — |
| `SpanDim2Geom.norm_diff_affine` | 41-46 | The affine difference identity `Q(u−w) − Q(u'−w) = polar Q (u'−u) w + (Q u − Q u')`; the quadratic part cancels, leaving an affine function of `w`. | — |
| `SpanDim2Geom.exactGram_of_sameWProfile` | 48-102 | **★** The span-dim-2 geometric recovery core: same isotropic-set profile over `W` (one-directional containment) plus `Z(u)` affinely spanning `W` ⟹ same exact Gram to `{a,b}` — `d`-independent, no Gauss, no Witt. | — |

## Archive/ChainDescent-scratch/ScratchSpanDim2Recovery.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SpanDim2Recovery.ObsInvariant` | 42-46 | The predicate "`obs` is `Stab(S)`-invariant": every `S`-fixing similitude preserves the observable (characterises what refinement sees). | Definition |
| `SpanDim2Recovery.stabOrbit_imp_obsEq` | 48-53 | Soundness (free half): same `Stab(S)`-orbit implies same observable, so `obs`-cells are unions of orbits. | — |
| `SpanDim2Recovery.obsEq_iff_stabOrbit` | 55-65 | **★** The reduction capstone: invariance + the wall kernel for `obs` + carried Witt give `obs t = obs t' ↔ StabOrbit` — i.e. `obs`-cells ARE the orbits (`bᵢ=1`). | — |
| `SpanDim2Recovery.SpanDim2Recovers` | 67-74 | Bundles the two route-A inputs at a base `S` (observable invariance + wall kernel + Witt), yielding `bᵢ=1`. | Structure |
| `SpanDim2Recovery.obsEq_iff_stabOrbit_of_recovers` | 76-81 | Packaged capstone: from `SpanDim2Recovers`, the `obs`-cell relation is exactly the `Stab(S)`-orbit relation. | — |

## Archive/ChainDescent-scratch/ScratchSpanDim2Span.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SpanDim2Span.hspan_of_two_indep` | 36-73 | **★** The combinatorial bridge: in a 2-dim plane, three isotropic points with two linearly independent difference vectors make `Z − w₀` span `W` — the `hspan` hypothesis of `exactGram_of_sameWProfile`; pure linear algebra. | — |

## Archive/ChainDescent-scratch/ScratchSpanDimBound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SpanDimBound.polar_eq_of_mem_span_singleton` | 39-48 | Polar collapses on a line: for `s ∈ span{a}`, `polar Q t s` is determined by the single scalar `polar Q t a`. | — |
| `SpanDimBound.stabOrbit_cover_card_le_line` | 50-80 | **★** The span-dim-1 orbit-multiplicity bound `bᵢ ≤ q²` (POLY), unconditional mod Witt — sharpens the `|K|^{|S|+1}` cover to `|K|²` by collapsing the polar profile onto the line's scalar. The PROVEN half of the recovery route. | — |

## Archive/ChainDescent-scratch/ScratchTBoundCorank.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `normT_bucket_bound_corank` | 20-96 | **Corank-stratified `|T|` bound (step C).** `|K|·‖T‖ ≤ |K|²·√|V| + 2·|K|·(|V|/√|K|)` — the degenerate deg bucket coefficient is the constant `2`, not `d`, via the corank-stratified `deg_bucket_le`. | — |
| `c0_le_const` | 98-108 | **The `c₀ ≤ ¾` arithmetic with the constant deg coefficient — no `hq2`.** Specializing `c0_le` at `dR := 2` makes its `d`-dependent threshold collapse into the already-present `q ≥ 256`, so only `d ≥ 3` and `q ≥ 256` bind. | — |
| `c0_le_threequarters_corank` | 110-190 | **THE per-anchor `c₀ ≤ ¾` bound — corank-tightened (no `hq2`).** Removes the `64·d² ≤ q` threshold by using the corank-stratified deg bucket, dropping `VO⁻₄(q)` from `q ≥ 1024` to `q ≥ 256`. | — |

## Archive/ChainDescent-scratch/ScratchTBoundCorank2.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `le_two_pow_sub_two` | 27-35 | The arithmetic helper `D ≤ 2^(D−2)` for `D ≥ 4`, used in the all-corank-1 case of the cap-`d−2` concentration bound. | — |
| `concentration_bound2` | 37-84 | **Concentration, cap `D−2`.** For `s ≥ 2` and exponents in `[1, D−2]` summing to `≤ D`, `∑ s^(c t) ≤ 2·s^(D−2)` — one `√q` sharper than `concentration_bound`, the arithmetic behind Route 0's threshold drop. | — |
| `deg_bucket_le2` | 86-186 | **Route 0 cap-`d−2` degenerate bucket.** For the pencil `y•pairForm Q p + z•pairForm Q r` with independent `p, r` and nondegenerate polar form, the degenerate-bucket sum is `≤ 2·|V|` — one `√q` sharper than `deg_bucket_le`, via the rank-2 corank cap `pencil_polarRad_finrank_le`. | — |
| `c0_le2` | 188-226 | **Route 0 `c₀ ≤ ¾` arithmetic at threshold `q ≥ 16`.** Feeding the cap-`d−2` deg term `2n/q` and the corank-1 `z_u` bound, closes `NS ≤ ¾·n` for `q ≥ 16` — dropping `c0_le_const`'s `q ≥ 256`. | — |
| `normT_bucket_bound_corank2` | 228-294 | **Route 0 `|T|` bound.** `|K|·‖T‖ ≤ |K|²·√|V| + 2·|V|` — the degenerate deg bucket is now `2·|V|` (via `deg_bucket_le2`), one `√q` smaller than `normT_bucket_bound_corank`. | — |
| `c0_le_threequarters_corank2` | 296-376 | **THE per-anchor `c₀ ≤ ¾` bound — Route 0 (threshold `q ≥ 16`).** Drops `c0_le_threequarters_corank`'s `q ≥ 256` to `q ≥ 16`, at the cost of new hypotheses `d ≥ 4`, `t₀−u, t₀−v` independent, `Q.polarBilin` nondegenerate, and non-isotropic anchor. | — |

## Archive/ChainDescent-scratch/ScratchWLClassCounts.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `WLClassCounts.iso3` | 51-54 | **The 3-valued isotropy relation over `V`** that 1-WL sees on the forms graph: `0` (self), `1` (isotropic nonzero), `2` (anisotropic); the abstract-`V` analogue of `isoClassK`. | Definition, `noncomputable` |
| `WLClassCounts.iso3_similitude` | 56-70 | A similitude preserves `iso3` (fixes `0`, scales `Q` by a nonzero multiplier so preserves `Q(·)=0`). | — |
| `WLClassCounts.classCount` | 71-74 | **The 1-WL neighbourhood count of colour class `c` at relation `k`:** `#{z : C z = c ∧ iso3 Q (u−z) = k}` — counting against a whole colour class, the power the singleton-anchor closure lacked. | Definition, `noncomputable` |
| `WLClassCounts.SameClassCounts` | 76-79 | **The class-count profile relation:** `u, u'` have equal 1-WL class-count profiles — the iterated observable the wall kernel runs against. | Definition |
| `WLClassCounts.IsWLStable` | 81-84 | **`C` is 1-WL-stable (equitable):** equal colour ⟹ equal class-count profile, the fixpoint property of the stable colouring `C^∞`; carried as a property of the actual WL colouring. | Definition |
| `WLClassCounts.ClassCountsSeparateGram` | 86-92 | **★ THE CORRECT OPEN PREDICATE (the frontier).** The class-count profile separates the exact Gram — the iterated colour-class instance of the wall kernel, replacing the false singleton-anchor `PlanePinnable`; proving it is the WL-dimension frontier. | Definition |
| `WLClassCounts.wallKernelFor_sameClassCounts` | 94-96 | `ClassCountsSeparateGram` is literally `WallKernelFor` for the class-count observable — the intended instance. | — |
| `WLClassCounts.wallKernel_of_wlStable` | 98-103 | **Stable `C` + class-count separation ⟹ the colour-equality wall kernel.** Equal colour ⟹ equal class-count profile ⟹ equal exact Gram. | — |
| `WLClassCounts.colorEq_iff_stabOrbit` | 105-114 | **★ `bᵢ=1` for the 1-WL-stable colouring — the corrected wiring capstone.** With `C` refinement-invariant, WL-stable, its class-counts separating the exact Gram, and the carried Witt extension, `C u = C u' ↔ StabOrbit`; the open content is the single predicate `ClassCountsSeparateGram`. | — |
| `WLClassCounts.sameClassCounts_of_stabOrbit` | 116-139 | **Soundness (FREE) — `SameClassCounts` is a graph invariant.** A `Stab(S)`-invariant `C` gives orbit-related vertices equal class-count profiles, so class-count cells are always unions of orbits. | — |

## Archive/ChainDescent-scratch/ScratchWLWiring.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `WLWiring.IsColorSingleton` | 48-49 | `w` is a colour-singleton under `C`: the unique vertex of its colour (individualised / pinned). | Definition |
| `WLWiring.ReadsSingletonIsotropy` | 61-66 | **The minimal 1-WL property the wiring needs.** Interface field: a refinement colouring `C` reflects the isotropy indicator `Q(·−w)=0` to any colour-singleton anchor `w`, so `C u` determines whether `Q(u−w)=0`. | Structure |
| `WLWiring.PinsPlane` | 68-69 | **`C` pins the plane `W`:** every plane point is a colour-singleton (Insight 4, `C^∞` pins `W`). | Definition |
| `WLWiring.refines_zSet_of_pinsPlane` | 71-78 | **`ReadsSingletonIsotropy` + `PinsPlane` ⟹ `C` refines `zSet`.** Equal colour forces the isotropic sets in the pinned plane `W` to coincide. | — |
| `WLWiring.stabOrbit_of_colorEq` | 80-94 | **The wiring payoff — WL-colour equality ⟹ same `Stab`-orbit** (the hard `cells ⊆ orbits` direction / `bᵢ=1` hard half), for a plane-pinning singleton-reading colouring on an anisotropic base `{a,b}`. | — |
| `WLWiring.colorEq_iff_stabOrbit` | 96-110 | **Full `bᵢ=1` for the WL colouring.** Adding `Stab`-invariance upgrades the payoff to the iff `C u = C u' ↔ StabOrbit`, so the WL cells coincide exactly with the `Stab({a,b})`-orbits. | — |
| `WLWiring.ReadsSingletonCounts` | 122-128 | **The count analogue of `ReadsSingletonIsotropy`.** Interface field: `C` reflects the joint isotropy count `jointIsoCountK Q · {t,t₀}` against colour-singleton anchors `t, t₀`. | Structure |
| `WLWiring.SeparatesPlaneFromComplement` | 130-135 | **The genuinely-open residual, named.** Plane points get a different `C`-colour from every non-plane vertex — the honest remaining WL-dimension content (orbit-rigidity of the plane does not make its points global colour-singletons). | Definition |
| `WLWiring.pinIter_subset_W` | 137-148 | The pinning closure never leaves the plane: `pinIter ⊆ W` given the seed is inside `W`. | — |
| `WLWiring.colorSingleton_of_mem_pinIter` | 150-183 | **The induction — every pinned point is a colour-singleton.** By induction on the closure level, using the complement separation, the count-reading interface, and `plane_count_sep` to rule out same-colour distinct plane points. | — |
| `WLWiring.pinsPlane_of_planePinnable` | 185-202 | **Reduce `C` pins `W` to `PlanePinnable` + the two interfaces + the residual.** If the pinning closure reaches all of `W`, `C` reads singleton counts, plane points are colour-separated from the complement, and the base is individualised, then `C` pins `W` — chaining with the Core gives `bᵢ=1` end-to-end. | — |

## Archive/ChainDescent-scratch/ScratchWallKernel.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Wall.similitude_polar` | 45-51 | Similitudes scale the polar form: `polar Q (g x) (g y) = μ · polar Q x y` (polarisation of `Q∘g=μ·Q`); for `μ=1` (isometry) the polar is preserved. | — |
| `Wall.SameExactGram` | 53-56 | Exact Gram profile to `S`: equal `Q` and equal `polar · s` ∀ `s ∈ S`. Determines the `Stab(S)`-orbit (via Witt). | Definition |
| `Wall.SameSquareClass` | 58-62 | Square-class profile to `S`: `χ` (quadratic character) of the exact Gram data — the finest graph-invariant (the cap). What refinement sees. | Definition |
| `Wall.sameExactGram_imp_sameSquareClass` | 64-66 | Exact ⟹ square-class (free, apply `χ`). | — |
| `Wall.stabOrbit_imp_sameExactGram_of_anisotropic` | 68-80 | **Soundness (free).** Orbit ⟹ exact Gram at an anisotropic base: the `S`-fixing similitude has `μ=1` (delimiter), so it is an isometry preserving `Q` and `polar · s`. | — |
| `Wall.WallKernel` | 82-87 | **★ The open kernel.** Square-class profile *determines* exact Gram profile — the entire open content of `CellsAreOrbits` in the anisotropic regime (bounded-base determination = separator→certifier). Count-form = `ZProfileSeparates`. | Definition |
| `Wall.WittExtendsToOrbit` | 89-93 | Carried Witt-extension input (tech debt): equal exact Gram to `S` ⟹ same `Stab(S)`-isometry-orbit. | Definition |
| `Wall.stabOrbit_of_sameSquareClass` | 95-100 | The reduction (hard direction): `WallKernel` + Witt ⟹ same square-class ⟹ same orbit. | — |
| `Wall.stabOrbit_iff_sameSquareClass_of_wallKernel` | 102-110 | **★ Isolation capstone (single-round).** At an anisotropic base, modulo {Witt}, `CellsAreOrbits` (orbit ⟺ square-class) **⟺ `WallKernel`**. (The single-round `SameSquareClass` instance — refuted at a bounded base by the 3c probe; see the parametric form below.) | — |
| `Wall.WallKernelFor` | 128-132 | **The observable-parametric wall kernel.** A relation `Obs` *determines* the exact Gram to `S` — `CellsAreOrbits`'s open content parameterised by the refinement observable. Probe-validated target: `Obs` = iterated `χ(det G₂)` 2-WL pair-count (the crack); `Obs = SameSquareClass` (single round) is refuted at a bounded base. | Definition |
| `Wall.wallKernel_eq_wallKernelFor` | 134-135 | `WallKernel` is the `SameSquareClass` instance of `WallKernelFor` (definitional). | — |
| `Wall.stabOrbit_of_obs` | 137-140 | Observable-parametric reduction: `WallKernelFor Obs` + Witt ⟹ `Obs ⟹ StabOrbit`. | — |
| `Wall.stabOrbit_iff_obs_of_wallKernelFor` | 142-150 | **★ Observable-parametric isolation capstone.** Given orbit-soundness of `Obs` (free for any graph invariant) + Witt, `CellsAreOrbits` for `Obs` (orbit ⟺ `Obs`) **⟺ `WallKernelFor Obs`**. Redirected 3c proves it for `Obs` = iterated `χ(det G₂)` 2-WL. | — |

## Archive/ChainDescent-scratch/ScratchWittCone.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `WittCone.reflFunc` | 26-28 | The reflection functional `y ↦ polar Q y v / Q v` (the `f` of `Module.reflection`) and its apply lemma. | Definition, `noncomputable` |
| `WittCone.reflFunc_apply` | 30-33 | — | — |
| `WittCone.reflFunc_self` | 35-39 | `reflFunc Q v v = 2` (the `Module.reflection` hypothesis), for `Q v ≠ 0`. | — |
| `WittCone.refl` | 41-43 | — | Definition, `noncomputable` |
| `WittCone.map_sub'` | 45-51 | The quadratic-difference expansion `Q (a − b) = Q a − polar Q a b + Q b`. | — |
| `WittCone.refl_isometry` | 53-62 | **W0** — the reflection is an isometry: `Q (τ_v y) = Q y` (needs only `Q v ≠ 0`). | — |
| `WittCone.reflSim` | 64-69 | **W0** — the reflection packaged as a `Similitude` (multiplier 1). | Definition, `noncomputable` |
| `WittCone.refl_swap` | 71-80 | **W0** — `Q u = Q v ∧ Q(u−v) ≠ 0 ⟹ τ_{u−v}(u) = v`. For isotropic `u,v` this is the `polar ≠ 0` case. | — |
| `WittCone.simComp` | 82-88 | Composition of similitudes (multipliers multiply); chains two reflections. | Definition, `noncomputable` |
| `WittCone.cone_case_polar_ne` | 90-98 | **W1, `polar ≠ 0` case** — two nonzero isotropic vectors with `polar Q u u' ≠ 0` are related by one reflection. | — |
| `WittCone.exists_hyperbolic_partner` | 100-116 | — | — |
| `WittCone.IsotropicPairing` | 118-123 | **The residual** of W1: for any two nonzero isotropic `u, u'`, an isotropic `w` non-orthogonal to both. A concrete vector-existence statement; the only remaining content of `WittConeTransitive`. | Definition |
| `WittCone.wittConeTransitive_of_pairing` | 125-146 | **W1 — the reduction.** `IsotropicPairing Q ⟹ WittConeTransitive Q` (the `polar≠0` case via `cone_case_polar_ne`; the `polar=0` case via two reflections through the pairing vector, composed by `simComp`). | — |
