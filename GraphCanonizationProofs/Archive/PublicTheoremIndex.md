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
| `AdjMatrix.ext` | — | Two adjacency matrices are equal iff their adjacency functions agree pointwise. | `@[ext]` |

## Archive/V4/FullCorrectness/Permutation.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AdjMatrix.permute` | 21-28 | Relabel vertices of G by permutation σ. Uses σ.symm for left-action semantics. | — |
| `AdjMatrix.permute_adj` | 30-32 | Simplification rule: `(G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `AdjMatrix.permute_one` | 34-39 | Permuting by the identity does nothing: `G.permute 1 = G`. | `@[simp]`; Widely reused — identity is the unit of permutation action |
| `AdjMatrix.permute_mul` | 41-47 | Permutation action composes as left action: `G.permute (σ * τ) = (G.permute τ).permute σ`. | Widely reused — composition of permutation actions |
| `AdjMatrix.permute_permute_symm` | 49-53 | Permuting by inverse undoes original: `(G.permute σ).permute σ⁻¹ = G`. | `@[simp]` |
| `AdjMatrix.permute_symm_permute` | 55-58 | Inverse permute then permute: `(G.permute σ⁻¹).permute σ = G`. | `@[simp]` |
| `swapVertexLabels_eq_permute` | 62-72 | Bridge between concrete `swapVertexLabels` and abstract `permute` action. | — |

## Archive/V4/FullCorrectness/Automorphism.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AdjMatrix.Aut` | 22-41 | The automorphism group of G: permutations σ with `G.permute σ = G`. Instances: `DecidableEq`, `Fintype`. | — |
| `mem_Aut_iff` | 43-44 | Characterization of `Aut` via permute: `σ ∈ G.Aut ↔ G.permute σ = G`. | API characterization; useful when needing the bicondition explicitly |
| `mem_Aut_iff_adj` | 46-56 | Characterization via adjacency: `σ ∈ G.Aut ↔ ∀ i j, G.adj (σ.symm i) (σ.symm j) = G.adj i j`. | API characterization in adjacency form |
| `AdjMatrix.orbit` | 60-62 | The `Aut(G)`-orbit of vertex v: all vertices reachable from v by an automorphism. | — |
| `mem_orbit_iff` | 64-65 | Characterization: `w ∈ G.orbit v ↔ ∃ σ ∈ G.Aut, σ v = w`. | API characterization of orbit membership |
| `AdjMatrix.mem_orbit_self` | 69-70 | Reflexivity: `v ∈ G.orbit v`. | — |
| `AdjMatrix.mem_orbit_symm` | 72-77 | Symmetry: `w ∈ G.orbit v → v ∈ G.orbit w`. | — |
| `AdjMatrix.mem_orbit_trans` | 79-84 | Transitivity: `v ∈ G.orbit u → w ∈ G.orbit v → w ∈ G.orbit u`. | — |
| `AdjMatrix.orbitSetoid` | 86-93 | Same-orbit as equivalence relation; classes are the `Aut(G)`-orbits. | — |
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
| `permNat` | 20-21 | Re-index natural numbers by permutation (identity outside `[0, n)`). | — |
| `permNat_one` | 23-24 | Permuting by identity is the identity on naturals. | `@[simp]` |
| `permNat_lt` | 26-28 | Permuting a number `< n` stays `< n`. | — |
| `permNat_of_lt` | 30-32 | Explicit formula for `permNat σ i` when `i < n`. | Widely reused — primary `permNat` rewrite tool |
| `permNat_of_ge` | 34-36 | Permuting a number `≥ n` is unchanged. | — |
| `permNat_inv_perm` | 38-42 | Applying σ then σ⁻¹ is identity on in-range naturals. | `@[simp]` |
| `permNat_perm_inv` | 44-48 | Applying σ⁻¹ then σ is identity on in-range naturals. | `@[simp]` |
| `permNat_fin` | 50-52 | `permNat` on a `Fin n` value equals the permuted `Fin` value. | `@[simp]` |
| `PathSegment.permute` | 62-65 | Relabel vertex indices inside a `PathSegment n` by permutation σ. | — |
| `PathsBetween.permute` | 67-87 | Relabel vertex indices inside a `PathsBetween n`, respecting depth cases. | — |
| `PathsFrom.permute` | 89-102 | Relabel vertex indices inside `PathsFrom n`, reordering the `pathsToVertex` list. | — |
| `PathState.permute` | 104-116 | Relabel a full `PathState n` by σ using σ.symm semantics. | — |
| `RankState.permute` | 118-132 | Relabel a `RankState` by σ: slot `(d, σ⁻¹ s, σ⁻¹ e)` maps to output slot `(d, s, e)`. | — |
| `initializePaths_pathsOfLength_size` | 136-139 | The `pathsOfLength` array of `initializePaths G` has size `n`. | `@[simp]` |
| `PathState_permute_pathsOfLength_size` | 141-146 | Permuting a `PathState` preserves the `pathsOfLength.size`. | `@[simp]` |
| `initializePaths_pathsOfLength_get_size` | 148-154 | Depth-`d` slice of `initializePaths G` is a length-`n` array. | — |

## Archive/V4/FullCorrectness/Equivariance/StageA.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `initializePaths_Aut_equivariant` | 204-287 | Main Stage A theorem: `initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)` for any σ. | **Stage A** — holds for all σ, no Aut(G) hypothesis |

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
| `RankState.σInvariant` | 344-359 | Predicate on `rs : RankState`: size-shape and value σ-invariance conditions sufficient to conclude `RankState.permute σ rs = rs`. | **Key structure** — packages σ-invariance for extensionality |
| `RankState.σInvariant.permute_eq_self` | 361-409 | Extensionality: σ-invariance implies `RankState.permute σ rs = rs`. | **Extensionality** — σ-invariance ⟹ permute equals identity |
| `calculatePathRankings_size_inv` | 411-544 | Size facts on `calculatePathRankings` output: `betweenRanks` is `vc×vc×vc`, `fromRanks` is `vc×vc`. | — |

## Archive/V4/FullCorrectness/Equivariance/ComparisonSort.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `sortBy_map` | 62-73 | `sortBy cmp (L.map f) = (sortBy cmp L).map f` when `f` preserves `cmp`; instantiated with `PathSegment.permute σ` for σ-equivariance. | Global form; pointwise variant `sortBy_map_pointwise` is strictly stronger |
| `perm_insertSorted` | 75-85 | `insertSorted cmp a L` is a `List.Perm` of `a :: L`. | — |
| `sortBy_perm` | 87-94 | `sortBy cmp L` is a `List.Perm` of `L`. | Widely reused — sorted output is a permutation of input |
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
| `labelEdgesStep` | 82-96 | The `labelEdgesAccordingToRankings` fold body extracted as a standalone function (swap-and-update). | — |
| `labelEdges_fold_strong` | 169-242 | Strong fold invariant: tracks both the cumulative permutation σ and `acc.2.getD v 0 = rankMap₀.getD (σ⁻¹ v) 0` pointwise. | — |
| `labelEdges_terminal_rankMap_identity` | 381-397 | After the full foldl over `List.finRange n`, the terminal rankMap is the identity: `rankMap.getD v.val 0 = v.val`. | — |

## Archive/V4/FullCorrectness/Tiebreak.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `VtsInvariant` | 39-41 | Predicate: `σ` maps `vts` to itself (`vts.getD (σ v).val 0 = vts.getD v.val 0` for all `v`). | — |
| `VtsInvariant.one` | 43-44 | The identity permutation always satisfies `VtsInvariant`. | — |
| `VtsInvariant.mul` | 46-51 | Composition: if σ and τ both satisfy `VtsInvariant`, so does `σ * τ`. | — |
| `VtsInvariant.inv` | 53-60 | Inversion: if σ satisfies `VtsInvariant`, so does `σ⁻¹`. | — |
| `AdjMatrix.TypedAut` | 62-77 | Subgroup of `Aut G` whose elements also satisfy `VtsInvariant vts`. | — |
| `mem_TypedAut_iff` | 79-81 | `σ ∈ G.TypedAut vts ↔ σ ∈ G.Aut ∧ VtsInvariant σ vts`. | API characterization; useful when needing the bicondition explicitly |
| `AdjMatrix.TypedAut_le_Aut` | 83-87 | `G.TypedAut vts` is a subgroup of `G.Aut`. | — |
| `VtsInvariant.replicate_zero` | 107-112 | The all-zeros array satisfies `VtsInvariant σ` for any σ. | — |
| `TypedAut_replicate_zero` | 114-119 | For any `G`, every automorphism is in `TypedAut G (Array.replicate n 0)` — the typed-automorphism group with all-zeros types coincides with the full automorphism group. | — |
| `typeClass` | 142-144 | The set of `Fin n` vertices with vertex type exactly `t₀` in `vts`. | — |
| `shiftAbove_size` | 168-170 | `shiftAbove t₀ vts` preserves array size. | — |
| `shiftAbove_getD` | 172-182 | Value of `shiftAbove t₀ vts` at position `j`. | — |
| `shiftAbove_getD_below` | 184-189 | Positions with type `< t₀` are unchanged by `shiftAbove`. | — |
| `shiftAbove_getD_above` | 191-195 | Positions with type `> t₀` have their value incremented by 1 after `shiftAbove`. | — |
| `shiftAbove_getD_target` | 197-200 | Positions with type `= t₀` also have value shifted after `shiftAbove`. | — |
| `breakTieCount` | 204-207 | Number of vertices in `vts` with type `t₀`. | — |
| `breakTie_noop` | 209-216 | If `t₀` does not appear in `vts`, `breakTie t₀ vts = vts`. | — |
| `breakTie_eq_promote_shift` | 218-226 | `breakTie t₀ vts = shiftAbove t₀ (breakTiePromote t₀ vts)`. | Algebraic decomposition; useful when reasoning about `breakTie` via its components |
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
| `runFrom` | 1007-1019 | "Remainder of the pipeline" referenced in §6: feed an intermediate typing in, run the remaining `orderVertices` outer iterations and the final `labelEdgesAccordingToRankings`, and produce the canonical matrix. | Pipeline entry point — all `runFrom_*` theorems concern this definition |
| `breakTieAt` | 1029-1038 | The "what if we had kept vertex `keep` instead of `min (typeClass vts t₀)`" alternative to `breakTie`. Promotes every vertex with value `t₀` except `keep` to `t₀ + 1`. | — |
| `breakTieAt_size` | 1074-1078 | `breakTieAt vts t₀ keep` preserves array size. | — |
| `breakTieAt_getD_of_ne` | 1129-1134 | `breakTieAt` leaves positions `≠ keep` unchanged. | — |
| `breakTieAt_getD_keep` | 1156-1160 | `breakTieAt` preserves the value at `keep`. | — |
| `breakTieAt_getD_promoted` | 1198-1206 | Value at positions promoted by `breakTieAt`. | — |
| `breakTieAt_VtsInvariant_eq` | 1208-1248 | `breakTieAt` preserves `VtsInvariant τ` when `τ keep = keep`. | Single-vts form; relational two-vts version: `breakTieAt_τ_related` |
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
| `sortBy_map_pointwise` | 73-89 | Pointwise variant of `sortBy_map`: requires `cmp (f a) (f b) = cmp a b` only for `a, b ∈ L`. | Pointwise form of `sortBy_map`; relational variant: `sortBy_map_pointwise_relational` |
| `comparePathSegments_σ_equivariant` | 91-130 | `comparePathSegments vts br (PathSegment.permute σ p) (PathSegment.permute σ q) = comparePathSegments vts br p q` under σ-invariant `vts` and `br`. | Single-σ form; relational generalization: `comparePathSegments_σ_relational` |
| `map_reindex_perm` | 138-172 | Reindex-perm lemma: σ-reindexing `L.map act` gives a `List.Perm` of `L.map act`. | — |
| `PathsBetween_permute_connectedSubPaths_perm` | 174-216 | `(p.permute σ).connectedSubPaths.Perm (p.connectedSubPaths.map (PathSegment.permute σ))` for depth>0 paths of length `vc`. | — |
| `PathsFrom_permute_pathsToVertex_perm` | 218-256 | `(p.permute σ).pathsToVertex.Perm (p.pathsToVertex.map (PathsBetween.permute σ))` for length-`vc` `pathsToVertex`. | — |
| `comparePathsBetween_σ_equivariant` | 258-299 | `comparePathsBetween vts br (p₁.permute σ) (p₂.permute σ) = comparePathsBetween vts br p₁ p₂` under σ-invariant `vts`/`br` and length conditions. | Single-σ form; relational generalization: `comparePathsBetween_σ_relational` |
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
| `from_assignList_σ_rank_closure` | 446-621 | The `fromRanks` assignList is σ-rank-closed: for each `(p, r)` in the list, `(PathsFrom.permute σ p, r)` is also in the list. | σ ∈ Aut G form; rel: `from_assignList_σ_rank_rel`, general: `from_assignList_σ_rank_general` |
| `mem_allBetween_iff` | 649-656 | `q ∈ allBetween ↔ ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex`. | — |
| `between_assignList_σ_rank_closure` | 658-833 | The `betweenRanks` assignList is σ-rank-closed: for each `(q, r)` in the list, `(PathsBetween.permute σ q, r)` is also in the list. | σ ∈ Aut G form; rel: `between_assignList_σ_rank_rel`, general: `between_assignList_σ_rank_general` |

## Archive/V4/FullCorrectness/Equivariance/PathEquivariance.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `calculatePathRankings_σInvariant_combined` | 319-339 | Combined `RankState.σInvariant σ` for `calculatePathRankings (initializePaths G) vts`: assembles size invariants and cell σ-invariance into the full `σInvariant` structure. | — |
| `calculatePathRankings_fromRanks_inv` | 341-350 | σ-invariance of `fromRanks` values: `(rs.fromRanks.getD d #[]).getD s.val 0 = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0`. Projection of `σInvariant_combined`. | Projection of `calculatePathRankings_σInvariant_combined` |
| `calculatePathRankings_betweenRanks_inv` | 352-361 | σ-invariance of `betweenRanks` values: `((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0 = ... (σ⁻¹ s) ... (σ⁻¹ e) ...`. Projection of `σInvariant_combined`. | Projection of `calculatePathRankings_σInvariant_combined` |
| `calculatePathRankings_σInvariant` | 363-370 | Direct alias for `calculatePathRankings_σInvariant_combined`; the canonical public name for the full σ-invariance result. | Public alias for `calculatePathRankings_σInvariant_combined` |
| `calculatePathRankings_RankState_invariant` | 372-382 | `RankState.permute σ` is the identity on `calculatePathRankings (initializePaths G) vts` when σ ∈ Aut G and vts is σ-invariant. | σ ∈ Aut G form; relational: `calculatePathRankings_σ_equivariant_relational`, general: `calculatePathRankings_σ_equivariant_general` |
| `calculatePathRankings_Aut_equivariant` | 384-398 | **Stage B**: `calculatePathRankings (PathState.permute σ (initializePaths G)) vts = RankState.permute σ (calculatePathRankings (initializePaths G) vts)`. Assembled from Stage A plus σ-invariance. | **Stage B** — requires σ ∈ Aut G |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `comparePathSegments_σ_relational` | 67-103 | Relational form: `comparePathSegments vts₂ br₂ p₁ p₂ = comparePathSegments vts₁ br₁ (f p₁) (f p₂)` when `f = PathSegment.permute σ` and the two `vts`/`br` pairs are σ-related. | Relational form of `comparePathSegments_σ_equivariant` |
| `sortBy_map_pointwise_relational` | 130-148 | Relational pointwise variant of `sortBy_map`: `sortBy cmp₂ (L.map f) = (sortBy cmp₁ L).map f` when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. | Relational form of `sortBy_map_pointwise` |
| `orderInsensitiveListCmp_map_pointwise_relational` | 150-203 | Relational pointwise variant of `orderInsensitiveListCmp_map`: `orderInsensitiveListCmp cmp₂ (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp₁ L₁ L₂` with per-element `cmp₂ (f a) (f b) = cmp₁ a b`. | — |
| `comparePathsBetween_σ_relational` | 205-252 | Relational form of `comparePathsBetween_σ_equivariant` for two different `vts`/`br` pairs. | Relational form of `comparePathsBetween_σ_equivariant` |
| `comparePathsFrom_σ_relational` | 254-305 | σ-equivariance of `comparePathsFrom` across two different `vts`/`br` pairs. | — |
| `set_chain_σRelated` | 360-521 | The `fromRanks` `set!`-chain produces τ-related outputs when the two assignLists are τ-related (each entry in one maps to a τ-shifted entry of equal rank in the other). | — |
| `setBetween_chain_σRelated` | 523-734 | The `betweenRanks` `setBetween`-chain produces τ-related outputs when the two assignLists are τ-related. | — |
| `from_assignList_σ_rank_rel` | 900-1154 | Relational σ-rank-closure for the `fromRanks` assignList: entries on the two sides are τ-related with equal ranks. | Relational form of `from_assignList_σ_rank_closure` (still requires σ ∈ Aut G) |
| `between_assignList_σ_rank_rel` | 1253-1485 | Relational σ-rank-closure for the `betweenRanks` assignList. | Relational form of `between_assignList_σ_rank_closure` (still requires σ ∈ Aut G) |
| `betweenRankFn_σ_rel_from_cells` | 1494-1510 | Cell-level τ-relatedness of a 3D table lifts to a τ-related `betweenRankFn`. | — |
| `CalcRankingsRel` | 1512-1536 | Loop invariant for the relational depth foldl: the two accumulators `(currentBetween₁, currentFrom₁)` and `(currentBetween₂, currentFrom₂)` are τ-related at every cell. | — |
| `calculatePathRankings_σ_equivariant_relational` | 1852-1871 | **Stage B-rel**: `calculatePathRankings` outputs on τ-related inputs are τ-related at every cell. Requires σ ∈ Aut G. | Relational form of `calculatePathRankings_RankState_invariant` (still requires σ ∈ Aut G) |

## Archive/V4/FullCorrectness/Equivariance/PathEquivarianceGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `from_assignList_σ_rank_general` | 397-633 | General σ-rank-closure for the `fromRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | General form of `from_assignList_σ_rank_closure` — drops σ ∈ Aut G hypothesis |
| `between_assignList_σ_rank_general` | 642-880 | General σ-rank-closure for the `betweenRanks` assignList across two Stage-A-related states (no Aut G hypothesis). | General form of `between_assignList_σ_rank_closure` — drops σ ∈ Aut G hypothesis |
| `calculatePathRankings_σ_equivariant_general` | 1280-1298 | **Stage B-rel-general**: `calculatePathRankings` on `initializePaths (G.permute σ)` is σ-related to `calculatePathRankings` on `initializePaths G`, for any σ (no Aut G hypothesis). | **Stage B-rel-general** — fully general form (no Aut G) |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoop.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_writeback` | 102-113 | After `convergeOnce`, every in-bounds position `i` holds `calculatePathRankings.getFrom (n-1) i`. | — |
| `RankState.getFrom_permute` | 115-142 | `getFrom` on `RankState.permute σ rs` reads from the `σ⁻¹`-shifted position in the original `rs`. | — |
| `calculatePathRankings_getFrom_invariant` | 144-177 | σ-invariance of `getFrom (n-1)`: positions `v` and `σ v` return the same value when σ ∈ Aut(G) and `vts` is σ-invariant. | — |
| `convergeOnce_Aut_invariant` | 179-196 | One `convergeOnce` step preserves Aut(G)-invariance: `output[σ v] = output[v]` for σ ∈ Aut(G). | σ ∈ Aut G form; relational: `convergeOnce_VtsInvariant_eq`, general: `convergeOnce_σ_equivariant_general` |
| `convergeOnce_size_preserving` | 198-222 | `convergeOnce` preserves the vertex type array size. | — |
| `convergeLoop_Aut_invariant` | 224-250 | The full convergence loop preserves Aut(G)-invariance for any fuel; proved by induction on fuel. | σ ∈ Aut G form; relational: `convergeLoop_VtsInvariant_eq`, general: `convergeLoop_σ_equivariant_general` |
| `convergeLoop_zeros_Aut_invariant` | 252-260 | Corollary: starting from the all-zeros array, the convergence loop preserves Aut(G)-invariance. | — |
| `orderVertices_Aut_equivariant` | 264-275 | Stage C: `orderVertices (PathState.permute σ (initializePaths G)) vts = orderVertices (initializePaths G) vts` for σ ∈ Aut(G). | **Stage C** |
| `labelEdges_Aut_equivariant` | 279-287 | Stage D: `labelEdgesAccordingToRankings vts (G.permute σ) = labelEdgesAccordingToRankings vts G` for σ ∈ Aut(G); follows immediately from `G.permute σ = G`. | **Stage D** |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_unchanged_when_not_flag` | 59-66 | If `convergeOnce`'s flag output is `false`, the output array equals the input array (fixed point). | — |
| `convergeLoop_unchanged_fixedpoint` | 68-83 | If `convergeOnce`'s flag is `false`, then `convergeLoop` is the identity at every fuel level. | — |
| `convergeLoop_succ_eq_loop_of_once` | 85-104 | `convergeLoop state vts (k+1) = convergeLoop state (convergeOnce state vts).1 k` regardless of the flag. | — |
| `calculatePathRankings_getFrom_VtsInvariant_eq` | 108-125 | Relational `getFrom (n-1)` analogue: for τ-related `vts₁`/`vts₂`, the `getFrom` values are τ-shifted. | — |
| `convergeOnce_VtsInvariant_eq` | 129-152 | One `convergeOnce` step on τ-related arrays produces τ-related outputs. Relational analogue of `convergeOnce_Aut_invariant`. | Relational form of `convergeOnce_Aut_invariant` (still requires σ ∈ Aut G) |
| `convergeLoop_VtsInvariant_eq` | 154-183 | The full `convergeLoop` preserves τ-relatedness for any fuel. Relational analogue of `convergeLoop_Aut_invariant`. | Relational form of `convergeLoop_Aut_invariant` (still requires σ ∈ Aut G) |

## Archive/V4/FullCorrectness/Equivariance/ConvergeLoopGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `convergeOnce_σ_equivariant_general` | 44-69 | **P6.B**: `convergeOnce` on `(initializePaths (G.permute σ), vts₂)` is σ-related to `convergeOnce` on `(initializePaths G, vts₁)` for any σ. | **P6.B** — general form of `convergeOnce_Aut_invariant` |
| `convergeLoop_σ_equivariant_general` | 71-103 | **P6.B loop**: The full `convergeLoop` is σ-equivariant across the two general states for any fuel. | **P6.B loop** — general form of `convergeLoop_Aut_invariant` |

## Archive/V4/FullCorrectness/Equivariance/StageDRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `TieFree` | 40-43 | Predicate: all `n` vertices have distinct types in `rks` (no ties). | — |
| `computeDenseRanks_perm_when_tieFree` | 362-380 | Under `TieFree rks n`, `computeDenseRanks` output is a permutation of `[0, 1, ..., n-1]`. | — |
| `computeDenseRanks_τ_shift_distinct` | 500-569 | Under `TieFree` and τ-related ranks, `computeDenseRanks` on `rks₂` is the τ-shifted `computeDenseRanks` on `rks₁`. | — |
| `labelEdges_VtsInvariant_eq_distinct` | 573-653 | When `rks` is tie-free, `labelEdgesAccordingToRankings rks G` is invariant under `VtsInvariant` (Aut G acts trivially). | Single-graph form (Phase 3.E); two-graphs version: `labelEdges_two_graphs_σ_related` |
| `labelEdges_two_graphs_σ_related` | 663-721 | Under τ-related tie-free ranks, `labelEdgesAccordingToRankings rks₂ G₂ = labelEdgesAccordingToRankings rks₁ G₁`. Stage D-rel. | **Stage D-rel** — fully general form (no Aut G) |

## Archive/V4/FullCorrectness/Equivariance/BreakTieRelational.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `shiftAbove_VtsInvariant_eq` | 33-52 | `shiftAbove t₀ vts₂` at slot `w` equals `shiftAbove t₀ vts₁` at slot `τ⁻¹ w` when `vts₁`/`vts₂` are τ-related. | — |
| `shiftAbove_VtsInvariant_size_eq` | 54-57 | τ-related `vts₁`/`vts₂` have the same size after `shiftAbove`. | — |
| `breakTieAt_τ_related` | 68-105 | `breakTieAt vts₂ t₀ (τ keep)` at slot `w` equals `breakTieAt vts₁ t₀ keep` at slot `τ⁻¹ w` when inputs are τ-related. | Relational form of `breakTieAt_VtsInvariant_eq` |
| `breakTieAt_size_eq` | 107-111 | τ-related `vts₁`/`vts₂` have the same size after `breakTieAt`. | — |

## Archive/V4/FullCorrectness/Invariants.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `IsPrefixTyping` | 72-76 | A typing `vts` is a prefix of ℕ: its value set equals `{0, 1, …, m-1}` for some `m`. | — |
| `IsPrefixTyping.replicate_zero` | 78-97 | The all-zeros array satisfies `IsPrefixTyping`. | — |
| `convergeLoop_size_preserving` | 101-117 | `convergeLoop` preserves the vertex type array size. | — |
| `getFrom_image_isPrefix_for_initializePaths` | 491-700 | The image of `getFrom (n-1)` on `calculatePathRankings (initializePaths G) vts` is a prefix `{0, ..., k}`. | — |
| `convergeLoop_preserves_prefix` | 702-739 | `convergeLoop` preserves `IsPrefixTyping` from fuel 0 onward. | — |
| `breakTie_targetPos_is_min_tied` | 743-832 | The tiebreak target position `breakTieAt`'s `keep` argument is the minimum vertex in the tied type class. | — |
| `UniquelyHeldBelow` | 849-855 | Predicate: every value `< q` in `vts` is held by exactly one vertex. The algorithmic hypothesis (Phase 5) that values `0..q-1` are already uniquely held, so remaining foldl iterations can finish breaking ties. | — |
| `convergeLoop_preserves_lower_uniqueness` | 1616-1643 | `convergeLoop` preserves `UniquelyHeldBelow q` for any fuel. | — |
| `breakTie_step_preserves_uniqueness` | 1751-1913 | One `breakTie` step preserves `UniquelyHeldBelow` for the next level. | — |
| `orderVertices_prefix_invariant` | 1966-1977 | `orderVertices (initializePaths G) zeros` satisfies `IsPrefixTyping`. | — |
| `orderVertices_n_distinct_ranks` | 1979-2043 | `orderVertices` produces exactly `n` distinct values `0, 1, ..., n-1`. | Final §7 invariant — leaf result |
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
| `breakTie_min_witness_in_typeClass` | 475-483 | The minimum witness vertex lies in `typeClass`. | Convenience corollary of `breakTie_min_witness` |
| `OrbitCompleteAfterConv` | 502-512 | Orbit-completeness: for `mid` an intermediate algorithm state, vertices with equal values in `convergeLoop(initializePaths G) mid n` lie in the same `TypedAut`-orbit of that converged array. | ⚠ empirically falsified 2026-04-28 — see [OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md) |
| `runFrom_VtsInvariant_eq_strong` | 514-707 | Strong relational theorem: `runFrom s vts₂ G = runFrom s vts₁ G` (not just τ-related, equal) given `OrbitCompleteAfterConv` and `UniquelyHeldBelow s`. | Single-graph strong form; two-graphs version: `runFrom_VtsInvariant_eq_strong_general` |
| `runFrom_VtsInvariant_eq` | 720-737 | Corollary of the strong form: `runFrom 0 zeros G = runFrom 0 (τ-shifted zeros) G`. | Convenience corollary of `runFrom_VtsInvariant_eq_strong` (specializes to zeros, start=0) |
| `tiebreak_choice_independent` | 739-775 | The canonical `orderVertices` output is independent of which tied vertex is chosen for tiebreaking; proved from `runFrom_VtsInvariant_eq`. | Phase 5 / §6 final result — leaf |

## Archive/V4/FullCorrectness/Equivariance/OrderVerticesGeneral.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `OrbitCompleteAfterConv_general` | 34-45 | Two-graphs variant of `OrbitCompleteAfterConv`: orbit-completeness for `convergeLoop (initializePaths (G.permute σ)) mid n`. | ⚠ empirically falsified 2026-04-28 (Cycle3 disjoint union, K4, odd-cycle bases) — see [OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md) |
| `runFrom_VtsInvariant_eq_strong_general` | 131-377 | **P6.C**: `runFrom s vts₁ G = runFrom s vts₂ (G.permute σ)` given `OrbitCompleteAfterConv_general` and σ-relatedness of the arrays. | **P6.C** — two-graphs form of `runFrom_VtsInvariant_eq_strong` |

## Archive/V4/FullCorrectness/Equivariance/MainRelationalNotes.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `zeros_σ_invariant` | 91-97 | The all-zeros array is σ-invariant for any σ: `(Array.replicate n 0).getD (σ v) 0 = (Array.replicate n 0).getD v 0 = 0`. | — |

## Archive/V4/FullCorrectness/Main.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `run_isomorphic_eq_new` | 147-157 | **(⟹) direction**: `G ≃ H → run zeros G = run zeros H`. Assembled from Stage A + Stage B-rel-general + P6.B/C + Stage D-rel. | — |
| `run_canonical_correctness` | 167-185 | **Main theorem**: `G ≃ H ↔ run zeros G = run zeros H`. Combines both directions. | **Main theorem** — public API of the project |

## Archive/V4/FullCorrectness/V4Reused.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `swapVertexLabels_self_inverse` | 47-49 | — | — |
| `swapVertexLabels_comm` | 51-55 | — | — |
| `AdjMatrix.Isomorphic.symm` | 59-70 | — | — |
| `labelEdgesAccordingToRankings_isomorphic` | 74-126 | — | — |
| `run_isomorphic_to_input` | 128-131 | — | — |
| `run_eq_implies_iso` | 135-146 | — | — |

## Archive/V4/LeanGraphCanonizerV4.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `VertexType` | 5 | — | — |
| `EdgeType` | 6 | — | — |
| `swapVertexLabels` | 17-21 | — | — |
| `Isomorphic` | 23-34 | — | — |
| `adjToString` | 36-41 | — | — |
| `PathSegment` | 56-60 | — | — |
| `PathsBetween` | 62-67 | — | — |
| `PathsFrom` | 69-73 | — | — |
| `PathState` | 75-76 | — | — |
| `RankState` | 78-80 | — | — |
| `RankState.getBetween` | 82-83 | — | — |
| `RankState.getFrom` | 85-86 | — | — |
| `insertSorted` | 90-92 | — | — |
| `sortBy` | 94-96 | — | — |
| `orderInsensitiveListCmp` | 98-103 | — | — |
| `comparePathSegments` | 107-125 | — | — |
| `comparePathsBetween` | 127-135 | — | — |
| `comparePathsFrom` | 137-145 | — | — |
| `initializePaths` | 149-165 | — | — |
| `assignRanks` | 175-186 | — | — |
| `setBetween` | 188-192 | — | — |
| `calculatePathRankings` | 194-224 | — | — |
| `convergeOnce` | 228-240 | — | — |
| `convergeLoop` | 241-245 | — | — |
| `shiftAbove` | 264-266 | — | — |
| `breakTiePromote` | 268-282 | — | — |
| `breakTie` | 284-290 | — | — |
| `orderVertices` | 292-297 | — | — |
| `computeDenseRanks` | 301-318 | — | — |
| `getArrayRank` | 320-343 | — | — |
| `labelEdgesAccordingToRankings` | 345-361 | — | — |
| `run` | 365-369 | — | — |

## Archive/V4/UniqueGraphsBySize.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `size2` | 9-12 | — | — |
| `size3` | 14-19 | — | — |
