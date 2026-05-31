# Private Theorem Index — GraphCanonizationProofs

Index of `private` Lean declarations in the GraphCanonizationProofs project (active source) — internal helpers/stepping-stones not used outside their own file. Listed for completeness; the public API is in `../PublicTheoremIndex.md`. Archived counterparts live in `Archive/PrivateTheoremIndex.md`.

Maintained by `scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers`: **Name**, **Line**, **Notes** are computed from source; **Description** is hand-written and preserved.
## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line.
- **Description**: What the declaration achieves / why it exists (not how it is proved), in ≤ 2 sentences.
- **Notes**: Computed from source — infrastructure kind, `noncomputable`, and `@[…]` attributes.

## ChainDescent.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `closeStep_keeps_less` | 239-242 | `closeStep` never demotes a decided `less` entry. | — |
| `iterate_closeStep_keeps_less` | 244-254 | Iterating `closeStep` preserves any `less` entry — once decided, frozen. | — |
| `transitiveClose_conflict_less` | 267-274 | `transitiveClose conflictMatrix 0 1 = .less` (the `less`-chain wins the first `if`). | — |
| `transitiveClose_swap_conflict_less` | 276-284 | `transitiveClose (swap conflictMatrix) 0 1 = .less` — the σ-swap fails to flip the tie-break. | — |
| `POE.toNat_injective` | 322-324 | `POE.toNat` is injective. | — |
| `encTuple_injective` | 334-339 | `encTuple` is injective. | — |
| `witnessAdj` | 502-504 | Witness adjacency: the empty graph on 5 vertices (the `cell_split_uniform_false` discrepancy lives entirely in `P`). | Definition |
| `witnessP0` | 506-515 | Witness pre-guess matrix (`0 < 2`, `1 < 3`): cell-mates `0,1` relate symmetrically to the cell `{2,3}` but asymmetrically to vertices `2`, `3`. | Definition |
| `witnessChi` | 517-524 | Witness colouring with cells `{0,1}`, `{2,3}`, `{4}`. | Definition |
| `witnessTC` | 526-538 | Explicit `closeStep`-fixpoint of `applyGuess witnessP0 2 4 less` (`witnessP0` plus `2 < 4` plus the closure entry `0 < 4`). | Definition |
| `witnessTC_eq` | 540-552 | `transitiveClose (applyGuess witnessP0 2 4 less) = witnessTC`. | — |
| `witnessChi_stable` | 554-563 | `witnessChi` is 1-WL-stable for `(witnessAdj, witnessP0)`. | — |

| `closeStep_unknown_eq` | 1609-1621 | Expansion of `closeStep P i j` when `P i j = .unknown`, exposing the explicit `if`-chain. | — |
| `closeStep_unknown_subset` | 1849-1858 | The unknown-entry set of `closeStep P` is contained in that of `P`. | — |
| `cl_prov_canonical` | 1978-1983 | Every pair in `cl_prov S` is canonical (`p.1.val < p.2.val`). | — |
| `commitsToP_cl_prov_lessMono` | 1985-2003 | `commitsToP (cl_prov S)` is `.less`-bounded by `transitiveClose (commitsToP S)` for canonical `S`. | — |
| `Colouring.vertexRankNat_lt_n` | 3015-3029 | `vertexRankNat χ v < n` for every `v` (the rank is a valid `Fin n` value). | — |
## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CFIBase.edgeCountOrdered` | 96-98 | Ordered-pair edge count of the base graph, `∑ v, H.degree v`. | Definition |
| `CFIBase.cfiVertexCount_pos` | 132-139 | The CFI vertex count is positive whenever the base has at least one vertex (`0 < m`). | — |
| `Finset.card_powerset_filter_even` | 625-677 | Even-cardinality subsets of a nonempty finset count `2^(card−1)` — the classical combinatorial identity underlying `card_SubsetVertex`. | — |
| `CFIBase.card_evenSubsetsOfNeighbors` | 685-695 | `(H.evenSubsetsOfNeighbors v).card = 2^(H.degree v − 1)`. | — |
| `CFIBase.card_SubsetVertex` | 697-704 | `Fintype.card H.SubsetVertex = ∑ v, 2^(H.degree v − 1)`. | — |
| `CFIBase.card_EndpointVertex` | 706-715 | `Fintype.card H.EndpointVertex = ∑ v, 2 * H.degree v`. | — |
| `IsCFI'.adj_seed_endpoint_diff_gadget` | 985-993 | Cross-gadget non-adjacency: a seed and an endpoint in different gadgets (v ≠ v') are never adjacent. | — |
| `IsCFI'.adj_endpoint_seed_diff_gadget` | 995-1002 | Cross-gadget non-adjacency (symmetric form): `adj (endpointVertex v' w b) (seedVertex v) = 0` when v ≠ v'. | — |
| `IsCFI'.adj_bridge` | 1004-1012 | An endpoint `e^b_{v→w}` is adjacent to its bridge partner `e^b_{w→v}` (Fin-n level). | — |
| `IsCFI'.endpointVertex_ne_bridge` | 1014-1036 | An endpoint and its bridge partner are distinct `Fin n` vertices. | — |
| `individualizedColouring_singleton_self_pos` | 1060-1064 | The individualized seed's colour is nonzero. | — |
| `individualizedColouring_singleton_eq_seed_iff` | 1066-1079 | Under a singleton individualization, a vertex shares the seed's colour iff it is the seed — only the seed carries the fresh colour. | — |
| `IsCFI'.signature_endpoint_false_ne_true` | 1098-1144 | §13.6 M2.4 — under the single-seed individualization, the b=0 and b=1 endpoints at gadget v toward w have distinct signature multisets. | — |
| `IsCFI'.refineStep_endpoint_false_ne_true` | 1152-1168 | §13.7 M2.5 — one `refineStep` round on a single-seed individualization gives gadget v's b=0 and b=1 endpoints distinct colours. | — |
| `IsCFI'.allSeeds_card_le_baseSize` | 1249-1252 | `|allSeeds| ≤ h.baseSize` (convenience inequality form). | — |
| `IsCFI'.signature_endpoint_false_ne_true_allSeeds` | 1271-1319 | §13.9 M3.B — multi-seed analogue of M2.4: under `χ_{allSeeds}` the b=0 and b=1 endpoints at gadget v have distinct signatures. | — |
| `IsCFI'.refineStep_endpoint_false_ne_true_allSeeds` | 1321-1335 | §13.9 M3.B — one `refineStep` round on `χ_{allSeeds}` splits gadget v's b=0 and b=1 endpoints by parity. | — |
| `IsCFI'.signature_endpoint_true_inter_gadget` | 1364-1409 | §13.10 M3.C — inter-gadget signature distinction: b=true endpoints at different gadgets (v ≠ v') differ under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_endpoint_true_inter_gadget` | 1411-1429 | §13.10 M3.C — one `refineStep` round on `χ_{allSeeds}` gives b=true endpoints at different gadgets distinct colours. | — |
| `IsCFI'.signature_bridge_step` | 1455-1506 | §13.11 M3.D — bridge-propagation signature step: if bridge partners are χ-distinguished and that colour is absent from the second endpoint's adj=1 reach, the two endpoints' signatures differ. | — |
| `IsCFI'.refineStep_bridge_step` | 1508-1532 | §13.11 M3.D Phase 1 — the local bridge-propagation step: under the no-match precondition, one `refineStep` distinguishes an endpoint pair from their distinguished bridge partners. The reusable inductive engine for the cascade. | — |
| `IsCFI'.refineStep_endpoint_true_intra_gadget_partner` | 1678-1742 | §13.13 Phase 2.1 — at round 2 on `χ_{allSeeds}`, b=true endpoints at the same gadget toward different partners (w ≠ w') get distinct colours. | — |
| `CFIBase.aEmpty_eq_subset_empty` | 1774-1776 | `aEmpty v` is the empty-subset case of `subset`. | — |
| `CFIBase.cfiAdj_subset_endpoint_same_gadget_true_of_not_mem` | 1778-1788 | `cfiAdj (a_S^v) (e^1_{v→w}) = 1` when w ∉ S — a non-saturated subset is adjacent to some b=1 endpoint. | — |
| `CFIBase.cfiAdj_subset_endpoint_same_gadget_false_of_mem` | 1790-1800 | `cfiAdj (a_S^v) (e^0_{v→w}) = 1` when w ∈ S. | — |
| `CFIBase.cfiAdj_subset_endpoint_diff_gadget` | 1802-1812 | Cross-gadget non-adjacency: `subset hS` at v is not adjacent to an endpoint at v' ≠ v. | — |
| `CFIBase.subset_ne_endpoint` | 1814-1821 | A subset vertex and an endpoint vertex are distinct CFI vertices. | — |
| `IsCFI'.seedVertex_eq_subsetVertex_empty` | 1845-1848 | `seedVertex v` is the empty-subset case of `subsetVertex`. | — |
| `IsCFI'.subsetVertex_ne_endpointVertex` | 1850-1858 | Subset and endpoint vertices are distinct in `Fin n`. | — |
| `IsCFI'.adj_subsetVertex_endpoint_same_gadget_true_of_not_mem` | 1860-1868 | Fin-n witness adjacency: `adj (subsetVertex hS) (endpointVertex hw true) = 1` when w ∉ S. | — |
| `IsCFI'.adj_subsetVertex_endpoint_same_gadget_false_of_mem` | 1870-1878 | Fin-n witness adjacency: `adj (subsetVertex hS) (endpointVertex hw false) = 1` when w ∈ S. | — |
| `IsCFI'.adj_subsetVertex_endpoint_diff_gadget` | 1880-1889 | Fin-n cross-gadget non-adjacency between a subset vertex and an endpoint at a different gadget. | — |
| `IsCFI'.signature_endpoint_b0_ne_b1_general_allSeeds` | 1966-2017 | §13.15 M3.B+ — a b=0 endpoint at any gadget has a different signature from a b=1 endpoint at gadget v under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_endpoint_b0_ne_b1_general_allSeeds` | 2019-2033 | §13.15 M3.B+ — one `refineStep` round on `χ_{allSeeds}` distinguishes any b=0 endpoint from a b=1 endpoint at gadget v. | — |
| `IsCFI'.signature_subset_step` | 2057-2102 | §13.16 Subset-step signature distinction: given a within-gadget b=1 witness endpoint whose colour is absent from the second subset's adj=1 reach, the two subsets' signatures differ. | — |
| `IsCFI'.refineStep_subset_step` | 2104-2124 | §13.16 The generic subset-propagation step (Approach 3 primitive): under the no-match precondition one `refineStep` distinguishes two subset vertices, ready to instantiate at any cascade round. | — |
| `IsCFI'.signature_subset_inter_gadget_round2` | 2177-2212 | §13.17 Phase 2.3 — at round 2 on `χ_{allSeeds}`, two subset vertices at different gadgets have distinct signatures, given the LHS subset has a witness w ∈ N(v) \ S. | — |
| `IsCFI'.refineStep_subset_inter_gadget_round2` | 2214-2236 | §13.17 Phase 2.3 — at round 2, subset vertices at different gadgets get distinct colours (LHS subset needs a witness w ∈ N(v) \ S). | — |
| `IsCFI'.adj_subsetVertex_seedVertex` | 2260-2270 | Subset-subset non-adjacency: a subset vertex and a seed vertex are never adjacent. | — |
| `IsCFI'.signature_subsetVertex_ne_endpoint_true_allSeeds` | 2272-2318 | §13.18 M3.B++ — a subset vertex (any gadget) and a b=1 endpoint at gadget v have distinct signatures at round 1 under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_subsetVertex_ne_endpoint_true_allSeeds` | 2320-2333 | §13.18 M3.B++ — one `refineStep` round on `χ_{allSeeds}` distinguishes a subset vertex from a b=1 endpoint at gadget v. | — |
| `IsCFI'.signature_subsetVertex_ne_endpoint_false_round2` | 2359-2466 | §13.19 Cross-type round-2 signature distinction: a witnessed subset vertex and a b=0 endpoint (any gadget) differ at χ_1. | — |
| `IsCFI'.refineStep_subsetVertex_ne_endpoint_false_round2` | 2468-2485 | §13.19 Cross-type round-2 — at χ_2 a witnessed subset vertex and a b=0 endpoint (any gadget) get distinct colours. | — |
| `IsCFI'.signature_endpoint_false_inter_gadget_round3` | 2516-2616 | §13.20 Phase 2.2 — at χ_2, two b=0 endpoints at different gadgets have distinct signatures, given a witness subset at the LHS gadget. | — |
| `IsCFI'.refineStep_endpoint_false_inter_gadget_round3` | 2618-2645 | §13.20 Phase 2.2 — at round 3, b=0 endpoints at different gadgets get distinct colours, given a witness subset (exists when deg(v) ≥ 3). | — |
| `IsCFI'.exists_phase22_witness` | 2701-2750 | §13.21 Under `OddDegree`, for any v ∈ N(w) builds an even subset S ⊆ N(w) with v ∈ S plus a witness x ∈ N(w) \ S; used to invoke Phase 2.2 at a bridge-partner gadget. | — |
| `IsCFI'.refineStep_endpoint_false_intra_gadget_partner_round4` | 2774-2880 | §13.22 Phase 2.X — under `OddDegree`, at round 4 b=0 endpoints at the same gadget toward different partners (w ≠ w') get distinct colours. | — |
| `IsCFI'.refineStep_subset_intra_gadget_S_round5` | 2906-2991 | §13.23 Phase 2.4 — under `OddDegree`, at round 5 two subset vertices at the same gadget with S ≠ S' get distinct colours. | — |
## ChainDescent/Cascade.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `refineStep_mono` | 165-171 | One refinement round preserves refinement: `Refines χ₁ χ₂ → Refines (refineStep χ₁) (refineStep χ₂)`. | — |

## ChainDescent/CascadeOracle.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `refineStep_singleton_pair_eq` | 299-325 | After individualizing a singleton `s`, two other vertices sharing a colour one refinement round later have identical adjacency and order-relation to `s`. Arbitrary-singleton generalisation of `Scheme.refineStep_round1_pair_eq`. | — |

## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `individualizedColouring_singleton_eq_v_iff` | 694-707 | `χ_v` uniqueness: `individualizedColouring n {v} u = individualizedColouring n {v} v ↔ u = v`. | — |
| `signature_count_eq_card` | 926-937 | §8.b.2 Bridge lemma: `Multiset.count t (signature adj P χ w)` equals the cardinality of the matching `u' ≠ w` preimage filter. | — |
| `signature_eq_card_eq` | 939-952 | Count equality from signature equality: equal signatures give equal preimage-filter cardinalities for every tuple `t`. | — |
| `iter_succ_count_eq` | 954-969 | Iter-round count equality: `iter[k+1]` equality forces matching intermediate-vertex counts for every (round-k colour, adj, P) triple. | — |
| `signature_countP_eq_card` | 971-982 | §8.b.2 `countP` form of `signature_count_eq_card`. | — |
| `signature_eq_countP_eq` | 984-994 | Aggregate `countP` equality from signature equality, for any decidable predicate `p`. | — |
| `iter_succ_countP_eq` | 996-1012 | Aggregate iter-round count equality: under `iter[k+1]` equality, intermediate-vertex counts for any decidable `p` over (iter[k] colour, adj, P) match between `w` and `u`. | — |
| `iter_succ_colour_count_eq` | 1014-1033 | Colour-only specialisation of `iter_succ_countP_eq`: under `iter[k+1]` equality, the count of intermediate vertices whose round-k colour satisfies `q` matches between `w` and `u`. | — |
| `step2_at_depth_zero_of_rank_le_one` | 1430-1463 | Sanity instance: `Step2_at_depth G P v 0` for rank ≤ 1 schurian scheme graphs. | — |
| `schemePart_at_refl` | 1529-1537 | `schemePart_at G P v k` is reflexive. | — |
| `schemePart_at_symm` | 1539-1549 | `schemePart_at G P v k` is symmetric. | — |
| `schemePart_at_trans` | 1551-1563 | `schemePart_at G P v k` is transitive. | — |
| `step2_converges_at_zero_of_rank_le_one` | 1708-1719 | Sanity check: the convergence framework recovers the rank-≤-1 case at depth 0. | — |
| `schemePart_at_one_adj_to_v` | 1789-1794 | Depth-1 extraction, adj-only specialisation. | — |
| `relOfPairDetByAdjP_of_rank_le_one` | 1855-1879 | `rank ≤ 1` schurian scheme graphs trivially satisfy depth-1 separation. | — |
| `adjSeparates_of_rank_le_one` | 1955-1966 | `rank ≤ 1` ⇒ `AdjSeparatesRelations` (≤ 1 non-diagonal index). | — |
