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
| `closeStep_keeps_less` | 245-248 | `closeStep` never demotes a decided `less` entry. | — |
| `iterate_closeStep_keeps_less` | 250-260 | Iterating `closeStep` preserves any `less` entry — once decided, frozen. | — |
| `transitiveClose_conflict_less` | 273-280 | `transitiveClose conflictMatrix 0 1 = .less` (the `less`-chain wins the first `if`). | — |
| `transitiveClose_swap_conflict_less` | 282-290 | `transitiveClose (swap conflictMatrix) 0 1 = .less` — the σ-swap fails to flip the tie-break. | — |
| `POE.toNat_injective` | 328-330 | `POE.toNat` is injective. | — |
| `encTuple_injective` | 340-345 | `encTuple` is injective. | — |
| `witnessAdj` | 508-510 | Witness adjacency: the empty graph on 5 vertices (the `cell_split_uniform_false` discrepancy lives entirely in `P`). | Definition |
| `witnessP0` | 512-521 | Witness pre-guess matrix (`0 < 2`, `1 < 3`): cell-mates `0,1` relate symmetrically to the cell `{2,3}` but asymmetrically to vertices `2`, `3`. | Definition |
| `witnessChi` | 523-530 | Witness colouring with cells `{0,1}`, `{2,3}`, `{4}`. | Definition |
| `witnessTC` | 532-544 | Explicit `closeStep`-fixpoint of `applyGuess witnessP0 2 4 less` (`witnessP0` plus `2 < 4` plus the closure entry `0 < 4`). | Definition |
| `witnessTC_eq` | 546-558 | `transitiveClose (applyGuess witnessP0 2 4 less) = witnessTC`. | — |
| `witnessChi_stable` | 560-569 | `witnessChi` is 1-WL-stable for `(witnessAdj, witnessP0)`. | — |

| `closeStep_unknown_eq` | 1615-1627 | Expansion of `closeStep P i j` when `P i j = .unknown`, exposing the explicit `if`-chain. | — |
| `closeStep_unknown_subset` | 1855-1864 | The unknown-entry set of `closeStep P` is contained in that of `P`. | — |
| `cl_prov_canonical` | 1984-1989 | Every pair in `cl_prov S` is canonical (`p.1.val < p.2.val`). | — |
| `commitsToP_cl_prov_lessMono` | 1991-2009 | `commitsToP (cl_prov S)` is `.less`-bounded by `transitiveClose (commitsToP S)` for canonical `S`. | — |
| `Colouring.vertexRankNat_lt_n` | 3021-3035 | `vertexRankNat χ v < n` for every `v` (the rank is a valid `Fin n` value). | — |
## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CFIBase.edgeCountOrdered` | 102-104 | Ordered-pair edge count of the base graph, `∑ v, H.degree v`. | Definition |
| `CFIBase.cfiVertexCount_pos` | 138-145 | The CFI vertex count is positive whenever the base has at least one vertex (`0 < m`). | — |
| `Finset.card_powerset_filter_even` | 603-655 | Even-cardinality subsets of a nonempty finset count `2^(card−1)` — the classical combinatorial identity underlying `card_SubsetVertex`. | — |
| `CFIBase.card_evenSubsetsOfNeighbors` | 663-673 | `(H.evenSubsetsOfNeighbors v).card = 2^(H.degree v − 1)`. | — |
| `CFIBase.card_SubsetVertex` | 675-682 | `Fintype.card H.SubsetVertex = ∑ v, 2^(H.degree v − 1)`. | — |
| `CFIBase.card_EndpointVertex` | 684-693 | `Fintype.card H.EndpointVertex = ∑ v, 2 * H.degree v`. | — |
| `IsCFI'.adj_seed_endpoint_diff_gadget` | 945-953 | Cross-gadget non-adjacency: a seed and an endpoint in different gadgets (v ≠ v') are never adjacent. | — |
| `IsCFI'.adj_endpoint_seed_diff_gadget` | 955-962 | Cross-gadget non-adjacency (symmetric form): `adj (endpointVertex v' w b) (seedVertex v) = 0` when v ≠ v'. | — |
| `IsCFI'.adj_bridge` | 964-972 | An endpoint `e^b_{v→w}` is adjacent to its bridge partner `e^b_{w→v}` (Fin-n level). | — |
| `IsCFI'.endpointVertex_ne_bridge` | 974-996 | An endpoint and its bridge partner are distinct `Fin n` vertices. | — |
| `individualizedColouring_singleton_self_pos` | 1020-1024 | The individualized seed's colour is nonzero. | — |
| `individualizedColouring_singleton_eq_seed_iff` | 1026-1039 | Under a singleton individualization, a vertex shares the seed's colour iff it is the seed — only the seed carries the fresh colour. | — |
| `IsCFI'.signature_endpoint_false_ne_true` | 1058-1104 | §13.6 M2.4 — under the single-seed individualization, the b=0 and b=1 endpoints at gadget v toward w have distinct signature multisets. | — |
| `IsCFI'.refineStep_endpoint_false_ne_true` | 1112-1128 | §13.7 M2.5 — one `refineStep` round on a single-seed individualization gives gadget v's b=0 and b=1 endpoints distinct colours. | — |
| `IsCFI'.allSeeds_card_le_baseSize` | 1209-1212 | `|allSeeds| ≤ h.baseSize` (convenience inequality form). | — |
| `IsCFI'.signature_endpoint_false_ne_true_allSeeds` | 1231-1279 | §13.9 M3.B — multi-seed analogue of M2.4: under `χ_{allSeeds}` the b=0 and b=1 endpoints at gadget v have distinct signatures. | — |
| `IsCFI'.refineStep_endpoint_false_ne_true_allSeeds` | 1281-1295 | §13.9 M3.B — one `refineStep` round on `χ_{allSeeds}` splits gadget v's b=0 and b=1 endpoints by parity. | — |
| `IsCFI'.signature_endpoint_true_inter_gadget` | 1324-1369 | §13.10 M3.C — inter-gadget signature distinction: b=true endpoints at different gadgets (v ≠ v') differ under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_endpoint_true_inter_gadget` | 1371-1389 | §13.10 M3.C — one `refineStep` round on `χ_{allSeeds}` gives b=true endpoints at different gadgets distinct colours. | — |
| `IsCFI'.signature_bridge_step` | 1415-1466 | §13.11 M3.D — bridge-propagation signature step: if bridge partners are χ-distinguished and that colour is absent from the second endpoint's adj=1 reach, the two endpoints' signatures differ. | — |
| `IsCFI'.refineStep_bridge_step` | 1468-1492 | §13.11 M3.D Phase 1 — the local bridge-propagation step: under the no-match precondition, one `refineStep` distinguishes an endpoint pair from their distinguished bridge partners. The reusable inductive engine for the cascade. | — |
| `IsCFI'.refineStep_endpoint_true_intra_gadget_partner` | 1638-1702 | §13.13 Phase 2.1 — at round 2 on `χ_{allSeeds}`, b=true endpoints at the same gadget toward different partners (w ≠ w') get distinct colours. | — |
| `CFIBase.aEmpty_eq_subset_empty` | 1734-1736 | `aEmpty v` is the empty-subset case of `subset`. | — |
| `CFIBase.cfiAdj_subset_endpoint_same_gadget_true_of_not_mem` | 1738-1748 | `cfiAdj (a_S^v) (e^1_{v→w}) = 1` when w ∉ S — a non-saturated subset is adjacent to some b=1 endpoint. | — |
| `CFIBase.cfiAdj_subset_endpoint_same_gadget_false_of_mem` | 1750-1760 | `cfiAdj (a_S^v) (e^0_{v→w}) = 1` when w ∈ S. | — |
| `CFIBase.cfiAdj_subset_endpoint_diff_gadget` | 1762-1772 | Cross-gadget non-adjacency: `subset hS` at v is not adjacent to an endpoint at v' ≠ v. | — |
| `CFIBase.subset_ne_endpoint` | 1774-1781 | A subset vertex and an endpoint vertex are distinct CFI vertices. | — |
| `IsCFI'.seedVertex_eq_subsetVertex_empty` | 1805-1808 | `seedVertex v` is the empty-subset case of `subsetVertex`. | — |
| `IsCFI'.subsetVertex_ne_endpointVertex` | 1810-1818 | Subset and endpoint vertices are distinct in `Fin n`. | — |
| `IsCFI'.adj_subsetVertex_endpoint_same_gadget_true_of_not_mem` | 1820-1828 | Fin-n witness adjacency: `adj (subsetVertex hS) (endpointVertex hw true) = 1` when w ∉ S. | — |
| `IsCFI'.adj_subsetVertex_endpoint_same_gadget_false_of_mem` | 1830-1838 | Fin-n witness adjacency: `adj (subsetVertex hS) (endpointVertex hw false) = 1` when w ∈ S. | — |
| `IsCFI'.adj_subsetVertex_endpoint_diff_gadget` | 1840-1849 | Fin-n cross-gadget non-adjacency between a subset vertex and an endpoint at a different gadget. | — |
| `IsCFI'.signature_endpoint_b0_ne_b1_general_allSeeds` | 1926-1977 | §13.15 M3.B+ — a b=0 endpoint at any gadget has a different signature from a b=1 endpoint at gadget v under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_endpoint_b0_ne_b1_general_allSeeds` | 1979-1993 | §13.15 M3.B+ — one `refineStep` round on `χ_{allSeeds}` distinguishes any b=0 endpoint from a b=1 endpoint at gadget v. | — |
| `IsCFI'.signature_subset_step` | 2017-2062 | §13.16 Subset-step signature distinction: given a within-gadget b=1 witness endpoint whose colour is absent from the second subset's adj=1 reach, the two subsets' signatures differ. | — |
| `IsCFI'.refineStep_subset_step` | 2064-2084 | §13.16 The generic subset-propagation step (Approach 3 primitive): under the no-match precondition one `refineStep` distinguishes two subset vertices, ready to instantiate at any cascade round. | — |
| `IsCFI'.signature_subset_inter_gadget_round2` | 2137-2172 | §13.17 Phase 2.3 — at round 2 on `χ_{allSeeds}`, two subset vertices at different gadgets have distinct signatures, given the LHS subset has a witness w ∈ N(v) \ S. | — |
| `IsCFI'.refineStep_subset_inter_gadget_round2` | 2174-2196 | §13.17 Phase 2.3 — at round 2, subset vertices at different gadgets get distinct colours (LHS subset needs a witness w ∈ N(v) \ S). | — |
| `IsCFI'.adj_subsetVertex_seedVertex` | 2220-2230 | Subset-subset non-adjacency: a subset vertex and a seed vertex are never adjacent. | — |
| `IsCFI'.signature_subsetVertex_ne_endpoint_true_allSeeds` | 2232-2278 | §13.18 M3.B++ — a subset vertex (any gadget) and a b=1 endpoint at gadget v have distinct signatures at round 1 under `χ_{allSeeds}`. | — |
| `IsCFI'.refineStep_subsetVertex_ne_endpoint_true_allSeeds` | 2280-2293 | §13.18 M3.B++ — one `refineStep` round on `χ_{allSeeds}` distinguishes a subset vertex from a b=1 endpoint at gadget v. | — |
| `IsCFI'.signature_subsetVertex_ne_endpoint_false_round2` | 2319-2426 | §13.19 Cross-type round-2 signature distinction: a witnessed subset vertex and a b=0 endpoint (any gadget) differ at χ_1. | — |
| `IsCFI'.refineStep_subsetVertex_ne_endpoint_false_round2` | 2428-2445 | §13.19 Cross-type round-2 — at χ_2 a witnessed subset vertex and a b=0 endpoint (any gadget) get distinct colours. | — |
| `IsCFI'.signature_endpoint_false_inter_gadget_round3` | 2476-2576 | §13.20 Phase 2.2 — at χ_2, two b=0 endpoints at different gadgets have distinct signatures, given a witness subset at the LHS gadget. | — |
| `IsCFI'.refineStep_endpoint_false_inter_gadget_round3` | 2578-2605 | §13.20 Phase 2.2 — at round 3, b=0 endpoints at different gadgets get distinct colours, given a witness subset (exists when deg(v) ≥ 3). | — |
| `IsCFI'.exists_phase22_witness` | 2661-2710 | §13.21 Under `OddDegree`, for any v ∈ N(w) builds an even subset S ⊆ N(w) with v ∈ S plus a witness x ∈ N(w) \ S; used to invoke Phase 2.2 at a bridge-partner gadget. | — |
| `IsCFI'.refineStep_endpoint_false_intra_gadget_partner_round4` | 2734-2840 | §13.22 Phase 2.X — under `OddDegree`, at round 4 b=0 endpoints at the same gadget toward different partners (w ≠ w') get distinct colours. | — |
| `IsCFI'.refineStep_subset_intra_gadget_S_round5` | 2866-2951 | §13.23 Phase 2.4 — under `OddDegree`, at round 5 two subset vertices at the same gadget with S ≠ S' get distinct colours. | — |
| `card_symmDiff_mod_two` | 3225-3235 | **Parity helper.** `|S ∆ T| ≡ |S| + |T| (mod 2)` — the fact behind "an even subgraph preserves the even-subset invariant." | — |
| `xor_eq_xor_iff` | 3237-3239 | Xor right-cancellation on `Bool` (`(a⊕c) = (b⊕c) ↔ a = b`, and the `≠` form). | — |
| `xor_ne_xor_iff` | 3241-3243 | Xor right-cancellation on `Bool`, `≠` form: `(a ⊕ c) ≠ (b ⊕ c) ↔ a ≠ b` (companion to `xor_eq_xor_iff`). | — |
## ChainDescent/Cascade.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `refineStep_mono` | 179-185 | One refinement round preserves refinement: `Refines χ₁ χ₂ → Refines (refineStep χ₁) (refineStep χ₂)`. | — |

| `individualizedColouring_singleton_sep` | 3245-3252 | The individualized vertex `v` carries a unique colour: `individualizedColouring n {v}` separates `v` from every other vertex. Used in `cellsAreOrbits_schemeAdj_singleton`'s `w=v`/`u=v` cases. | — |
| `affV_card` | 552-555 | (Phase 2, M0.3) `card (F_p^d) = p^d` (via `Fintype.card_fun` + `ZMod.card`). | — |
| `instNonemptyAffV` | 723-727 | (Phase 2, M1.1 helper) `Nonempty (Fin (p^d))` (`p` prime ⟹ `p^d ≥ 1`). Needed for `orbitalIdx`/diagonal facts used outside the `affineScheme` definition. | Instance |
## ChainDescent/CascadeOracle.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `refineStep_singleton_pair_eq` | 472-497 | After individualizing a singleton `s`, two other vertices sharing a colour one refinement round later have identical adjacency and order-relation to `s`. Arbitrary-singleton generalisation of `Scheme.refineStep_round1_pair_eq`. | — |

## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme.relOfPair_self` | 133-137 | `relOfPair v v = 0`: the diagonal sits in `R_0`. | — |
| `AssociationScheme.schemeEquiv_refl` | 173-175 | Reflexivity of `schemeEquiv I` (needs `0 ∈ I`, via `relOfPair_self`). | — |
| `AssociationScheme.schemeEquiv_symm` | 177-179 | Symmetry of `schemeEquiv I` (free, via `relOfPair_symm` — relations are symmetric). | — |
| `AssociationScheme.schemeEquiv_equivalence` | 200-203 | A `ClosedSubset`'s induced relation is an `Equivalence` — the block system as a genuine equivalence relation. | — |
| `coe_inv_eq_symm` | 467-471 | (Phase 2, M0) `↑(g⁻¹) = (↑g).symm` as a permutation (subgroup coercion commutes with inversion). | — |
| `AssociationScheme.vProfile_self` | 584-588 | `vProfile S v v = 0`. | — |
| `AssociationScheme.vProfile_eq_iff` | 590-593 | `vProfile S v w = vProfile S v u ↔ relOfPair v w = relOfPair v u`. | — |
| `AssociationScheme.vProfile_eq_zero_iff` | 595-607 | `vProfile S v w = 0 ↔ w = v`: the diagonal-relation form. | — |
| `AssociationScheme.vProfile_ne_self_of_ne` | 609-616 | `v` is a singleton in `vProfile S v ·`: for `w ≠ v`, `vProfile S v w ≠ vProfile S v v`. Matches the `SchemeProfile.v_singleton` field. | — |
| `AssociationScheme.vProfile_aut_invariant` | 686-696 | §4.2 S1.a — a v-stabilizing scheme automorphism preserves `vProfile`: `vProfile S v (π w) = vProfile S v w`. | — |
| `vProfile_eq_of_schemeOrbit` | 700-708 | Trivial direction: `SchemeOrbitPartition` refines `vProfile`-equality. | — |
| `SchemeGraph.adj_eq_one_iff` | 870-874 | Adjacency characterisation: `adj v w = 1 ↔ relOfPair v w ∈ J`. | — |
| `SchemeGraph.adj_eq_zero_iff` | 876-880 | Non-adjacency characterisation: `adj v w = 0 ↔ relOfPair v w ∉ J`. | — |
| `SchemeGraph.adj_self` | 882-885 | Loopless: `adj v v = 0`. | — |
| `SchemeGraph.adj_eq_zero_or_one` | 893-898 | Adjacency takes values in `{0, 1}`. | — |
| `SchurianSchemeGraph.relOfPair_aut_eq` | 942-947 | Graph automorphisms of a `SchurianSchemeGraph` preserve `relOfPair`. | — |
| `SchurianSchemeGraph.vProfile_aut_invariant` | 949-954 | Graph automorphisms fixing `v` preserve `vProfile S v ·` (scheme-graph form, via `isAut_imp_isSchemeAut`). | — |
| `SchurianSchemeGraph.vProfile_eq_imp_graphOrbit` | 1008-1017 | Step 1 (forward, graph-Aut terms): equal `vProfile` implies graph-orbit equivalence. | — |
| `SchurianSchemeGraph.graphOrbit_imp_vProfile_eq` | 1019-1027 | Step 1 (reverse, graph-Aut terms): graph-orbit equivalence implies equal `vProfile`. | — |
| `SchurianSchemeGraph.vProfile_iff_graphOrbit` | 1029-1037 | Step 1 (graph-Aut combined): `vProfile` equality iff v-stabilized graph-Aut orbit equivalence — the form bridging to `OrbitPartition adj P {v}` in T2.M4. | — |
| `individualizedColouring_singleton_eq_v_iff` | 1090-1103 | `χ_v` uniqueness: `individualizedColouring n {v} u = individualizedColouring n {v} v ↔ u = v`. | — |
| `SchemeGraph.refineStep_round1_J_eq` | 1165-1195 | S2.a for scheme graphs: round-1 equality under `χ_v` forces matching J-class membership of `relOfPair v ·`. | — |
| `AssociationScheme.intersectionCount_eq_of_vProfile_eq` | 1267-1281 | Corollary: if `relOfPair v w = relOfPair v u`, the intersection counts at `(v,w)` and `(v,u)` coincide for every `(i, l)`. | — |
| `iter_succ_count_eq` | 1350-1365 | Iter-round count equality: `iter[k+1]` equality forces matching intermediate-vertex counts for every (round-k colour, adj, P) triple. | — |
| `signature_countP_eq_card` | 1367-1378 | §8.b.2 `countP` form of `signature_count_eq_card`. | — |
| `iter_succ_countP_eq` | 1392-1408 | Aggregate iter-round count equality: under `iter[k+1]` equality, intermediate-vertex counts for any decidable `p` over (iter[k] colour, adj, P) match between `w` and `u`. | — |
| `iter_succ_colour_count_eq` | 1410-1429 | Colour-only specialisation of `iter_succ_countP_eq`: under `iter[k+1]` equality, the count of intermediate vertices whose round-k colour satisfies `q` matches between `w` and `u`. | — |
| `iter_succ_adj_eq` | 1443-1457 | §8.b.3 S2.a lifted to any depth ≥ 1: `iter[k+1]` equality between non-`v` vertices forces matching adj-to-`v`. | — |
| `warmRefine_adj_eq` | 1459-1474 | warmRefine form of S2.a: two non-`v` vertices in the same warmRefine cell share adjacency to `v`. | — |
| `SchurianSchemeGraph.warmRefine_J_eq` | 1476-1500 | Two non-`v` vertices in the same warmRefine cell share J-class membership of `relOfPair v ·` — the coarsest non-trivial Step 2 refinement. | — |
| `SchurianSchemeGraph.schurian_scheme_profile_exists_of_step2` | 1563-1573 | Packages `toSchemeProfile` as the `Nonempty` existence result matching the `schurian_scheme_profile_exists` axiom. | — |
| `trivialPMatrix_invariant` | 1587-1591 | Every permutation preserves `trivialPMatrix`, discharging the P-invariance hypothesis automatically. | — |
| `theorem_2_HOR_concrete_trivialP` | 1656-1669 | `theorem_2_HOR_concrete` for trivial P: P-invariance becomes automatic, leaving only `Step2_target`. | — |
| `trivialSchurianSchemeGraph_step2` | 1697-1703 | `Step2_target` holds trivially on the 1-vertex scheme: any two vertices in `Fin 1` are equal. | — |
| `step2_of_rank_le_one` | 1737-1776 | §9.4 Step 2 for rank ≤ 1 schurian scheme graphs: `vProfile` takes only `0` (at `v`) and `1` (elsewhere), so warmRefine separation suffices. | — |
| `step2_of_step2_at_depth` | 1818-1826 | `Step2_at_depth G P v k` for `k ≤ n` lifts to `Step2_target G P v`. | — |
| `step2_at_depth_zero_of_rank_le_one` | 1828-1861 | Sanity instance: `Step2_at_depth G P v 0` for rank ≤ 1 schurian scheme graphs. | — |
| `ncard_setOf_eq_filter_card` | 1886-1893 | Bridge lemma: for `Fintype` and decidable `p`, `{x | p x}.ncard = (Finset.univ.filter p).card`. Bridges `Set.ncard`-based `schemePart_at` to `Finset.filter.card` outputs. | — |
| `schemePart_at_refl` | 1927-1935 | `schemePart_at G P v k` is reflexive. | — |
| `schemePart_at_symm` | 1937-1947 | `schemePart_at G P v k` is symmetric. | — |
| `schemePart_at_trans` | 1949-1961 | `schemePart_at G P v k` is transitive. | — |
| `schemePartFrom_refl` | 2094-2099 | §10.3b `schemePartFrom` is reflexive (induction on depth). | — |
| `schemePartFrom_symm` | 2101-2109 | §10.3b `schemePartFrom` is symmetric. | — |
| `schemePartFrom_trans` | 2111-2121 | §10.3b `schemePartFrom` is transitive — the equivalence property the realization induction consumes. | — |
| `step2_of_converges_at` | 2234-2245 | Step 2 from convergence plus the inductive step: `Step2_converges_at G P v k` with `k ≤ n` gives `Step2_target G P v`. | — |
| `step2_converges_at_zero_of_rank_le_one` | 2247-2258 | Sanity check: the convergence framework recovers the rank-≤-1 case at depth 0. | — |
| `schemePart_at_one_adj_to_v` | 2328-2333 | Depth-1 extraction, adj-only specialisation. | — |
| `relOfPairDetByAdjP_of_rank_le_one` | 2394-2418 | `rank ≤ 1` schurian scheme graphs trivially satisfy depth-1 separation. | — |
| `step2_of_det` | 2425-2435 | §10.7 `Step2_target G P v` from `RelOfPairDetByAdjP` (lifts depth-1 convergence). | — |
| `relOfPairDetByAdjP_of_adjSeparates` | 2476-2492 | `AdjSeparatesRelations` implies `RelOfPairDetByAdjP`. | — |
| `adjSeparates_of_rank_le_one` | 2494-2505 | `rank ≤ 1` ⇒ `AdjSeparatesRelations` (≤ 1 non-diagonal index). | — |
| `relOfPairDetByAdjP_of_rank_two_J_singleton` | 2553-2560 | Combined: `rank = 2` + `|J| = 1` ⇒ `RelOfPairDetByAdjP`. | — |
| `det2_of_det` | 2622-2629 | Depth-1 separation ⇒ depth-2 separation (ignores block-degrees). | — |
| `step2_of_det2` | 2662-2677 | Lifts `Step2_converges_at … 2` to `Step2_target` (`n < 2` vacuous via `Fin` subsingleton). | — |
| `schemePart_at_of_orbit` | 2724-2734 | A v-fixing `P`-preserving automorphism puts `w, u` in the same `schemePart_at k` class (`k ≤ n`). | — |
| `orbit_of_vProfile_eq` | 2736-2750 | `vProfile`-equality ⟹ `OrbitPartition` (schurian Step 1 plus P-invariance). | — |
| `ncard_eq_sum_POE` | 2752-2767 | P-value fibering of an `ncard`: the count splits over the finitely-many `POE` values of `P x ·`, dropping `P` from a block-degree count. | — |
| `vProfile_imp_schemePart_at` | 2963-2972 | The free ⊇ direction: same relation with `v` ⟹ same `schemePart_at k` class. | — |
| `schemePart_at_le` | 2974-2985 | `schemePart_at` is downward-monotone in the depth. | — |
| `AssociationScheme.relCommon_eq_intersectionNumber` | 2987-3002 | Common-neighbour count = structure constant: `#{u' : (v,u')∈R_l ∧ (z,u')∈R_m} = p^{relOfPair v z}_{l,m}`. | — |
| `relIsolatedAt_zero` | 3100-3114 | The diagonal `R_0 = {v}` is isolated at every depth. | — |
| `relIsolatedAt_mono` | 3116-3131 | Isolation is upward-closed in depth (`k ≤ j ≤ n`). | — |
| `mem_occursFromV` | 3310-3313 | Membership criterion: `l` occurs from `v` iff some `w` has `relOfPair v w = l`. | — |
| `zero_mem_occursFromV` | 3315-3317 | The diagonal relation `R₀` always occurs from `v`. | — |
| `occursFromV_card_le` | 3319-3322 | At most `n` relations occur from `v` — the bound that holds the closure depth at `≤ n`. | — |
| `mem_isolationStep` | 3342-3349 | Membership in one closure round: already isolated, or occurring from `v` and newly pinned. | — |
| `subset_isolationStep` | 3351-3355 | The closure round is extensive (`Iso ⊆ isolationStep`), feeding the generic saturation engine. | — |
| `isolationStep_subset_occursFromV` | 3357-3365 | The closure round preserves the `occursFromV` bound, so the engine saturates within `≤ n` steps. | — |
| `IsoPinned.mono` | 3499-3508 | Pinning is monotone in the isolated set: a uniquely-pinned relation stays pinned under any larger `Iso ⊇ Iso1`, letting a graded chain feed the closure's growing fixpoint. | — |
| `AssociationScheme.smul_schemeEquiv_class` | 3718-3733 | A `schemeEquiv I`-class moves under `g ∈ SchemeAutGroup` to the class of `g • a`: `g • {y | schemeEquiv I a y} = {y | schemeEquiv I (g•a) y}` (via `schemeEquiv_isSchemeAut`). | — |
## ChainDescent/Saturation.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Saturation.card_add_le_of_strict` | 83-95 | — | — |
## ChainDescent/CascadeAffine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `affinePermFin_apply` | 574-577 | (Phase 2, M0.3) `affinePermFin g₀ t i = affineE (g₀ (affineE.symm i) + t)`. | `@[simp]` |
| `mulUnitHom_apply` | 1042-1044 | F0: `mulUnitHom u x = ↑u * x`. | `@[simp]` |
| `conjHom_apply` | 1054-1056 | F0: `conjHom hd e u = efield hd (e (efield⁻¹ u))`. | `@[simp]` |
| `sigmaCyc_zpow_apply` | 1073-1081 | F0 (load-bearing): `σ^k` acts as multiplication by `α^k` through the field iso (`σ^k u = efield (α^k · efield⁻¹ u)`) — the `σ^k ↦ α^k` reduction both deliverables turn on. | — |
| `exists_npow_fqGen` | 1083-1091 | F0: every nonzero `z ∈ F_q` is a natural power of `α` (the multiplicative-orbit fact, for the irreducibility argument). | — |
| `frobLinear_apply` | 1169-1170 | F1: `frobLinear x = x ^ p`. | `@[simp]` |
| `frobLinear_mul` | 1172-1176 | F1: the **twist relation** `φ(α·x) = α^p · φ(x)` — Frobenius (a ring hom) carries mult-by-`α` to mult-by-`α^p`; the algebraic core of the gap. | — |
| `frobLinear_conj_mulUnit` | 1178-1187 | F1: `φ ∘ (mul α) ∘ φ⁻¹ = (mul α)^p` as linear automorphisms (conjugation carries the generator to its `p`-th power). | — |
| `sigmaPow_zpow_apply` | 1293-1299 | F2b: `σ_β^k` acts as multiplication by `β^k` through the field iso. Generalizes `sigmaCyc_zpow_apply`. | — |
| `frobLinear_conj_mulUnit'` | 1521-1528 | (separation step 1) `φ ∘ (mul β) ∘ φ⁻¹ = (mul β)^p` for arbitrary unit `β` (generalizes `frobLinear_conj_mulUnit`). | — |
