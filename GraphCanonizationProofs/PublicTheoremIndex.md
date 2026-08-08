# Public Theorem Index — GraphCanonizationProofs

Index of public Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project (active source), grouped by source file path. Archived counterparts live in `Archive/PublicTheoremIndex.md`. Private declarations live in `PrivateTheoremIndex.md`.

Maintained by `scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers`: the **Name**, **Line**, and **Notes** columns are computed from source; **Description** is hand-written and preserved. Prose between tables (this note, the Legend, `### …` sub-headers, per-file descriptions) is passed through untouched.
## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line. Gaps between theorems represent whitespace or comments.
- **Description**: What the declaration achieves / why a consumer would use it (not how it is proved), in ≤ 2 sentences. A leading `§…` section marker or **bold anchor** links it to the documentation.
- **Notes**: Computed from source — the infrastructure kind (`Definition`/`Structure`/`Inductive`/`Class`/`abbrev`/`axiom`/`Instance`), `noncomputable`, and `@[…]` attributes. `private` is omitted (it is encoded by the public/private index split).

## ChainDescent.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `POE` | 66-70 | Partial-order entries: the three values `less`, `unknown`, `greater` that populate a `PMatrix`. | Inductive |
| `neg` | 83-87 | Antisymmetric reverse on one entry: swaps `less`/`greater`, fixes `unknown`. | Definition |
| `neg_neg` | 89-90 | `neg` is an involution: `neg (neg e) = e`. | `@[simp]` |
| `POE.swap` | 92-95 | σ-swap on one entry (the matrix-wide relabelling of the direction-symmetry argument); coincides with `neg`. | Definition |
| `POE.swap_swap` | 97 | σ-swap is an involution: `swap (swap e) = e`. | `@[simp]` |
| `swap_less` | 99 | `swap .less = .greater`. | `@[simp]` |
| `swap_greater` | 100 | `swap .greater = .less`. | `@[simp]` |
| `swap_unknown` | 101 | `swap .unknown = .unknown`. | `@[simp]` |
| `PMatrix` | 107-108 | The partial-order matrix type `Fin n → Fin n → POE`. | Definition |
| `swap` | 114-115 | Pointwise σ-swap of a `PMatrix`: swap `less` with `greater` at every entry. | Definition |
| `swap_swap` | 117-118 | σ-swap is an involution on `PMatrix`: `swap (swap P) = P`. | `@[simp]` |
| `Antisymmetric` | 120-122 | A `PMatrix` is antisymmetric when `P i j = POE.neg (P j i)` for all `i, j`. | Definition |
| `AdjMatrix` | 131-132 | Self-contained adjacency matrix on `Fin n`, wrapping a `Fin n → Fin n → Nat` field. | Structure |
| `applyGuess` | 136-143 | Apply a single guess `(a, b, dir)` to `P`: set `P a b := dir`, `P b a := neg dir`, leaving every other entry unchanged. Does not transitively close. | Definition |
| `closeStep` | 170-183 | Single-step transitive closure: derive `P i j` from a uniform chain `i → k → j`, with `less`-chains taking priority over `greater`-chains at ties. | Definition |
| `transitiveClose` | 185-189 | Transitive closure of a `PMatrix` by iterating `closeStep` `n*n` times — enough rounds to reach fixpoint. | Definition |
| `conflictMatrix` | 220-233 | Concrete 4-vertex witness with a conflicted pair `(0,1)` carrying both a `less`-chain and a `greater`-chain; refutes σ-swap commutation. | Definition |
| `closeStep_keeps_less` | 235-238 | `closeStep` never demotes a decided `less` entry. | — |
| `iterate_closeStep_keeps_less` | 240-250 | Iterating `closeStep` preserves any `less` entry — once decided, frozen. | — |
| `closeStep_swap_false` | 252-261 | **Refutation:** `closeStep` does not commute with σ-swap unconditionally — the `less`-first tie-break is not σ-symmetric (fails on `conflictMatrix`). | — |
| `transitiveClose_swap_false` | 282-296 | **Refutation:** `transitiveClose` does not commute with σ-swap unconditionally (witnessed by `conflictMatrix`). | — |
| `Colouring` | 300-301 | A vertex colouring `Fin n → Nat`. | Definition |
| `signature` | 303-309 | Multiset signature of vertex `v` under colouring `χ` and state `(adj, P)`: the `(χ u, adj.adj v u, P v u)` tuples over all `u ≠ v`. | Definition |
| `POE.toNat` | 311-316 | Numeric code for a `POE` entry matching the C# packing: `less ↦ 0`, `unknown ↦ 1`, `greater ↦ 2`. | Definition |
| `encTuple` | 322-328 | Canonical injection of a signature tuple `(colour, edge-label, POE)` into `Nat` (Cantor pairing); mirrors the C# neighbour-tuple packing. | Definition |
| `sigKey` | 337-344 | Canonical refinement key of a vertex: its old colour followed by the sorted encoded signature multiset (the C# `[own-colour, sorted neighbour-tuples]`). | Definition |
| `sigKey_eq_iff` | 346-360 | Two vertices share a `sigKey` iff they have the same old colour and the same signature. | — |
| `warmRefine` | 389-399 | Warm 1-WL refinement: iterate `refineStep` `n` times from `initial`; concrete and computable. | Definition |
| `refineStep` / `refineStep_iff` | ~320-417 | **Concrete (2026-05-30, no longer axioms):** `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)` (own colour + sorted encoded signature = the C# `WarmPartition.RefineRound`); `refineStep_iff` (same colour ⟺ same old colour + same signature) is now a **theorem**. Removes `refineStep`/`refineStep_iff` from the axiom basis project-wide. Helpers: `POE.toNat`(_injective), `encTuple`(_injective), `sigKey`, `sigKey_eq_iff`. | Def + theorem |
| `samePartition` | 403-406 | Two colourings induce the same partition: `χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j` for every `i, j`. | Definition |
| `samePartition.refl` | 412 | `samePartition` is reflexive. | — |
| `samePartition.symm` | 414-415 | `samePartition` is symmetric. | — |
| `samePartition.trans` | 417-419 | `samePartition` is transitive. | — |
| `refineStep_refines` | 425-430 | **Refinement is split-only (one round).** Equal refined colour implies equal old colour. | — |
| `warmRefine_refines` | 432-458 | Warm refinement is split-only: equal warm-refined colour implies equal starting colour. | — |
| `iterate_closeStep_fix` | 490-496 | Iterating `closeStep` from a fixpoint of itself stays at that fixpoint. | — |
| `cell_split_uniform_false` | 561-586 | **Refutation:** cell-mates do not in general keep equal signatures after a guess plus TC (witnessed by `witnessP0`, the gap fixed only by singleton-cell `a`, `b`). | — |
| `iterate_refineStep_preserves_singleton` | 617-630 | Iterating refinement preserves a singleton for any number of rounds. | — |
| `signature_eq_of_samePartition` | 648-675 | **Signature equality is a partition invariant of the colouring:** partition-equal colourings induce the same signature-equality relation between vertices. | — |
| `warm_6_2` | 677-754 | **§6.2 direction invariance.** With `a, b` `χι`-singletons, warm refinement after `a < b` and after `b < a` induce the same partition. | — |
| `warmRefine_swap` | 770-812 | **Direction-blindness (Q1).** Warm refinement on `P` and on its σ-swap induce the same partition. | — |
| `applyGuess_comm` | 826-844 | **Q2 — guesses commute.** Guessing on `{a,b}` then `{b,c}` (pairwise-distinct vertices) gives the same `(adj, P)` as the reverse order, since the writes touch disjoint matrix entries. | — |
| `warmRefine_agree_off'` | 865-912 | **§6.2 — composable cross-branch sharing.** Matrices agreeing off `D` and `samePartition`-equal starting colourings (with `D` all `χ`-singletons) yield the same warm-refined partition; the cross-level form that chains across descent levels. | — |
| `warmRefine_agree_off` | 914-948 | **§6.2 — the cell partition depends only on the matrix off the decision set `D`.** Matrices agreeing off `D` (its vertices `χι`-singletoned) yield the same partition; the same-`χι` specialisation of `warmRefine_agree_off'`. | — |
| `PartitionInvariant` | 965-969 | A target-cell selector is partition-invariant when it depends only on the partition a colouring induces, not on raw colour values. | Definition |
| `target_direction_blind` | 971-980 | **§6.2 spine — base case.** For a partition-invariant selector, the target cell chosen after `a < b` equals the one after `b < a`. | — |
| `target_agree_off` | 982-995 | **§6.2 spine — inductive step.** For a partition-invariant selector and matrices agreeing off a singletoned decision set `D`, the target cell is the same even when the start colourings only agree up to partition. | — |
| `Egnd` | 40-41 | **§13.** The canonical ground set on `Fin n`: ordered pairs `(i, j)` with `i < j`. | Definition |
| `Pof` | 49-62 | **§13.** Commit a set `S ⊆ Egnd n` of pair-guesses into a P-matrix: write `less` at `(u,v) ∈ S`, `greater` at `(v,u)`, leaving other entries unchanged. | Definition, `noncomputable` |
| `cl` | 64-69 | **§13.** Propagation closure on pair-guesses: the canonical pairs whose endpoints get separated by warm refinement after committing `S`. | Definition |
| `SingletonAt` | 79-81 | The fresh-colour hypothesis at a pair `p`: both `p.1` and `p.2` are `χι`-singletons. | Definition |
| `cl_extensive` | 83-98 | **§13 M1 — extensiveness of `cl`.** For canonical `S` whose vertices are all `χι`-singletons, every pair in `S` lies in `cl S`. | — |
| `FullyDiscrete` | 164-166 | A colouring is fully discrete when every vertex is its own `χι`-singleton. | Definition |
| `cl_monotone_discrete` | 168-185 | **§13 M0, vacuous case.** Under `FullyDiscrete`, every canonical pair lies in every `cl S`, so `cl S = Egnd n` and monotonicity carries no structural information. | — |
| `TVerticesSingletons` | 198-200 | Every endpoint of every pair in `T` is a `χι`-singleton. | Definition |
| `warmRefine_samePartition_T_individualised` | 202-287 | **§13 M0, strong form.** Warm refinement under `Pof P₀ S` and `Pof P₀ T` induces the *same* partition when `S ⊆ T` and every endpoint of every `T`-pair is a `χι`-singleton. | — |
| `cl_monotone_T_individualised` | 289-300 | **§13 M0 — monotonicity of `cl`** under the T-individualised hypothesis: `S ⊆ T` implies `cl S ⊆ cl T`. | — |
| `cl_idempotent` | 326-340 | **§13 M2 — idempotence of `cl`** under fresh-colour individualisation of `S ∪ cl S`: `cl (cl S) = cl S`. | — |
| `Pof_fs` | 412-418 | **§14.** Finset-based computable analogue of `Pof`, enabling `decide`-checkable refutations. | Definition |
| `commitsToP` | 420-422 | **§14.** All-unknown-base commits-to-matrix shortcut: `Pof_fs (fun _ _ => .unknown) S`. | Definition |
| `cl_prov` | 424-429 | **§14.** Provenance closure (TC-based): the canonical pair-guesses whose direction is decided by `transitiveClose` of `commitsToP S`. | Definition |
| `cl_prov_empty` | 460-469 | **§14 CL0 for `cl_prov`:** `cl_prov ∅ = ∅`. | — |
| `cl_prov_extensive` | 471-485 | **§14 CL1 for `cl_prov`:** for canonical `S`, every commit's direct `less` write survives transitive closure, so `S ⊆ cl_prov S`. | — |
| `cl_prov_M3_false` | 503-513 | **§14 — refutes matroid M3 exchange for `cl_prov`.** A concrete `n=5, S={(1,2),(3,4)}, x=(2,3), y=(1,4)` counterexample where the M3 premise holds but the conclusion fails; machine-checked by `decide`. | — |
| `hasLessChain` | 527-530 | Existence of a `.less`-chain in `P` from `i` to `j` via some intermediate `k` with both edges `.less`. | Definition |
| `hasGreaterChain` | 532-534 | Existence of a `.greater`-chain in `P` from `i` to `j` via some intermediate `k`. | Definition |
| `CanConsistent` | 536-540 | A `PMatrix` is canonical-consistent when every `.less` entry sits at `i.val < j.val` and every `.greater` entry at `i.val > j.val`. | Definition |
| `LessMono` | 542-545 | One-sided `.less`-direction entry-wise monotonicity between two matrices: `P i j = .less → Q i j = .less`. | Definition |
| `cl_prov_monotone` | 815-840 | **§14 CL3 — monotonicity for `cl_prov`:** canonical `S ⊆ T` implies `cl_prov S ⊆ cl_prov T`. | — |
| `numUnknown` | 849-852 | Number of `.unknown` entries in a `PMatrix` — the strictly-decreasing potential bounding TC iteration. | Definition |
| `transitiveClose_idempotent` | 980-986 | **TC idempotence.** `transitiveClose (transitiveClose M) = transitiveClose M`. | — |
| `cl_prov_idempotent` | 1017-1047 | **CL2 — idempotence.** `cl_prov (cl_prov S) = cl_prov S` for canonical `S`. | — |
| `IndivStep` | 72-96 | Existential witness of one descent-step individualisation: a colouring `χ'` that singletons every vertex in target `T` and refines `χ` outside `T`. Data, not a function — the trace carries one per step. | Structure |
| `singletons_union` | 100-121 | **D-singletons preserved.** If `χ` singletons every `v ∈ D`, an `IndivStep` with target `T` singletons every `v ∈ D ∪ T`. | — |
| `IndivStep.default` | 155-206 | **Concrete `IndivStep` witness.** A constructive individualisation step (parity-tagged base-`n` encoding), proving traces exist at every level so the spine theorem is non-vacuous. | Definition |
| `DescentTrace` | 215-253 | Inductive predicate: `(D, P, χι)` is reachable by `k` descent steps from `(P₀, χι₀)` under selector `sel`, each step carrying an `IndivStep` witness and a matrix agreeing with `P₀` off the enlarged decision set. | Inductive |
| `singletons` | 257-274 | **Trace invariant.** A trace's colouring singletons its whole decision set `D`. | — |
| `P_agrees` | 276-286 | **Trace invariant.** A trace's matrix agrees with `P₀` on every entry with an endpoint outside `D`. | — |
| `SpineChain` | 290-298 | Bundle of a `DescentTrace` with its derived state `(D, P, χι)`. The spine theorem is branch-independence of two such chains. | Structure |
| `partition` | 305-309 | The chain's level-`k` partition: warm refinement of its accumulated `(P, χι)`. | Definition |
| `spine_branch_independent` | 330-404 | **The spine theorem (branch independence).** Any two `DescentTrace`s through `k` levels agree on the accumulated `D` (literal) and the level-`k` partition (`samePartition`) — handing the oracle one fixed partition instead of `2^d` refinement worlds. | — |
| `SpineChain.branch_independent` | 406-415 | **The spine theorem, `SpineChain` wrapper.** Two chains at level `k` share `D` and level-`k` partition. | — |
| `defaultColouring` | 436-446 | The level-`k` colouring of the default reference chain: iterate refine-then-individualise (via `IndivStep.default`) from `χι₀`, with the matrix held fixed at `P₀`. | Definition |
| `defaultD` | 448-457 | The level-`k` decision set of the default chain: accumulate `sel (warmRefine adj P₀ (defaultColouring k))` across all levels. | Definition |
| `defaultTrace` | 459-472 | The concrete `DescentTrace` realising the default construction, using `IndivStep.default` at every level and `P = P₀` throughout. | Definition |
| `defaultSpineChain` | 474-482 | The concrete reference `SpineChain` at every level, bundling `defaultD`/`P₀`/`defaultColouring`/`defaultTrace`. | Definition |
| `SpineChain.eq_default` | 484-495 | **Reference corollary.** Every `SpineChain` at level `k` shares `D` and level-`k` partition with `defaultSpineChain` — there is a canonical level-`k` partition, computable by one deterministic descent. | — |
| `Discrete` | 519-522 | A colouring is discrete when every cell is a singleton — equivalently, `χ : Fin n → Nat` is injective. | Definition |
| `of_samePartition` | 526-530 | Discreteness is `samePartition`-invariant: equal partitions transport `Discrete`. | — |
| `SpineChain.IsLeaf` | 545-551 | A `SpineChain` reaches a leaf when its level-`k` partition is discrete (every vertex a singleton). | Definition |
| `TargetsNonsingletonCell` | 566-572 | Selector hypothesis: every returned vertex has a same-colour partner (`sel` only picks from non-singleton cells). | Definition |
| `NonemptyOnNonDiscrete` | 574-579 | Selector hypothesis: `sel χ` is non-empty whenever `χ` is not yet discrete. | Definition |
| `defaultD_univ_isLeaf` | 581-596 | **`D` covers all vertices ⇒ leaf.** When the accumulated decision set is the full vertex set, the default chain's spine partition is discrete. | — |
| `defaultD_grows_if_not_leaf` | 598-637 | **`D` strictly grows on every non-leaf step.** Under the two selector hypotheses, a non-leaf level-`k` chain has `|defaultD k| < |defaultD (k+1)|`. | — |
| `defaultSpineChain_reaches_leaf` | 639-678 | **Leaf existence.** Under `TargetsNonsingletonCell` and `NonemptyOnNonDiscrete`, the default descent reaches a leaf within `n` levels. | — |
| `DirAssignment` | 701-707 | Order assignment relative to `(P₀, D)`: an antisymmetric matrix agreeing with `P₀` on every entry with an endpoint outside `D`. The linear oracle's input shape — a point in the order-label residual. | Structure |
| `default` | 2769-2776 | **Trivial `DirAssignment`.** When `P₀` is antisymmetric, `P₀` itself is a valid order assignment for any `D` (witnesses non-emptiness). | Definition |
| `samePartition_pair` | 722-734 | Any two `DirAssignment`s over the same `(P₀, D)`, refined against a `D`-singletoning colouring, induce the same partition. | — |
| `samePartition_chain` | 736-749 | **Spine equivalence.** A `DirAssignment` over a chain's `D`, refined against the chain's colouring, induces the chain's partition — the residual is exactly the choice of `DirAssignment`, partition fixed. | — |
| `flipPair` | 753-797 | **Single-pair direction flip.** Negate the `(a, b)` and `(b, a)` entries of a `DirAssignment` via `POE.neg`. The generator of the `Z₂` group action on direction choices. | Definition |
| `flipPair_idempotent` | 811-820 | **Flip is an involution.** Two applications of `flipPair` to the same pair return the original `DirAssignment` — the `Z₂` generator squares to identity. | — |
| `flipPair_partition_invariant` | 822-832 | **Flipping preserves the partition.** `σ` and `σ.flipPair a b` share the spine partition — the order labels move, the partition doesn't. | — |
| `flipPair_comm` | 834-858 | **Flips on disjoint pairs commute** — the abelian-ness of the `Z₂^d` action: distinct decisions don't interfere. | — |
| `IsAut` | 886-889 | A `Fin n`-permutation `π` is a graph automorphism of `adj` when it preserves adjacency edge-by-edge: `adj.adj (π v) (π w) = adj.adj v w`. | Definition |
| `IsAut.refl` | 895-896 | The identity permutation is an automorphism. | — |
| `IsAut.trans` | 898-903 | Composition of automorphisms is an automorphism. | — |
| `IsAut.symm` | 905-911 | The inverse of an automorphism is an automorphism. | — |
| `labelledAdj` | 915-921 | **Labelled adjacency.** Adjacency matrix relabelled by `π`: entry `(i, j)` is the original adjacency between `π⁻¹ i` and `π⁻¹ j`. | Definition |
| `labelledAdj_eq_of_isAut` | 923-936 | **Automorphisms fix the labelled adjacency.** `IsAut π adj` implies `labelledAdj π adj = adj.adj` — an automorphism is invisible at the labelled level. | — |
| `isAut_of_labelledAdj_eq` | 938-948 | **Converse.** A permutation preserving the labelled adjacency is an automorphism. | — |
| `vertexRankNat` | 961-963 | Strict rank of vertex `v`: the count of vertices `u` with `χ u < χ v`. | Definition |
| `vertexRank` | 981-983 | Vertex rank packaged as `Fin n` via `vertexRankNat_lt_n`. | Definition |
| `rankPerm` | 1023-1027 | **The rank permutation.** Bijection `Fin n ≃ Fin n` mapping each vertex to its colour-rank on a `Discrete` colouring. | Definition, `noncomputable` |
| `rankPerm_apply` | 1029-1030 | Unfolding lemma: `rankPerm χ h v = vertexRank χ v`. | `@[simp]` |
| `vertexRank_comp` | 1034-1053 | `vertexRank (χ ∘ g) v = vertexRank χ (g v)` — a pure `Finset.card` reindex along `g`. *(Relocated from `LinearOracle.lean` for the cascade oracle's `colourMatchPerm` (M-B).)* | — |
| `rankPerm_comp` | 1055-1075 | **Rank reindexing.** `rankPerm (χ ∘ e) = rankPerm χ · e` — relabelling conjugate-shifts the rank permutation (the §L.5 conjugation gap). *(Relocated from `LinearOracle.lean`.)* | — |
| `SpineChain.canonAdj` | 1091-1117 | **Leaf canonical adjacency.** Given a leaf `SpineChain` and a `DirAssignment σ` over its `D`, relabel `adj` by the rank permutation of the warm-refined partition. | Definition, `noncomputable` |
| `matrixLT` | 1121-1128 | **Row-major lex strict less-than on `n × n` matrices.** The first disagreeing cell `(i, j)` (row-then-column order) has `M₁ i j < M₂ i j`. | Definition |
| `PMatrix.fintype` | 1160-1165 | `Fintype` instance for `PMatrix n`, stated explicitly since `PMatrix` is a `def` and so does not inherit the `Pi` instance transparently. | Instance |
| `DirAssignment.fintype` | 1171-1181 | **`Fintype` on `DirAssignment P₀ D`.** Obtained by injecting the σ-field into the `Fintype` `PMatrix n`. | Instance, `noncomputable` |
| `relabelMatrix` | 1185-1192 | **Relabel a bare matrix** `Fin n → Fin n → Nat` by a permutation `π`: entry `(i,j)` becomes `M (π⁻¹ i) (π⁻¹ j)`. Lets `LeafTwistSpec` state the leaf-relabelling property without re-wrapping as an `AdjMatrix`. | Definition |
| `MatrixLex` | 1194-1199 | `Fin n → Fin n → Nat` viewed under the row-major lex order via nested `Pi.Lex`. | `abbrev` |
| `toMatrixLex` | 1201-1204 | Wrap a matrix into its Lex'd form (identity at runtime — `Lex` is a type synonym). | Definition |
| `ofMatrixLex` | 1206-1208 | Unwrap a Lex'd matrix back to a plain `Fin n → Fin n → Nat`. | Definition |
| `ofMatrixLex_toMatrixLex` | 1210-1211 | `ofMatrixLex (toMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_ofMatrixLex` | 1213-1214 | `toMatrixLex (ofMatrixLex M) = M`. | `@[simp]` |
| `canonFormImages` | 1222-1231 | The Finset of Lex-wrapped `canonAdj` images over all `DirAssignment`s for a leaf chain — the candidate set `canonForm` minimises over. | Definition, `noncomputable` |
| `canonForm` | 1241-1261 | **The canonical leaf adjacency matrix:** the lex-min `canonAdj` over all `DirAssignment`s (row-major lex). Requires `Nonempty (DirAssignment P₀ chain.D)`. | Definition, `noncomputable` |
| `canonForm_mem_image` | 1263-1278 | **`canonForm` comes from some `DirAssignment`:** it equals `canonAdj σ` for some `σ`. | — |
| `canonForm_le_canonAdj` | 1280-1296 | **`canonForm` is the lex-minimum:** `toMatrixLex (canonForm) ≤ toMatrixLex (canonAdj σ)` for every `DirAssignment σ`. | — |
| `LinearOracleSpec` | 1300-1316 | **The linear-oracle interface type:** given a leaf chain and a current-branch `DirAssignment`, return either `none` or a verified automorphism of `adj` (bundled as a subtype). | Definition |
| `some_isAut` | 3379-3391 | **Soundness (subtype-level):** when the oracle returns `some result`, the returned permutation is automatically an automorphism. | — |
| `LeafTwistSpec` | 1337-1354 | **Leaf-twist validity spec:** when the oracle returns `some result`, the returned `π` relabels the input branch's canonical adjacency to that of some other `DirAssignment σ'` — the property justifying pruning. | Definition |
| `individualizedColouring` | 45-49 | **Fresh-colour individualisation** of a vertex set `S`: each `v ∈ S` gets unique colour `v.val + 1`; vertices outside `S` share colour `0`. | Definition |
| `FixesPointwise` | 51-54 | Predicate: permutation `π` fixes every vertex in `S` pointwise (`π v = v` for `v ∈ S`). | Definition |
| `complement` | 60-68 | A pointwise-fixing permutation stabilises the complement setwise: `v ∉ S` implies `π v ∉ S`. | — |
| `individualizedColouring_invariant` | 72-81 | An automorphism fixing `S` pointwise preserves the individualised colouring: `χ_S (π v) = χ_S v` for every `v`. | — |
| `warmRefine_invariant_of_isAut` | 157-166 | Warm refinement preserves automorphism invariance: if `(adj, P, χ_init)` are all `π`-invariant, so is `warmRefine adj P χ_init`. | — |
| `signature_transport` | 180-205 | **Signature transport.** An automorphism `g` carrying `(P₁, χ₁)` to `(P₂, χ₂)` maps the `(P₂, χ₂)`-signature at `g v` to the `(P₁, χ₁)`-signature at `v`. Cross-config form of `signature_invariant_of_isAut`. | — |
| `sigKey_transport` | 207-214 | **`sigKey` transport** — cross-config: `sigKey adj P₂ χ₂ (g v) = sigKey adj P₁ χ₁ v`. | — |
| `refineStep_transport` | 216-224 | **`refineStep` transport** — one round, cross-config: `refineStep adj P₂ χ₂ (g v) = refineStep adj P₁ χ₁ v`. | — |
| `iterate_refineStep_transport` | 226-240 | **Iterated `refineStep` transport** across any number of rounds, cross-config. | — |
| `warmRefine_transport` | 242-251 | **Warm-refinement transport.** An automorphism carrying `(P₁, χ₁)` to `(P₂, χ₂)` carries the warm refinement of the first onto the second. | — |
| `OrbitPartition` | 267-273 | **Aut_S orbit relation** on vertices: `v ~ w` iff some automorphism of `adj` preserving `P` and fixing `S` pointwise sends `v` to `w`. | Definition |
| `refl` | 412 | Reflexivity of `OrbitPartition` (via the identity permutation). | — |
| `symm` | 414-415 | Symmetry of `OrbitPartition` (via permutation inverse). | — |
| `trans` | 417-419 | Transitivity of `OrbitPartition` (via permutation composition). | — |
| `subset_warmRefine` | 318-333 | **Trivial direction of the squeeze:** orbits refine 1-WL cells — `OrbitPartition v w` implies `warmRefine` colours of `v` and `w` agree. | — |
| `refineStep_iter_le_eq` | 346-364 | Refinement is split-only across iterations: equality at iterate `k + d` implies equality at iterate `k`. | — |
| `warmRefine_eq_iter_eq` | 366-380 | `warmRefine` equality implies iterate-`r` equality for any `r ≤ n`; the bridge from the fixpoint partition to any earlier-round partition. | — |
| `id_of_discrete_invariant` | 405-414 | **Fact B (pointwise):** a `π`-invariant discrete colouring forces `π` to be the identity. | — |
| `aut_trivial_of_discrete_warmRefine` | 416-432 | **Fact B (CFI):** if `warmRefine adj P χ_S` is discrete, every automorphism preserving `(adj, P)` and fixing `S` pointwise is the identity. | — |
| `orbit_iff_eq_of_discrete_warmRefine` | 434-452 | **Fact B (partition):** at discrete depth, `OrbitPartition adj P S v w ↔ v = w`. | — |
| `CascadesAt` | 474-481 | **Cascade-at-depth-`k` predicate:** some `S` with `S.card ≤ k` makes `warmRefine adj P (individualizedColouring n S)` discrete. | Definition |
| `cascadesAt_univ` | 483-502 | **Trivial cascade at depth `n`:** taking `S = univ` gives a discrete starting colouring preserved by warm refinement — the every-graph fallback. | — |
| `theorem_1_HOR_at_depth` | 522-545 | **Key theorem (Tier 1 HOR).** If `adj` cascades at depth `k`, some `S` with `S.card ≤ k` makes `warmRefine` discrete and the `Aut_S`-orbit partition equal to the `warmRefine` partition. | — |
| `theorem_1_HOR_at_n` | 567-578 | **Theorem 1, trivial-bound corollary:** every graph admits orbit recovery at depth `n`. Axiom-free specialisation to `cascadesAt_univ`. | — |
| `theorem_1_HOR` | 580-591 | **Theorem 1 (legacy existential form):** some `S` makes `warmRefine` discrete and orbits equal cells. | — |
| `theorem_1_HOR_pointwise` | 593-605 | **Theorem 1, pointwise corollary:** at the cascade depth, every automorphism preserving `(adj, P)` and fixing `S` is the identity. | — |
| `SchemeProfile` | 658-674 | **Key structure (Tier 2).** Bundles a v-profile colouring with its structural facts: profile classes equal `Aut_v` orbits (schurian Step 1) and 1-WL refines the profile partition (intersection-number Step 2). | Structure |
| `warm_iff_profile` | 680-693 | **Squeeze for `SchemeProfile`:** the 1-WL fixpoint partition equals the profile partition. | — |
| `theorem_2_HOR_of_profile` | 709-725 | **Theorem 2 (assembly form):** given a `SchemeProfile` witness at `v`, the 1-WL fixpoint partition at depth 1 equals the `Aut_v`-orbit partition. The axiom-free assembly lemma `Scheme.lean`'s `theorem_2_HOR_concrete` consumes (the placeholder axioms `IsSchurianSchemeGraph` / `schurian_scheme_profile_exists` and the conditional `theorem_2_HOR` were retired 2026-06-05). | — |

## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CFIBase` | 49-60 | §1 A **CFI base graph** on `Fin m`: a simple (symmetric, loopless) `AdjMatrix m` with every vertex of degree at least 2 — the structural prerequisite for building CFI gadgets. | Structure |
| `neighbors` | 68-70 | The neighbour set of `v` in the base graph, as a `Finset (Fin m)`. | Definition |
| `degree` | 72-73 | The degree of `v` in the base graph: `(H.neighbors v).card`. | Definition |
| `mem_neighbors` | 75-78 | Membership characterisation: `w ∈ H.neighbors v ↔ H.adj.adj v w ≠ 0`. | `@[simp]` |
| `not_self_mem_neighbors` | 83-87 | No vertex is its own neighbour (looplessness): `v ∉ H.neighbors v`. | — |
| `mem_neighbors_symm` | 89-92 | The neighbour relation is symmetric: `w ∈ H.neighbors v ↔ v ∈ H.neighbors w`. | — |
| `gadgetSize` | 109-111 | §3 Size of the CFI gadget at base vertex `v`: `2^(degree v − 1) + 2 * degree v` — even-subset vertices plus endpoint vertices. | Definition |
| `cfiVertexCount` | 113-115 | Total vertex count of `CFI(H)`: `∑ v, H.gadgetSize v`. | Definition |
| `evenSubsetsOfNeighbors` | 145-148 | §4 The `Finset` of even-cardinality subsets of `N(v)`; indexes the subset vertices `a_S^v` of `CFI(H)`. | Definition |
| `mem_evenSubsetsOfNeighbors` | 155-159 | Membership: `S ∈ evenSubsetsOfNeighbors v ↔ S ⊆ N(v) ∧ S.card % 2 = 0`. | `@[simp]` |
| `triangleBase` | 169-180 | §5 The triangle `K_3` as a `CFIBase 3`: the smallest base graph satisfying the degree-≥-2 invariant; the running smoke-test base. | Definition |
| `SubsetVertex` | 211-213 | §6 Type-level encoding of subset vertices of `CFI(H)`: pairs `(v, S)` with `S ∈ evenSubsetsOfNeighbors v`. | `abbrev` |
| `EndpointVertex` | 215-218 | §6 Type-level encoding of endpoint vertices of `CFI(H)`: triples `(v, w, b)` with `w ∈ N(v)` and `b : Bool`. | `abbrev` |
| `CFIVertex` | 220-228 | §6 The vertex type of `CFI(H)`: the sum `SubsetVertex ⊕ EndpointVertex`. | `abbrev` |
| `triangleBase_cfiVertex_card` | 282-284 | §7 Smoke test: `Fintype.card triangleBase.CFIVertex = 18`, matching `cfiVertexCount`. | — |
| `cfiAdj` | 310-323 | §8 **The CFI adjacency function** on `CFIVertex H`, returning 0/1 per the subset/endpoint clauses and the untwisted inter-gadget bridge formula. | Definition |
| `cfi_triangle_no_twins` | 395-398 | §8.1 `CFI(triangle)` has no twin pairs: any two distinct vertices are separated by some third vertex. Confirms CFI's `Z₂` is a global gadget-flip, not a transposition — so the twin slice and CFI are complementary abelian classes. | — |
| `cfiAdjMatrix` | 425-435 | §9 **The CFI adjacency matrix** on `Fin (Fintype.card H.CFIVertex)`, lifting `cfiAdj` through `Fintype.equivFin`. | Definition, `noncomputable` |
| `IsCFI'` | 451-471 | §9 **Concrete `IsCFI` predicate.** A witness that `adj : AdjMatrix n` is the CFI of some base `H : CFIBase m`, exposing the base graph and bijection `Fin n ≃ H.CFIVertex` as addressable data. | Structure |
| `IsCFI'.baseSize` | 473-478 | The base graph's vertex count `h.m` for a CFI witness `h`; the depth-bound API ties `cfi_depth_bound h` to `h.baseSize`. | `abbrev` |
| `cfiAdjMatrix_is_cfi` | 480-511 | **Self-witness**: every `H.cfiAdjMatrix` satisfies `IsCFI'`, with `H` itself as the base. | Definition, `noncomputable` |
| `cfi_depth_bound` | 542-556 | §10 **Cascade-depth function for CFI graphs**, concretely `h.baseSize` (discharges the former axiom in Stage-4 M1). | Definition |
| `cfi_depth_bound_le` | 558-573 | **The CFI depth bound is `≤ baseSize`**, trivial after the M1 concretization. | — |
| `card_CFIVertex` | 687-694 | §11 **The cardinality identity**: `Fintype.card H.CFIVertex = H.cfiVertexCount` — the abstract vertex type matches the gadget-size sum formula. | — |
| `IsCFI'.six_baseSize_le` | 712-746 | §12 **Connector**: a CFI graph has at least `6 * baseSize` vertices (each gadget contributes ≥ 6) — yields the `n/6` depth bound. | — |
| `aEmpty` | 765-770 | §13.1 The canonical seed vertex `a_∅^v` of `CFI(H)`: the subset vertex at gadget `v` with the empty subset, individualized by the M2-M4 cascade. | Definition |
| `endpoint` | 772-775 | §13.1 The endpoint vertex `e^b_{v→w}` of `CFI(H)` at gadget `v`, pointing toward `w ∈ N(v)` with parity bit `b`. | Definition |
| `cfiAdj_aEmpty_endpoint_diff_gadget` | 807-820 | **Cross-gadget non-adjacency**: `cfiAdj (a_∅^v) (e^b_{v'→w}) = 0` when `v ≠ v'`. | — |
| `cfiAdj_bridge` | 822-838 | **The bridge edge**: `cfiAdj (e^b_{v→w}) (e^b_{w→v}) = 1` — same-parity endpoints at neighbouring gadgets pointing toward each other. | — |
| `IsCFI'.seedVertex` | 851-855 | §13.3 The `Fin n` vertex corresponding to the seed `a_∅^v` for an `IsCFI'` witness — what the cascade individualizes. | Definition |
| `IsCFI'.endpointVertex` | 857-861 | §13.3 The `Fin n` vertex corresponding to `e^b_{v→w}` for an `IsCFI'` witness — the endpoints the cascade probes. | Definition |
| `e_seedVertex` | 867-871 | Bijection round-trip: `h.e (h.seedVertex v) = h.H.aEmpty v`. | `@[simp]` |
| `e_endpointVertex` | 873-878 | Bijection round-trip: `h.e (h.endpointVertex hw b) = h.H.endpoint hw b`. | `@[simp]` |
| `individualizedColouring_singleton_self` | 1001-1004 | Individualizing a single seed gives it colour `seed.val + 1`. | `@[simp]` |
| `individualizedColouring_singleton_other` | 1006-1010 | Under a singleton individualization, every non-seed vertex gets colour `0`. | `@[simp]` |
| `individualizedColouring_eq_iff_of_mem` | 1137-1153 | Multi-seed uniqueness: under `individualizedColouring n S`, for `v ∈ S` a vertex shares v's colour iff it equals v. Generalises the singleton form to arbitrary S. | — |
| `allSeeds` | 1159-1166 | §13.8 The cascade individualization set `{seedVertex v : v ∈ Fin m}` — one seed per base vertex; the witness used in `cfi_cascades_polynomially`. | Definition |
| `allSeeds_card` | 1193-1199 | `|allSeeds| = h.baseSize`; with `six_baseSize_le` the cascade individualization has at most n/6 vertices. | `@[simp]` |
| `adj_endpointVertex_eq_one_iff` | 1498-1520 | §13.12 Endpoint-endpoint adjacency characterisation: two endpoints are adjacent iff they form a bridge pair (`v_a = w_b ∧ w_a = v_b ∧ b_a = b_b`). | — |
| `subset` | 1719-1724 | §13.14 The CFI vertex `a_S^v`: the subset vertex at gadget v with even subset S ⊆ N(v). Generalises `aEmpty v` (the S = ∅ case). | Definition |
| `IsCFI'.subsetVertex` | 1777-1783 | §13.14 The `Fin n` vertex for `a_S^v`. Generalises `seedVertex v` (the empty-subset case). | Definition |
| `e_subsetVertex` | 1789-1795 | Bijection round-trip: `h.e (subsetVertex hS) = subset hS`. | `@[simp]` |
| `adj_subsetVertex_eq_one_iff` | 1843-1896 | §13.14 Subset-adjacency characterisation: `adj u (subsetVertex_{v'} hS') = 1` iff u is an endpoint at v' whose parity satisfies `(w' ∈ S') ⊕ b`. Generalises `adj_seedVertex_eq_one_iff` (S' = ∅). | — |
| `IsCFI'.adj_symm` | 2095-2099 | §13.16.5 CFI adjacency is symmetric at the `Fin n` level: `adj.adj i j = adj.adj j i`. | — |
| `OddDegree` | 2625-2628 | §13.21 Odd-degree CFI base: every base vertex has odd degree, ensuring no even subset of N(v) is saturated. Hypothesis for the axiom-free cascade (covers K₄, K₃,₃, Petersen). | Definition |
| `cfi_cascades_polynomially_oddDeg` | 2963-3167 | §13.24 M4 — for OddDegree CFI graphs, `warmRefine adj P χ_{allSeeds}` is `Discrete`; discharges `CascadesAt` (the cascade axiom) axiom-free at depth `cfi_depth_bound h`. | — |
| `theorem_1_HOR_cfi_oddDeg` | 3169-3188 | **Tier-1 CFI orbit recovery.** Theorem 1 for OddDegree CFI graphs, axiom-free: orbit partition coincides with the warm-refined colouring at depth ≤ baseSize, conditional only on `OddDegree`. | — |

**§15 — Stage 3: gadget-flip automorphisms (the `Z₂^β` generators).** *We build the generator
*existence* (the cycle-space flips), not the full `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` iso — the hard
surjectivity half is needed by no consumer. Both consumers (`LinearOracle.configSwap_of_aut`
and Tier-3a B1's `hwit`) want the same object: a CFI automorphism with controlled support,
realised by the even-subgraph (cycle-space) flip. Phases 0–1 below; Phases 2–6 (adjacency
preservation, `Fin n` lift, support/locality, `P`-preservation, consumer wiring) follow.*

| Name | Description | Notes |
|------|-------------|-------|
| `CFIBase.flipSet` | 3243-3247 | The `F`-incident neighbours of `v` (`F : Fin m → Fin m → Bool` an even subgraph), as a subset of `N(v)`. | Definition |
| `CFIBase.symmDiff_flipSet_mem_even` | 3259-3275 | **Even-subset invariant preserved.** If every `flipSet F v` is even (`F` an even subgraph), `S ∆ flipSet F v` stays an even subset of `N(v)`. | — |
| `CFIBase.cfiFlip` | 3324-3334 | **The cycle-space gadget flip** on `CFIVertex H`: toggles endpoint parities along `F` (`e^b_{v→w} ↦ e^{b⊕F v w}_{v→w}`) and complements subsets (`a_S^v ↦ a_{S ∆ flipSet F v}^v`). | Definition |
| `CFIBase.cfiFlipEquiv` | 3346-3350 | The gadget flip as an `Equiv.Perm CFIVertex` (self-inverse). | Definition |
| `xor_eq_xor_iff` / `xor_ne_xor_iff` | Xor right-cancellation on `Bool` (`(a⊕c) = (b⊕c) ↔ a = b`, and the `≠` form). | private |
| `CFIBase.decide_mem_symmDiff_flipSet` | 3354-3361 | **Phase 2 bridge.** For `w ∈ N(v)`, `w ∈ S ∆ flipSet F v ↔ (w∈S) ⊕ F v w` — endpoint parity and subset membership flip together. | — |
| `CFIBase.cfiFlip_isAut` | 3363-3394 | **Phase 2 (the automorphism core).** For `F` an even subgraph that is symmetric (`F v w = F w v`), `cfiFlip F` preserves `cfiAdj` on every pair. Subset–endpoint: the `(w∈S)⊕b` invariant survives the joint flip; endpoint–endpoint bridge: the single edge `{v,w}` has one `F`-bit (symmetry), so `b₁=b₂` survives. | — |
| `IsCFI'.cfiFlipAut` | 3720-3724 | **Phase 3.** The gadget flip transported to `adj`'s vertices `Fin n` via the CFI labelling `h.e`: `g = e⁻¹ ∘ cfiFlip F ∘ e`. | Definition |
| `IsCFI'.e_cfiFlipAut` | 3726-3734 | Transport identity `e (g v) = cfiFlip F (e v)` — `e` intertwines the `Fin n` and `CFIVertex` flips. | — |
| `IsCFI'.isAut_cfiFlipAut` | 3736-3746 | **Phase-3 deliverable.** For `F` an even symmetric subgraph, `cfiFlipAut F ∈ Aut(adj)` — an honest `IsAut … adj` (via `matching` + `cfiFlip_isAut`) the consumers (`configSwap_of_aut`, Tier-3a `hwit`) use. | — |
| `IsCFI'.cfiFlipAut_involutive` | 3748-3755 | The lifted flip is an involution (needed where the decision pair must be *swapped*, `g a = b ∧ g b = a`). | — |
| `CFIBase.gadget` | 3402-3405 | **Phase 4.** The base vertex (gadget) of a CFI vertex. | Definition |
| `CFIBase.cfiFlip_eq_self_of_flipSet_empty` | 3407-3427 | **Locality.** If `F` has no edge at `x`'s gadget (`flipSet F (gadget x) = ∅`), the flip fixes `x` (`S ∆ ∅ = S`; empty flip set ⟹ `F v w = false` ⟹ parity unchanged). | — |
| `IsCFI'.cfiFlipAut_eq_self_of_flipSet_empty` | 3757-3765 | Locality lifted to `Fin n`: `F` avoiding `i`'s gadget ⟹ `cfiFlipAut F` fixes `i`. | — |
| `IsCFI'.disjoint_support_cfiFlipAut` | 3767-3777 | **Phase-4 deliverable.** If every vertex of a committed set `T` lives in an `F`-free gadget, then `Disjoint T (cfiFlipAut F).support` — the exact `Disjoint (committed set) π.support` the path-fixing consumers (`hwit`, `configSwap`) require. | — |
| `CFIBase.cfiFlip_endpoint` / `_swap` | **C1b.0 recon.** The flip toggles `e^b_{v→w}`'s parity by `F v w`; so it swaps the parity-pair `e^0/e^1` iff `{v,w} ∈ F` — the primary flippable decision pair. | simp / — |
| `CFIBase.cfiFlip_subset` | 3454-3460 | The flip symmetric-differences `a_S^v` by `flipSet F v` — swaps the subset-pair iff the gadget is `F`-touched (the second flippable kind). | — |
| `IsCFI'.cfiFlipAut_endpointVertex` / `_swaps_endpointVertex` | **C1b.0 (lifted).** The `Fin n` swap fact: `cfiFlipAut F` swaps `endpointVertex hw false ↔ true` iff `F v w = true` — the foundational swap C1b.1 keys on. | — |
| `triFlip_swaps_edge_01` | 3901-3909 | C1b.0 prototype validation: the triangle flip swaps the parity-pair on edge `{0,1}` (`decide`, independent confirmation). | — |
| `CFIBase.isEdgeOf` / `triEdge` | **C1b.2a.** The triangle even-subgraph through edge `{v,w}` with apex `u` — the minimal even subgraph through an edge. | Definition |
| `CFIBase.triEdge_eq_true` / `_iff` / `_symm` / `_cyclic` / `_apex` | Characterisation (membership, source-grouped), symmetry, cyclic invariance `{v,w,u}={w,u,v}`, and `F v w = true`. | — |
| `CFIBase.flipSet_triEdge` / `_other` | The triangle's flip set is `{w,u}` at base vertex `v` (degree 2), and `∅` off `{v,w,u}` (the avoidance → D-locality). | — |
| `CFIBase.exists_even_triangle` | 3591-3603 | **C1b.2a deliverable.** If the decision edge has a common neighbour `u` (distinct, in `N(v)∩N(w)`), an even symmetric `F` through `{v,w}` exists with support `{v,w,u}` (avoids everything else) — the concrete cycle `F` cascade-1b needs, for triangle-containing bases. General triangle-free bases (K₃,₃, Petersen) need C1b.2b. | — |
| `CFIBase.evenPermEdge` | 3613-3616 | **C1b.2b.** The even-subgraph indicator of a permutation-cycle `σ` (the cycle's "next-vertex" map). A vertex's F-neighbours are `{σ p, σ⁻¹ p}` — degree 2, no list arithmetic. | Definition |
| `CFIBase.evenPermEdge_eq_true` / `_symm` / `_iff_of_mem` | Membership characterisation, symmetry, and the moved-vertex F-neighbours `= {σ p, σ⁻¹ p}`. | — |
| `CFIBase.flipSet_evenPermEdge_of_mem` / `_of_fixed` | Flip set `= {σ p, σ⁻¹ p}` at a moved vertex (degree 2), `∅` at a fixed point (avoidance). | — |
| `CFIBase.exists_even_cycle` | 3691-3705 | **C1b.2b deliverable.** A permutation-cycle `σ` through `{v,w}` (`σ v = w`) with H-edges (`hEdge`) and orbits ≥ 3 (`hNo2`) yields an even symmetric `F` through `{v,w}` avoiding every `σ`-fixed vertex. Subsumes the triangle; covers triangle-free bases. The cycle's *existence* in `H − Σ` is the isolated graph hypothesis (where treewidth enters). | — |
| `IsCFI'.cfiFlipAut_preserves_P` | 3788-3797 | **Phase 5.** The gadget flip preserves any `P` that *every* `adj`-automorphism preserves (the descent's profile/trivial `P`) — transported through `isAut_cfiFlipAut`. Honest scope: a component-moving flip preserves exactly the automorphism-invariant `P`'s. | — |
| `IsCFI'.cfiFlipAut_pathFixing_witness` | 3799-3815 | **Phase-5 deliverable (Tier-3a B1 `hwit` shape).** Assembles Phases 3–5 + `g v = w` into `∃ π, IsAut π adj ∧ (∀ x u, P (π x)(π u) = P x u) ∧ Disjoint T π.support ∧ π v = w` — exactly what `Cascade.cascadeComposition_pathFixing`'s `hwit` consumes. | — |
| `triFlipEdges` / `triFlip_even` | **Phase-0 prototype:** `triangleBase`'s unique nontrivial even subgraph (all 3 edges; β=1) and its even-flip-set fact. | Definition / — |
| `triFlip_involutive_check` | 3878-3883 | Phase-0 smoke test: triangle gadget flip is an involution (`decide`, kernel, axiom-clean). | — |
| `triFlip_isAut_check` | 3885-3892 | **Phase-0 crux:** the triangle gadget flip preserves `cfiAdj` on all 18×18 pairs (`decide`) — validates cycle-flip-is-automorphism on the smallest case before the general Phase-2 proof. | — |
| `triFlip_nontrivial` | 3894-3899 | Phase-0 smoke test: the triangle gadget flip moves some vertex — a nontrivial `CFI(triangle)` automorphism. | — |

| `CFIBase.mem_flipSet` | 3254-3257 | Membership in the flip set: `w ∈ flipSet F v ↔ w ∈ N(v) ∧ F v w`. | `@[simp]` |
| `CFIBase.xorF` | 3285-3287 | **(CFI-cov.2)** Pointwise XOR of two flip-edge indicators — the cycle-space `Z₂` sum. | Definition |
| `CFIBase.flipSet_xorF` | 3289-3297 | **(CFI-cov.2)** The flip-set of an XOR is the symmetric difference of the flip-sets: `flipSet (xorF F F') v = flipSet F v ∆ flipSet F' v`. The reusable core of the cycle-space sum. | — |
| `CFIBase.even_xorF` | 3299-3306 | **(CFI-cov.2)** Even flip-subgraphs stay even under `xorF` (symmetric-difference preserves even cardinality, via `card_symmDiff_mod_two`). | — |
| `CFIBase.CycleSpace` | 3308-3311 | **(CFI-cov.2) The cycle space `Z₂^β`**: symmetric, even flip-subgraphs `F` — the index set of the gauge flips `cfiFlip F` (the `Z₂^β` factor of `Aut(CFI(H))`). | Definition |
| `CFIBase.cycleSpace_xorF` | 3313-3316 | **(CFI-cov.2)** The cycle space is closed under the `Z₂` sum `xorF` (symmetric + even both preserved). | — |
| `CFIBase.cycleSpace_const_false` | 3318-3322 | **(CFI-cov.2)** The empty flip-subgraph (zero) lies in the cycle space. | — |
| `CFIBase.cfiFlip_endpoint_swap` | 3443-3452 | **C1b.0.** The flip swaps the parity-pair `e^0_{v→w}/e^1_{v→w}` iff `F v w = true` (the swap companion of `cfiFlip_endpoint`). | — |
| `CFIBase.cfiFlip_xorF` | 3470-3485 | **(CFI-cov.3) Gauge flip is a homomorphism on the cycle space:** `cfiFlip (xorF F F') = cfiFlip F ∘ cfiFlip F'` (endpoint: Bool-xor assoc/comm; subset: symmDiff assoc/comm via `flipSet_xorF`). The `Z₂^β`-factor group structure. | — |
| `CFIBase.cfiFlip_const_false` | 3487-3498 | **(CFI-cov.3)** The zero subgraph is the identity flip: `cfiFlip (fun _ _ => false) = id` (cycle-space zero ↦ identity). | — |
| `CFIBase.flipSet_triEdge_other` | 3560-3570 | **D-locality.** Off the triangle `{v,w,u}` the triangle's flip set is empty, so the triangle flip fixes every other gadget. | — |
| `CFIBase.flipSet_evenPermEdge_of_fixed` | 3656-3665 | **D-locality (triangle-free bases).** At a `σ`-fixed vertex the permutation-cycle flip set is empty, so the cycle flip avoids every fixed gadget. | — |
| `IsCFI'.cfiFlipAut_swaps_endpointVertex` | 3829-3841 | **C1b.0 (lifted to `Fin n`).** `cfiFlipAut F` swaps `endpointVertex hw false ↔ true` iff `F v w = true` — the foundational decision-pair swap C1b.1 keys on. | — |
| `IsCFI'.cfiFlipAut_xorF` | 3845-3853 | **(CFI-cov.3) The lifted gauge-flip homomorphism:** `cfiFlipAut (xorF F F') = cfiFlipAut F * cfiFlipAut F'` (the `Fin n` form of `cfiFlip_xorF` via `e_cfiFlipAut`). So `F ↦ cfiFlipAut F` is a group homomorphism `(Z₂^β, xorF) → Equiv.Perm (Fin n)`, image the gauge group. | — |
| `IsCFI'.cfiFlipAut_one` | 3855-3861 | **(CFI-cov.3)** The zero gauge flip is the identity: `cfiFlipAut (fun _ _ => false) = 1` — the homomorphism preserves the unit. | — |
## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme` | 47-91 | A symmetric association scheme on `Fin n`: a partition of `Fin n × Fin n` into `rank + 1` symmetric relations `R_0, …, R_rank` (`R_0` the diagonal) with well-defined intersection numbers `p^k_{ij}`. | Structure |
| `relOfPair` | 107-109 | §1.1 The unique relation index `i : Fin (S.rank + 1)` for which `rel i v w = true`. | Definition, `noncomputable` |
| `rel_relOfPair` | 111-114 | The pair `(v, w)` lies in `R_{relOfPair v w}`. | — |
| `relOfPair_unique` | 116-119 | Uniqueness: any relation containing `(v, w)` is `relOfPair v w`. | — |
| `rel_iff_relOfPair` | 121-124 | Characterisation: `rel i v w = true ↔ i = relOfPair v w`. | — |
| `relOfPair_symm` | 126-131 | `relOfPair v w = relOfPair w v`. | — |
| `relOfPair_eq_zero_iff` | 139-147 | Diagonal characterisation: `relOfPair v w = 0 ↔ v = w`. | — |
| `AssociationScheme.ClosedSubset` | 161-166 | **(EOL scheme leg) Closed relation subset = block system.** `I` contains the diagonal `R_0` and is closed under the complex product (`R_i,R_j ∈ I` and `intersectionNumber i j k ≠ 0` ⟹ `R_k ∈ I`). The association-scheme form of a block system / sub-equivalence; on a schurian scheme graph it is a union of scheme relations, hence refinement-visible. | Definition |
| `AssociationScheme.schemeEquiv` | 168-171 | **(EOL scheme leg) The equivalence induced by a relation subset:** `v ~ w` iff `relOfPair v w ∈ I`. Under `ClosedSubset` it is a genuine equivalence (the block system). | Definition |
| `AssociationScheme.schemeEquiv_trans` | 181-198 | **Transitivity from closure under the complex product.** `w` witnesses `intersectionNumber (relOfPair v w)(relOfPair w x)(relOfPair v x) ≠ 0`, so the `ClosedSubset` closure clause forces `relOfPair v x ∈ I`. Where the scheme's intersection numbers do the work a raw partition could not. | — |
| `AssociationScheme.closedSubset_univ` | 205-207 | The whole relation set is always closed (the trivial "one block" system). | — |
| `AssociationScheme.IsPrimitive` | 209-214 | **(EOL scheme leg) Scheme primitivity:** the only closed subsets are the diagonal `{R_0}` and the whole relation set — no non-trivial block system. The Cameron-free, scheme-theoretic primitivity for the Exhaustive-Obstruction Lemma's leg C on coherent-configuration residuals. | Definition |
| `AssociationScheme.exists_nontrivial_closedSubset_of_not_isPrimitive` | 216-225 | **(Imprimitive ⟹ non-trivial block system)** Unfolding `¬IsPrimitive`: there is a closed subset `I` neither `{R_0}` nor `univ` — a genuine non-trivial block system. The entry point letting the Route B imprimitive discharge construct its partition `β` (the `schemeEquiv I` block-class) from the descent's combinatorial `¬IsPrimitive` observation. Via `push Not`. | — |
| `AssociationScheme.schemeEquiv_class_eq_iff` | 227-245 | **(Block-class equality characterization)** `{y | schemeEquiv I u y} = {y | schemeEquiv I w y} ↔ schemeEquiv I u w` for a closed subset `I` — the `schemeEquiv I`-classes are the blocks, equal iff their basepoints are related. The honest characterization of the Route B partition `β v := {y | schemeEquiv I v y}`, needed wherever `β u = β w` must be related back to the scheme (e.g. a future non-recovering `hfiber`). Standard equivalence-class machinery on `schemeEquiv_equivalence`. | — |
| `AssociationScheme.exists_composable_of_intersectionNumber` | 247-265 | **(Phase 2, M1.1c — general)** A nonzero intersection number is realized by a composable triple: `R_k` nonempty ∧ `intersectionNumber i j k ≠ 0 ⟹ ∃ x y z, (x,y) ∈ R_i ∧ (y,z) ∈ R_j ∧ (x,z) ∈ R_k`. The general ingredient the `ClosedSubset`-closure clause needs (reusable for the §5.3 general crux: "the difference of a composite relation is the sum of the parts'"). `R_k`-nonemptiness explicit (the axioms do not force every index inhabited). | — |
| `IsSchemeAut` | 287-292 | §2 Scheme automorphism: a permutation of `Fin n` preserving every relation index of `S`. | Definition |
| `IsSchemeAut.refl` | 298-299 | The identity is a scheme automorphism. | — |
| `IsSchemeAut.trans` | 301-307 | Scheme automorphisms compose. | — |
| `IsSchemeAut.symm` | 309-315 | The inverse of a scheme automorphism is a scheme automorphism. | — |
| `relOfPair_eq` | 317-326 | Scheme automorphisms preserve `relOfPair`: `relOfPair (π v) (π w) = relOfPair v w`. | — |
| `SchurianScheme` | 330-341 | An `AssociationScheme` whose relations are exactly the diagonal orbits of `IsSchemeAut`: any two pairs in a relation are connected by some scheme automorphism. | Structure |
| `trivialScheme` | 353-369 | §3 The trivial scheme on `Fin 1` (rank 0, single relation `R_0`); smoke test confirming `AssociationScheme` is inhabited. | Definition |
| `trivialSchurianScheme` | 371-379 | §3 The trivial `Fin 1` scheme is schurian (only the identity is needed). | Definition |
| `Orbital` | 395-401 | §3.1 (Phase 2, M0) The **orbitals** of `G ≤ Perm (Fin n)`: orbits of the diagonal action on `Fin n × Fin n` — the relations of the orbital scheme. | `abbrev` |
| `orbMk` | 403-404 | (Phase 2, M0) The orbital containing the pair `(v, w)`. | Definition |
| `orbMk_eq_iff` | 406-416 | (Phase 2, M0) **Orbital-equality bridge**: `orbMk v w = orbMk v' w'` iff some `g ∈ G` carries `(v',w')` to `(v,w)`. | — |
| `orbMk_smul` | 418-421 | (Phase 2, M0) A group element `g ∈ G` fixes every orbital (`orbMk (g v)(g w) = orbMk v w`). | — |
| `orbMk_diag_iff` | 423-435 | (Phase 2, M0) Under transitivity, `orbMk v w` is the diagonal orbital iff `v = w`. | — |
| `orbitalRank` | 437-438 | (Phase 2, M0) The rank of the orbital scheme: one less than the number of orbitals. | Definition, `noncomputable` |
| `orbitalRank_succ` | 440-444 | (Phase 2, M0) `orbitalRank G + 1 = #orbitals` (the orbital quotient is nonempty). | — |
| `orbitalIdx` | 446-453 | (Phase 2, M0) The orbital indexing `Fin (rank+1) ≃ orbitals`, arranged so index `0` is the diagonal orbital. | Definition, `noncomputable` |
| `orbitalIdx_zero` | 455-458 | (Phase 2, M0) `orbitalIdx G 0` is the diagonal orbital. | — |
| `orbMk_out` | 460-465 | (Phase 2, M0) `Quotient.out` recovers a representative pair of any orbital. | — |
| `orbitalAssocScheme` | 473-528 | **(Phase 2, M0.1 — the model)** The **orbital association scheme** of a generously-transitive `G ≤ Perm (Fin n)`: relations = the orbitals, `relOfPair v w` = orbital of `(v,w)`. Intersection-number axiom via the bijection `u ↦ g·u` (`Finset.card_bij'`) — `G` acts transitively on each orbital so the witness count is constant. Stays native to `Fin n` (no `V ≃ Fin(p^d)` transport). The reusable Phase-2 model; the affine `V⋊G₀` instance specializes it. Axiom-clean. | Definition, `noncomputable` |
| `orbitalScheme` | 530-548 | **(Phase 2, M0.2 — schurian)** The orbital scheme is **schurian**: two pairs in the same orbital are `G`-related (the witness `g ∈ G` is a `IsSchemeAut`). Produces a `SchurianScheme n`, pluggable into `SelfDetectsStably`/the seal. Axiom-clean. | Definition, `noncomputable` |
| `vProfile` | 569-578 | T2.2 The v-profile colouring `w ↦ (relOfPair v w).val`: a vertex invariant relative to a fixed individualized `v`. | Definition, `noncomputable` |
| `SchemeOrbitPartition` | 631-635 | §4.1 The v-stabilized scheme-Aut orbit relation: some scheme automorphism with `π v = v` sends `w` to `u`. | Definition |
| `SchemeOrbitPartition.refl` | 641-643 | Reflexivity of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.symm` | 645-653 | Symmetry of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.trans` | 655-665 | Transitivity of `SchemeOrbitPartition`. | — |
| `schemeEquiv_isSchemeAut` | 720-727 | **(EOL scheme leg, bridge) The block system is scheme-automorphism-invariant:** `schemeEquiv I (π v)(π w) ↔ schemeEquiv I v w` for a scheme automorphism `π`. The closed subset's partition is preserved by the symmetry — a genuine system of imprimitivity. From `IsSchemeAut.relOfPair_eq`. | — |
| `schemeEquiv_schemeOrbit` | 729-742 | **(EOL scheme leg, bridge) The block of `v` is a union of v-stabilized scheme-Aut orbits** (block system coarser than the orbit partition): same `v`-orbit ⟹ same `schemeEquiv I` block. With orbit recovery (v-orbits = `warmRefine` cells) this makes the block refinement-visible — scheme-imprimitivity ⟹ cascade. | — |
| `vProfile_eq_imp_schemeOrbit` | 748-761 | S1.b — under the schurian axiom, equal `vProfile` implies a v-fixing scheme automorphism connecting the two vertices. | — |
| `vProfile_iff_schemeOrbit` | 763-772 | Step 1 of Theorem 2 (combined): for a schurian scheme, profile equality at `v` is exactly v-stabilized scheme-Aut orbit equivalence. | — |
| `JointSchemeOrbit` | 798-801 | The `Stab(T)`-orbit relation: a scheme automorphism fixing every base point in `T` and sending `w ↦ u`. Base-set generalization of `SchemeOrbitPartition` (the `T = {v}` case). The rank-4 / `s(C)` analysis object. | Definition |
| `jointProfile_eq_of_jointSchemeOrbit` | 803-814 | **(Reverse bridge — provable, any `T`.)** A `T`-fixing automorphism `w ↦ u` forces `relOfPair t w = relOfPair t u` for all `t ∈ T` — i.e. `Stab(T)`-orbits **refine** the joint profile. The half that always holds; via `IsSchemeAut.relOfPair_eq`. Axiom-clean. | — |
| `JointProfileRecoversAt` | 816-821 | **(Forward bridge — the recovery-at-`T` proposition; OPEN for `|T| ≥ 2`.)** Joint-profile agreement over `T` ⟹ a single `T`-fixing automorphism `w ↦ u` (the structural form of "cells = `Stab(T)`-orbits"). Free at `|T| = 1`; open at `|T| ≥ 2` = the `s(C) ≥ 2` content, smallest at rank-4 (amorphic). The joint profile only sees `⋂ₜ Stab(t)`-orbits, generally coarser than the `Stab(T)`-orbit. | Definition |
| `jointProfileRecoversAt_singleton` | 823-833 | **(The `|T| = 1` base case is free.)** Single-base recovery: `JointProfileRecoversAt S {v}`, from the landed schurian forward `vProfile_eq_imp_schemeOrbit`. The first base where the forward can fail is `|T| ≥ 2` (the open rank-4 / `s(C)` crux). Axiom-clean. | — |
| `SchemeGraph` | 850-859 | §5 A graph derived from a scheme by marking a set `J ⊆ Fin (rank + 1)` of relations as edges (`0 ∉ J`, so loopless). | Structure |
| `adj` | 865-868 | The derived adjacency matrix: `(v, w)` is an edge iff `relOfPair v w ∈ J`. | Definition, `noncomputable` |
| `adj_symm` | 887-891 | Symmetric: `adj v w = adj w v`. | — |
| `SchurianSchemeGraph` | 922-936 | §6 A `SchemeGraph` schurian w.r.t. graph automorphisms: `schurian_transitive` (orbits ⊇ relations) and `isAut_imp_isSchemeAut` (orbits ⊆ relations). | Structure |
| `GraphOrbitFixing` | 971-975 | §7 The v-stabilized graph-Aut orbit relation: some `π ∈ Aut(adj)` with `π v = v` and `π w = u`. | Definition |
| `GraphOrbitFixing.refl` | 981-982 | Reflexivity of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.symm` | 984-991 | Symmetry of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.trans` | 993-1000 | Transitivity of `GraphOrbitFixing`. | — |
| `SchurianSchemeGraph.schemeEquiv_graphOrbit` | 1039-1048 | **(EOL scheme leg, bridge) The block of `v` is a union of graph-Aut orbits.** Graph version of `schemeEquiv_schemeOrbit`: a graph automorphism fixing `v` (`GraphOrbitFixing`) preserves the `schemeEquiv I` block, since on a schurian scheme graph every graph aut is a scheme aut (`isAut_imp_isSchemeAut`). Block system coarser than the v-stabilized graph-orbit partition — ready to compose with recovery. | — |
| `refineStep_round1_pair_eq` | 1105-1153 | §8.a S2.a round-1 lemma: under `χ_v`, equal colour after one `refineStep` for non-`v` `w, u` forces `(adj w v, P w v) = (adj u v, P u v)`. | — |
| `refineStep_round1_adj_eq` | 1155-1163 | S2.a (adj-only): round-1 equality forces `adj w v = adj u v`. | — |
| `iterSignature` | 1216-1224 | §8.b The signature multiset of `w` computed against the `iter[k]` refinement of `χ_v`. | Definition |
| `iter_succ_eq_iff` | 1226-1237 | Round-by-round unfolding: `iter[k+1]` equality decomposes into `iter[k]` equality plus matching iter-k signatures. | — |
| `AssociationScheme.intersectionCount_via_w` | 1239-1265 | Scheme axiom in usable form: the count of `u'` with `(v,u') ∈ R_i` and `(w,u') ∈ R_l` equals `intersectionNumber i l (relOfPair v w)` — depends only on `vProfile w`. | — |
| `Step2_target` | 1290-1306 | §8.c Step 2 statement (target): for a `SchurianSchemeGraph` and compatible `P`, `warmRefine` cells refine `vProfile` classes. | Definition |
| `signature_count_eq_card` | 1322-1333 | §8.b.2 Bridge lemma: `Multiset.count t (signature adj P χ w)` equals the cardinality of the matching `u' ≠ w` preimage filter. | — |
| `signature_eq_card_eq` | 1335-1348 | Count equality from signature equality: equal signatures give equal preimage-filter cardinalities for every tuple `t`. | — |
| `signature_eq_countP_eq` | 1380-1390 | Aggregate `countP` equality from signature equality, for any decidable predicate `p`. | — |
| `toSchemeProfile` | 1528-1561 | **T2.M4 assembly.** The `SchemeProfile` constructor: from a `SchurianSchemeGraph`, a P-invariance hypothesis, and a `Step2_target` witness, build the abstract `SchemeProfile G.adj P v`. | Definition, `noncomputable` |
| `trivialPMatrix` | 1584-1585 | §9.1 The trivial `PMatrix`: every entry is `POE.unknown`. | Definition |
| `SchurianSchemeGraph.toSchemeProfile_trivialP` | 1593-1600 | Specialisation of `toSchemeProfile` to trivial P: P-invariance is automatic, leaving only `Step2_target`. | Definition, `noncomputable` |
| `IsSchurianSchemeGraph'` | 1619-1625 | §9.2 Concrete schurian-scheme-graph predicate: `adj` arises as the derived adjacency of some `SchurianSchemeGraph`. | Structure |
| `theorem_2_HOR_concrete` | 1627-1654 | **Theorem 2 (HOR for schurian scheme graphs), concrete form.** From `IsSchurianSchemeGraph' adj` plus P-invariance plus a `Step2_target` witness, derive the `OrbitPartition ↔ warmRefine` equivalence. | — |
| `trivialSchurianSchemeGraph` | 1683-1695 | §9.3 The trivial 1-vertex schurian scheme graph (empty edge set, identity automorphism only). | Definition |
| `theorem_2_HOR_trivial` | 1705-1723 | **First fully discharged Theorem 2 instance.** For the trivial 1-vertex scheme with trivial P, the `OrbitPartition ↔ warmRefine` equivalence holds unconditionally. | — |
| `theorem_2_HOR_concrete_rank_le_one` | 1778-1790 | **Theorem 2 unconditional for rank ≤ 1 schurian scheme graphs** (e.g. K_n). | — |
| `Step2_at_depth` | 1807-1816 | §10 Depth-parametrised Step 2: iter[k] equality implies `vProfile` equality; a depth-explicit version of `Step2_target`. | Definition |
| `schemePart_at` | 1895-1919 | §10.1 Recursive partition predicate at depth `k`: depth 0 is `χ_v`-equality; depth `k+1` adds matching (adj, P, depth-`k` class) counts over neighbours. | Definition |
| `iter_refines_schemePart_at` | 1979-2066 | §10.3 **Inductive refinement.** The `iter[k] χ_v` partition refines `schemePart_at G P v k`; the substantive intersection-number induction step of Step 2. | — |
| `schemePartFrom` | 2080-2092 | §10.3b **(two-vantage realization)** The depth-`k` counting partition from an **arbitrary** initial colouring `χ₀` — `schemePart_at` generalized off the single-base `individualizedColouring n {v}` to any base (the base is used only at depth 0). The descent's multi-vantage recovery is the `χ₀ = individualizedColouring n S` instance; pure 1-WL, no scheme structure. | Definition |
| `iterFrom_refines_schemePartFrom` | 2123-2196 | §10.3b **(two-vantage realization, general base)** For any initial colouring `χ₀`, `iter[k] χ₀` refines `schemePartFrom adj P χ₀ k`: equal warm-refined colour ⟹ the depth-`k` multi-base counts agree. Generalizes `iter_refines_schemePart_at` to an arbitrary base (inductive step verbatim, base used only at depth 0). The **realization half** of the two-vantage step (seal-handoff §"G2 attack board"): a multi-base counting separation is *seen* by warm refinement; the open converse (primitive ⟹ gap broken at base+O(1)) is the crux. | — |
| `iterSet_refines_schemePartFrom` | 2198-2207 | §10.3b **(two-vantage realization, descent form)** The `χ₀ = individualizedColouring n S` instance: individualizing a base **set** `S` and warm-refining sees the multi-base counting partition. The `S = {e, e'}` case is the two-vantage step's realization half — a distinguishing two-base count is realized as a warm-refinement split. | — |
| `Step2_converges_at` | 2225-2232 | §10.4 Step 2 convergence at depth `k`: `schemePart_at`-k equivalence implies `vProfile` equality. | Definition |
| `schemePart_at_one_to_v` | 2276-2326 | §10.5 **Depth-1 extraction.** For `w, u ≠ v`, `schemePart_at G P v 1 w u` forces `adj w v = adj u v ∧ P w v = P u v`. | — |
| `RelOfPairDetByAdjP` | 2355-2363 | §10.6 **Depth-1 separation hypothesis**: `(adj v ·, P v ·)` determines `relOfPair v ·` on non-`v` vertices. | Definition |
| `step2_converges_at_one_of_det` | 2365-2392 | **Step 2 convergence at depth 1 under depth-1 separation.** | — |
| `theorem_2_HOR_concrete_of_det` | 2437-2447 | **Theorem 2 unconditional under depth-1 separation** (Petersen-class). | — |
| `AdjSeparatesRelations` | 2470-2474 | §10.8 Cleaner reformulation of depth-1 separation: `(· ∈ J)` is injective on non-diagonal relations. P-free. | Definition |
| `adjSeparates_of_rank_two_J_singleton` | 2507-2551 | **`rank = 2` + `|J| = 1` ⇒ `AdjSeparatesRelations`.** The unique element of `J` distinguishes the two non-diagonal relations. | — |
| `theorem_2_HOR_concrete_rank_two_J_singleton` | 2562-2576 | **Theorem 2 unconditional for rank-2 + `|J| = 1` schurian scheme graphs** — covers Petersen, Kneser `K(5,2)`, Johnson `J(5,2)`. Axiom-clean. | — |
| `Depth2Det` | 2604-2620 | §10.9 **Depth-2 separation predicate**: the depth-2 invariant (adj/`P`-to-`v` plus the depth-1 block-degree vector) determines `relOfPair v ·`. Weaker than `RelOfPairDetByAdjP`. | Definition |
| `step2_converges_at_two_of_det2` | 2631-2660 | **Step 2 convergence at depth 2 under depth-2 separation.** | — |
| `theorem_2_HOR_concrete_of_det2` | 2679-2691 | **Theorem 2 unconditional under depth-2 separation**; depth-2 analogue of `theorem_2_HOR_concrete_of_det`. | — |
| `IntersectionSeparates` | 2769-2778 | §10.10 **Intersection-number separation hypothesis**: `intersectionNumber j0 j0 ·` distinguishes the non-edge, non-diagonal relations (those adjacency cannot). | Definition |
| `depth2Det_of_intersectionSeparates` | 2780-2904 | **Discharges `Depth2Det`** for single-edge (`J = {j0}`) schurian scheme graphs with an edge-neighbour of `v` and intersection-number separation. | — |
| `theorem_2_HOR_concrete_intersectionSeparates` | 2906-2926 | **Theorem 2 unconditional for single-edge schurian scheme graphs with intersection-number separation** — first genuinely rank-≥-3 coverage (e.g. the 7-cycle). Strictly subsumes the rank-2/`|J|=1` case. Axiom-clean. | — |
| `RelIsolatedAt` | 2954-2961 | §10.11 **Relation-isolation predicate**: relation `l`'s `schemePart_at k` class is exactly `R_l` from `v`. The bootstrap's central object. | Definition |
| `isolatedCount_eq` | 3004-3060 | **The reusable counting heart**: a depth-`k`-isolated `l` lets `schemePart_at (k+1)` pin the intersection number `p^{·}_{l,j0}` (block-degree into `R_l`, summed over `P`). | — |
| `relIsolatedAt_one_j0` | 3062-3098 | **Base case**: the edge relation `j0` is isolated at depth 1. | — |
| `relIsolatedAt_succ` | 3133-3181 | **The bootstrap step**: a finset `Iso` of depth-`k`-isolated relations plus a separation pinning `i` by `(adjacency, counts into Iso)` ⟹ `i` is isolated at depth `k+1`. | — |
| `convergence_of_all_isolated` | 3183-3192 | All relations isolated at depth `k` ⟹ `Step2_converges_at G P v k` (`schemePart_at k` = `vProfile` partition). | — |
| `theorem_2_HOR_concrete_of_isolation` | 3194-3213 | **Theorem 2 from an isolation chain** — the general engine. Exhibiting that every relation isolates by depth `k ≤ n` gives Theorem 2 unconditionally. Axiom-clean. | — |
| `theorem_2_HOR_concrete_intersectionSeparates3` | 3215-3282 | **Theorem 2 for depth-3 single-anchor schemes** (e.g. the 9-cycle) — reaches rank-≥-4 schemes the depth-2 result cannot. Axiom-clean. | — |

| `occursFromV` | 3302-3308 | §10.12 — The relations that actually occur from `v` (non-empty blocks `R_l`); the honest carrier for the isolation closure, keeping its saturation depth `≤ n`. | Definition, `noncomputable` |
| `IsoPinned` | 3324-3332 | §10.12 — `i` is uniquely pinned by `Iso`: the only non-diagonal relation with its `(edge-membership, intersection-counts into Iso)` signature, exactly the `hsep` hypothesis of `relIsolatedAt_succ`. | Definition |
| `isolationStep` | 3334-3340 | §10.12 — One round of the isolation closure: keep `Iso` and add every relation occurring from `v` that is pinned by `Iso`. The extensive operator driving the saturation engine. | Definition, `noncomputable` |
| `relIsolatedAt_of_not_occurs` | 3367-3373 | Relations that never occur from `v` are vacuously isolated at any depth. | — |
| `stage_relIsolatedAt` | 3375-3412 | **Stage lemma (closure ⇒ isolation engine).** Every relation in the `m`-th closure round `isolationStep^[m] {0, j0}` is isolated at depth `m + 1`, turning the saturated closure into full isolation. | — |
| `EdgeGenerates` | 3414-3421 | §10.12 — The one structural hypothesis replacing the rank ladder: the isolation closure of `{R₀, R_{j0}}` reaches every relation occurring from `v`. The scheme-graph realisation of the seal's **D1**. | Definition |
| `theorem_2_HOR_of_edgeGenerates` | 3423-3474 | **General convergence — Theorem 2 from `EdgeGenerates`.** Covers every single-edge schurian scheme graph whose edge relation generates the scheme, with no per-rank separation data: the saturation engine plus stage lemma yield orbit recovery at depth `≤ n`. | — |
| `PPolynomial` | 3510-3535 | §10.13 — A P-polynomial (metric / distance-regular) schurian scheme w.r.t. edge `j0`: relations form a distance ladder `R 0,…,R rank` with a tridiagonal intersection array and nonzero subdiagonal. The abstract form of "distance-regular". | Structure |
| `pPolynomial_pinned` | 3537-3569 | The metric pinning lemma: in a P-polynomial scheme, distance `R k` (`k ≥ 2`) is uniquely pinned among non-diagonal relations by its counts into the strictly-closer distances `{R 0,…,R (k−1)}`. | — |
| `edgeGenerates_of_pPolynomial` | 3571-3623 | **EdgeGenerates for every P-polynomial scheme.** The distance ladder walks out the isolation closure (each `R k` lands once all closer distances do), so the closure contains every relation. | — |
| `theorem_2_HOR_of_pPolynomial` | 3625-3646 | **General convergence for the metric class — Theorem 2 for every P-polynomial schurian scheme graph.** One theorem covering the entire distance-regular family (cycles, Johnson, Hamming, all DRGs) with no per-scheme separation data; the P-polynomial structure discharges `EdgeGenerates`, which the engine turns into orbit recovery. | — |
| `schemeEquiv_warmRefine_of_pPolynomial` | 3648-3671 | **(EOL scheme leg — bridge CLOSED) The block of `v` is refinement-visible.** On a P-polynomial schurian scheme graph, same `warmRefine` cell (after individualizing `v`) ⟹ same `schemeEquiv I` block. Composes recovery (`theorem_2_HOR_of_pPolynomial`: cell ⟹ `OrbitPartition adj P {v}`) with `schemeEquiv_graphOrbit` (drop the P-clause via `h.matching`). So a `ClosedSubset`'s block is a **union of `warmRefine` cells** — scheme-imprimitivity ⟹ refinement-visible split, the ingredient for "non-cascade ⟹ primitive". | — |
| `AssociationScheme.SchemeAutGroup` | 3696-3710 | §11 — The **scheme automorphism group** as a `Subgroup` of `Equiv.Perm (Fin n)` (carrier `IsSchemeAut`); mirrors `AutGroup`. The group object whose `MulAction` blocks/primitivity ground the EOL scheme leg. | Definition |
| `AssociationScheme.mem_schemeAutGroup` | 3712-3713 | Membership: `π ∈ SchemeAutGroup S ↔ IsSchemeAut S π`. | `@[simp]` |
| `AssociationScheme.schemeAutGroup_smul` | 3715-3716 | The subgroup action's `smul` is application of the underlying permutation: `g • v = (↑g) v`. | `@[simp]` |
| `AssociationScheme.isBlock_schemeEquiv` | 3735-3755 | **A closed subset's `schemeEquiv I`-class is a Mathlib `IsBlock`** for the scheme-Aut action: translates are classes, and distinct classes (`schemeEquiv_equivalence`) are disjoint. The combinatorial→group block bridge. | — |
| `schemeAutGroup_isPretransitive` | 3761-3768 | **Pretransitivity is free on a schurian scheme** — the diagonal `R_0` is a single relation, so the schurian axiom at `i = 0` connects any two points by a scheme automorphism. | — |
| `exists_relOfPair_from` | 3770-3784 | **Every relation is realized from any fixed point** (schurian + every relation occurs): `∃ u, relOfPair a u = j`. The non-degeneracy companion for the primitivity correspondence. | — |
| `isPrimitive_of_isPreprimitive` | 3786-3822 | **Group-primitive ⟹ scheme-primitive** (every relation occurs): if the scheme-Aut action is `IsPreprimitive`, the only closed subsets are `{R_0}`/`univ` (a closed subset's class is a block, hence trivial, forcing the subset trivial). | — |
| `isPreprimitive_of_isPrimitive` | 3824-3908 | **Scheme-primitive ⟹ group-primitive** (the leg-C-useful direction, every relation occurs): a block `B ∋ a` is `Aut_a`-invariant ⟹ a union of `vProfile` classes ⟹ `B = schemeEquiv I_B`; the intersection numbers make `I_B` closed, so primitivity forces `B` trivial. | — |
| `isPreprimitive_iff_isPrimitive` | 3910-3931 | **(EOL scheme leg, group side) Scheme primitivity = group-action preprimitivity.** On a schurian scheme where every relation occurs, combinatorial `IsPrimitive` ⟺ Mathlib `IsPreprimitive` of `SchemeAutGroup` — the standard primitive-permutation-group notion the cited Babai/Sun–Wilmes classification is stated against. | — |
| `schemeBlock_fiber_transitive` | 3944-3957 | §11.1 **(Route B imprimitive-decomposition gate — fiber)** The stabiliser of a closed-subset block acts transitively on that block (`orbit (stabilizer (block of a)) a = block of a`), so the fiber's orbital configuration is schurian. Mathlib `IsBlock.orbit_stabilizer_eq` on `isBlock_schemeEquiv` + `schemeAutGroup_isPretransitive`. Confirms the recursion's fiber constituent stays in the schurian class (the non-schurity risk is about abstract S-ring wreaths, not group block systems). | — |
| `schemeBlocks_transitive` | 3959-3970 | §11.1 **(Route B imprimitive-decomposition gate — quotient)** The scheme-Aut group carries any closed-subset block onto any other (`smul_schemeEquiv_class` + vertex transitivity), so the action on blocks is transitive and the quotient scheme is schurian. With `schemeBlock_fiber_transitive`, discharges the Route-B schurity gate: both constituents of the imprimitive decomposition stay schurian, so the size-induction's IH applies. | — |
| `PrimitiveCCClassification` | 4010-4033 | §12 **(EOL scheme leg) The cited classification** (Babai 1981 / Sun–Wilmes 2015 on primitive coherent configurations), a named `Prop` parametrized by the largeness + Cameron-scheme predicates — carried as an explicit hypothesis, **never a fresh `axiom`**: every group-preprimitive, CC-rank-≥-3, **large** schurian scheme (every relation occurring) is a Cameron scheme. Largeness is essential (excludes the small/cascading `C₇`). | Definition |
| `exhaustiveObstruction_scheme` | 4035-4052 | §12 **(EOL scheme leg, capstone) Exhaustive-Obstruction Lemma on scheme residuals, modulo the cited classification.** A **primitive** (`IsPrimitive`), **large** (`IsLargeScheme` = non-cascade / super-poly Aut), CC-rank-≥-3 schurian scheme residual is a Cameron section. The content is the landed bridge `isPreprimitive_of_isPrimitive` turning the descent's combinatorial primitivity into the group preprimitivity `hClassify` consumes; the Cameron case still flags (classification half — Cameron-hard, **not** GI-hard). Largeness is the genuine driver (not non-abelian — plan §4 R3). | — |
| `exhaustiveObstruction_scheme_trichotomy` | 4054-4073 | §12 **(EOL scheme leg) EOL trichotomy (doc §1 disjunction form).** Given the cited classification and rank ≥ 3, every schurian scheme residual is one of: **not primitive** (cascade-recoverable), **not large** (small Aut — recoverable/abelian region), or a **Cameron scheme** — the negation-complete tiling (primitive? large?) faithfully excluding the small-but-primitive `C₇`-type schemes from the Cameron branch. | — |
| `LargenessBridge` | 4101-4109 | §12.1 **(carried largeness) The non-cascade bridge.** `∀ m S, NonCascade m S → IsLargeScheme m S` — the named input making the capstone's largeness antecedent explicit, discharged by the **identity** at `NonCascade = IsLargeScheme = IsLargeSchemeViaAut`. Carried as a hypothesis (never an `axiom`), mirroring `PrimitiveCCClassification`; the genuine '¬consumed ⟹ large' stays open (G2-B). | Definition |
| `exhaustiveObstruction_scheme_of_nonCascade` | 4111-4127 | §12.1 **(EOL scheme leg) EOL with a traceable largeness antecedent.** `exhaustiveObstruction_scheme` with the free `IsLargeScheme` hypothesis reached *through* the descent's `NonCascade` observation + the stated `LargenessBridge`, so largeness is no longer free-floating. `LargenessBridge` is the single named substrate-conditional input the no-fusion battery validates; everything else is §12 routing. Still the classification half — Cameron-hard, **not** GI-hard. | — |
| `exhaustiveObstruction_scheme_nonCascade_trichotomy` | 4129-4149 | §12.1 **(EOL scheme leg) EOL trichotomy in descent-observable terms.** Routes `exhaustiveObstruction_scheme_trichotomy` through `LargenessBridge` to restate the disjunction against the descent's own observable: every rank-≥-3 schurian scheme residual is **not primitive** (imprimitive ⟹ refinement-visible block to cascade on), **cascades** (`¬ NonCascade` — recovers at poly depth, the consumable region), or is a **Cameron scheme** (the flagged obstruction). | — |
| `exhaustiveObstruction_scheme_nonCascade_trichotomy'` | 4151-4173 | **(EOL trichotomy, primitivity-carrying)** Identical to `exhaustiveObstruction_scheme_nonCascade_trichotomy` but the cascade disjunct carries `IsPrimitive`: `¬IsPrimitive ∨ (IsPrimitive ∧ ¬NonCascade) ∨ Cameron`. Free strengthening — the cascade branch of the proof is already inside `by_cases hprim` (true). Lets the seal's cascade obligation be the *primitive floor* (the self-detection lemma) rather than an all-`¬NonCascade` claim self-detection cannot meet on imprimitive residuals. Axiom-clean. | — |
| `BlockRefinementVisible` | 4187-4195 | §13 **(EOL Step 3a, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** The block of `v` from a closed subset `I` is **refinement-visible**: same `warmRefine` cell ⟹ same `schemeEquiv I` block. Quarantines Step 3a's WL-dimension boundary into one predicate (implied by orbit recovery; broader validity = the open A2 probe). | Definition |
| `schemeEquiv_warmRefine_of_edgeGenerates` | 4197-4216 | §13 **(EOL Step 3a)** The block-visibility bridge on the `EdgeGenerates` class — widens `schemeEquiv_warmRefine_of_pPolynomial` from metric/`PPolynomial` to every edge-generating schurian scheme graph (recovery via `theorem_2_HOR_of_edgeGenerates`, then the general `schemeEquiv_graphOrbit`). | — |
| `blockRefinementVisible_of_edgeGenerates` | 4218-4227 | §13 **(EOL Step 3a)** Discharges `BlockRefinementVisible` on the orbit-recovery (`EdgeGenerates`) class — every closed-subset block of `v` is refinement-visible where the edge relation generates the scheme. | — |
| `SchemePartSeparatesBlock` | 4229-4240 | §13 **(EOL Step 3a, Gate-G crux)** The depth-`n` counting partition `schemePart_at` distinguishes I-membership of `relOfPair v ·`. Strictly weaker than `EdgeGenerates` (asks only that the counting fusion `W` respect the I-boundary). A2-iii's open question = does *every* `ClosedSubset` satisfy it; candidate obstruction = a relation-algebra counting-twin split by `I` (`a2iii-plan §1.1`). | Definition |
| `blockRefinementVisible_of_schemePartSeparates` | 4242-4256 | §13 **(EOL Step 3a — A2-ii graded discharge)** Discharges `BlockRefinementVisible` from counting-separation, **wider than `blockRefinementVisible_of_edgeGenerates`** (holds off the full-recovery class). Proof: shared `warmRefine` cell = shared `(refineStep)^[n]` colour → (`iter_refines_schemePart_at`) shared `schemePart_at n` class → equal I-membership by `hsep`. | — |
| `cell_splits_of_imprimitive` | 4258-4296 | §13 **(EOL Step 3a — the reduction)** Imprimitive (non-trivial closed subset `I`) + block-visibility ⟹ `warmRefine` separates two **non-`v`** vertices (one in `v`'s block, one out): genuine refinement progress on an imprimitive scheme, the ingredient feeding the (3b) decomposition recursion toward the primitive base case (§12 capstone). | — |
## ChainDescent/CascadeOracle.lean

The a-priori cascade-oracle Lean contract (plan: `docs/Archive/ChainDescent/chain-descent-cascade-oracle-lean-brief.md`). Builds axiom-clean (only `refineStep`/`refineStep_iff` + Lean foundationals), no `sorry`. Phase A = soundness/validity, Phase B = the completeness reduction (wired to the axiom-free orbit-recovery theorems), Phase C = the residual obligations: verdict iso-invariance is *discharged conditionally* (`verdictIsoInvariant_of_complete` — it reduces to localisation), and localisation is *split* into (1a) bounded-depth recoverability — **proved** on the cascade class (`RecoverableByDepth` + `recoverableByDepth_cfi`/`_scheme`, anchored by `cellsAreOrbits_of_discrete`) — and (1b) intermediate-to-deep bridging, **open but not GI ∈ P** (cascade-class construction correctness). Only general-class completeness is the GI ∈ P obligation. §C.0 also proves the deferred-decisions foundation `real_stays_real`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `mono` | 58-67 | §C.0 Orbit monotonicity: an `Aut_{S'}`-orbit pair stays an orbit pair at every smaller individualized set `S ⊆ S'`, so a certified merge can be reused at shallower nodes. | — |
| `real_stays_real` | 69-77 | §C.0 Deferred-decisions foundation: a genuine decision (no orbit relation) at `S` is still genuine at every larger `S' ⊇ S`, so deferring a real decision never loses it. | — |
| `orbitPartition_of_support_disjoint` | 111-125 | §C.0.1 **Support backbone.** An automorphism that fixes the individualized set `S` pointwise and sends `v ↦ w` certifies that `v, w` share an `Aut_S`-orbit. | — |
| `exists_orbit_witness_of_aut` | 127-137 | §C.0.1 **Availability depth.** A symmetry of support size `s` keeps its orbit pair certifiable down to individualized sets of size `n − s` — full-support symmetries only at the root, transpositions almost to the leaves. | — |
| `CascadeOracleSpec` | 139-151 | The a-priori cascade-oracle interface: at an internal descent node, return either `none` or a verified automorphism merging two representatives. The cascade analogue of `LinearOracleSpec` (not leaf-gated). | Definition |
| `some_isAut` | 158-166 | **Soundness (subtype-level):** when the oracle returns `some result`, the returned permutation is automatically an automorphism. | — |
| `OrbitMapSpec` | 168-180 | The oracle's soundness contract: every merge it returns is a genuine `Aut_D`-orbit pair — the property that makes pruning the merged branch safe. | Definition |
| `merged_sameCell` | 182-193 | A sound oracle only ever merges vertices that 1-WL already left in the same cell, so it never collapses across cells. | — |
| `OrbitRecoverableAt` | 215-224 | The orbit-recovery target at `S`: the `Aut_S`-orbit relation equals the 1-WL cell relation, so refinement computes orbits and a complete oracle exists. | Definition |
| `orbitRecoverable_of_cascade` | 226-234 | On the cascade class, orbits are recoverable at some set of size ≤ `k` — the general foundation behind every cascade-class oracle instance. | — |
| `orbitRecoverable_scheme` | 246-256 | Rank-2, single-edge-class schurian scheme graphs are orbit-recoverable at depth 1 (axiom-free). | — |
| `CellsAreOrbits` | 258-271 | The genuinely-open half of orbit recovery: every same-cell pair is a real `Aut_S`-orbit pair. Holds at cascade and discretizing depth, fails at generic intermediate nodes — this predicate names the open localisation content. | Definition |
| `orbitRecoverableAt_iff_cellsAreOrbits` | 273-282 | Orbit recoverability is exactly `CellsAreOrbits` (the other half is unconditional), pinning localisation to a single implication. | — |
| `cellsAreOrbits_of_discrete` | 284-296 | **Recursion-bottom anchor.** At any discretizing depth `CellsAreOrbits` holds for free, so localisation is never GI-hard — the descent can always deepen to where cells = orbits. | — |
| `colourMatch_eq_aut` | 316-331 | §C.2 **Leg-(a) linchpin (harvest-window).** At a **discrete** footprint, any colour-match permutation `t` (`warmRefine χ₂ ∘ t = warmRefine χ₁`) carried by an orbit automorphism `g` *equals* `g` — forced by `warmRefine_transport` + injectivity. The harvest *argument* ("harvest window ⟹ harvested"), class-agnostic; no σ-coherence / cycle / rank rebasing. | — |
| `colourMatch_isAut` | 333-344 | §C.2 **Leg-(a) deliverable.** The colour-match candidate `t` is an automorphism (`t = g`) — the harvest's verification succeeds whenever the orbit pair is genuine, given a discrete footprint. | — |
| `indivWithRep` | 346-353 | §C.2 Uniform-colour individualization: committed set `S` by index **plus** one explored rep `r` with a single fresh colour `n+1`. The uniform colour is what lets the orbit automorphism transport branch-`r₁` onto branch-`r₂` (index colours would split the swapped pair). | Definition |
| `indivWithRep_transport` | 355-372 | §C.2 The transport hypothesis discharged for `indivWithRep`: an orbit automorphism fixing `S` and sending `r₁ ↦ r₂` (`r₂ ∉ S`) carries the branch-`r₁` colouring onto the branch-`r₂` colouring (`χ₂ ∘ g = χ₁`). | — |
| `harvest_isAut_of_discrete` | 374-388 | §C.2 **Leg-(a), grounded.** Orbit automorphism exists (fixes path `S`, `g r₁ = r₂`, `r₂ ∉ S`) + **discrete** branch-`r₂` footprint ⟹ the colour-match candidate verifies. The remaining input — discreteness within a bounded depth — is the (class-specific, leg-B-only) depth witness, not the harvest. | — |
| `IsColourMatch` | 390-396 | §C.2 The cascade harvest's construction relation: `t` matches branch-`w`'s refined colours to branch-`v`'s (`warmRefine χ_w ∘ t = warmRefine χ_v`, `χ_v = indivWithRep D v`). The interface the `colourMatchPerm` / `matchOracle` of M-B (open) builds and verifies. | Definition |
| `colourMatch_complete` | 398-408 | §C.2 **Completeness brick.** An `Aut_D` witness `g` (fixes `D`, `g v = w`, `w ∉ D`) *is* a colour-match (`warmRefine_transport` ∘ `indivWithRep_transport`), so at a recoverable node the construction is non-empty. Leg-(a)'s completeness direction. | — |
| `colourMatch_unique` | 410-423 | §C.2 **Uniqueness brick.** `colourMatch_eq_aut` against `IsColourMatch`: at a discrete footprint any colour-match equals the orbit automorphism `g`. With `colourMatch_complete`, the colour-match at a discrete recoverable node exists, is unique, and is `g`. | — |
| `colourMatch_exists_of_cellsAreOrbits` | 439-452 | **§C.2 The firing certificate exists.** At an orbit-recoverable node the orbit automorphism *is* a verifying colour-match (`colourMatch_complete`), so the harvest's construction target is non-empty with no order/σ data and no discreteness — the existence half of folding Leg B's firing into the colour-model recovery. | — |
| `harvest_fires_of_cellsAreOrbits_discrete` | 454-469 | **§C.2 Leg B fires in the colour model.** At an orbit-recoverable + discrete footprint any constructed colour-match for the decision pair verifies as an automorphism — the order-free, class-agnostic firing that folds the hidden-abelian (linear-oracle) case into the same harvest as the cascade oracle. | — |
| `isAut_swap_of_twin` | 498-532 | A twin pair's transposition is an automorphism: if `v, w` have identical adjacency to every other vertex of a simple graph, `swap v w` preserves `adj`. Shared with the linear oracle's twin `ConfigSwap`. | — |
| `orbitPartition_swap_of_twin` | 534-599 | An order-undecided twin pair `v, w ∉ S` is an `Aut_S`-orbit pair at **any** individualized set, witnessed by the transposition `(v w)`. The reconstruction core behind the twin-endpoint and twin-cells results. | — |
| `cellsAreOrbits_of_compl_card_le_two` | 601-715 | **Twin endpoint of the support spectrum.** When at most two vertices stay un-individualized (`|Sᶜ| ≤ 2`), `CellsAreOrbits` holds via the omitted pair's transposition; with `cellsAreOrbits_of_discrete` it pins both ends. | — |
| `cellsAreOrbits_of_twin_cells` | 717-773 | `CellsAreOrbits` at **arbitrary** support whenever every same-cell pair is an order-undecided twin — the genuine-twin / module abelian regime (not CFI, which has no twins). The twin-reconstructible slice of the open localisation obligation. | — |
| `orbitRecoverableAt_of_twin_cells` | 775-794 | Oracle-vocabulary form of `cellsAreOrbits_of_twin_cells`: on the twin regime refinement computes the orbit partition at any node, with no depth bound. | — |
| `RecoverableByDepth` | 796-805 | Cascade-class membership for the oracle contract: there is a polynomially-bounded depth at which cells = orbits (the bound carries all the content). | Definition |
| `recoverableByDepth_cfi` | 815-821 | **(1a), proved for CFI** (axiom-free, odd-degree): recoverable by depth `cfi_depth_bound h` (≤ baseSize ≤ n/6). | — |
| `recoverableByDepth_scheme` | 823-835 | **(1a), proved for schemes** (axiom-free, rank 2 / `|J| = 1`): recoverable by depth 1, at the very node the oracle acts on. | — |
| `recoverableByDepth_pPolynomial` | 837-854 | **(1a), proved for the whole metric/DRG family** (axiom-free, P-polynomial / `|J|=1`): recoverable by depth 1, via `theorem_2_HOR_of_pPolynomial`. Generalizes `recoverableByDepth_scheme` (rank-2 only) to every P-polynomial schurian scheme graph — cycles, Johnson, Hamming, all DRGs — in one oracle-vocabulary export; depth-1 cells non-singleton (genuine recovery at the structural oracle's node). | — |
| `recoverableByDepth_univ` | 856-863 | Every graph is trivially recoverable by depth `n` (individualize everything), so only the *polynomial* depth bound is cascade-class content. | — |
| `CascadeComplete` | 870-877 | Completeness contract: the oracle certifies every genuine `Aut_D`-orbit pair; with soundness it then computes the orbit relation exactly. | Definition |
| `certifies_iff_orbit` | 879-893 | For a sound and complete cascade oracle, it returns `some` exactly on the pairs sharing an `Aut_D`-orbit. | — |
| `CellComplete` | 895-902 | The polynomial completeness contract: the oracle certifies every pair sharing a 1-WL cell (refinement-decidable). | Definition |
| `complete_of_cellComplete_recoverable` | 904-917 | **Key theorem.** At an orbit-recoverable node, certifying every same-cell pair already certifies every orbit — reducing orbit-completeness to a polynomial check. | — |
| `VerdictIsoInvariant` | 964-977 | Iso-invariance contract (strategy §15 gap 2): the oracle's verdict depends only on the iso-invariant 1-WL partition. Derivable — see `verdictIsoInvariant_of_complete`. | Definition |
| `cascadeComplete_of_localization` | 979-990 | Capstone: cell-completeness plus all-nodes recoverability yields `CascadeComplete`, naming the open localisation obligation as its hypotheses. | — |
| `cascadeComplete_of_cellsAreOrbits` | 992-1003 | Capstone stated against the single open implication: cell-completeness plus `CellsAreOrbits` at every node yields `CascadeComplete`. | — |
| `verdictIsoInvariant_of_complete` | 1005-1020 | **Key theorem.** A sound, complete oracle at orbit-recoverable nodes is automatically iso-invariant, so iso-invariance is part of localisation rather than a separate obligation. | — |
| `computes_orbits_of_complete` | 1022-1034 | Capstone: a sound and complete cascade oracle computes the `Aut_D`-orbit relation exactly (program-level correctness, given the completeness obligation). | — |

| `rankPerm_inv_mul_eq_of_match` | 1051-1063 | §C.4 M-B — the rank-composition identity behind `colourMatchPerm = g`: if `g` value-matches the two colourings (`χ₂ ∘ g = χ₁`), then `(rankPerm χ₂)⁻¹ * rankPerm χ₁ = g`. Pure `vertexRank_comp` reindexing, no graph structure. | — |
| `colourMatchPerm` | 1065-1075 | §C.4 **M-B — the colour-match permutation.** The explicit `Equiv.Perm` from the two *discrete* branch colourings, as the rank composition `(rankPerm χ_w)⁻¹ * (rankPerm χ_v)` (`χ_r = warmRefine adj P (indivWithRep n D r)`). Always well-defined given discreteness; `= g` at a recoverable node. | Definition, `noncomputable` |
| `colourMatchPerm_eq_of_orbit` | 1077-1090 | §C.4 **M-B completeness linchpin.** An `Aut_D` witness `g` (`g v = w`, `w ∉ D`) value-matches the two branch colourings (`colourMatch_complete`), so `colourMatchPerm = g` — built from the colours, not assumed. | — |
| `matchOracle` | 1091-1109 | §C.4 **M-B — the colour-match cascade oracle.** Constructs `colourMatchPerm` (when both footprints discrete) and returns it **iff** it verifies as an `Aut_D` orbit map (`IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`). Construct-and-check, not the existential shortcut. | Definition, `noncomputable` |
| `matchOracle_orbitMapSpec` | 1134-1144 | §C.4 **M-B soundness — `OrbitMapSpec`, unconditional.** When `matchOracle` fires, its four checks *are* the `OrbitPartition` witness conditions, so the returned perm certifies a genuine `Aut_D` orbit pair. No discreteness/recoverability hypothesis. | — |
| `matchOracle_cellComplete` | 1146-1182 | §C.4 **M-B completeness — `CellComplete`.** Conditional on every node one-step-discretizing (`hdisc`, = the exposure-depth witness / M-C / "B's core") and `CellsAreOrbits` everywhere (`hco`, = localisation): at a same-cell pair the orbit automorphism exists, `colourMatchPerm = g`, so the oracle fires. | — |
| `matchOracle_cascadeComplete` | 1184-1195 | §C.4 **M-B capstone — `CascadeComplete`.** `matchOracle` computes the orbit relation exactly, reduced to the two named-open hypotheses (discretizing depth + `CellsAreOrbits`); soundness is already unconditional. | — |
| `matchOracle_verdictIsoInvariant` | 1197-1211 | §C.4 **M-B — flag iso-invariance, free.** With soundness + completeness, `verdictIsoInvariant_of_complete` gives the verdict as a function of the iso-invariant 1-WL partition (strategy §15 gap 2) for `matchOracle` on the recoverable class. | — |
| `discrete_of_samePartition` | 1230-1233 | §C.4b Discreteness transfers across `samePartition`: `samePartition χ₁ χ₂ → Discrete χ₁ → Discrete χ₂`. | — |
| `warmRefine_samePartition` | 1235-1240 | §C.4b `warmRefine` respects `samePartition` (specialization of `warmRefine_agree_off'`, `D = ∅`): equal-partition starts warm-refine to equal-partition results. | — |
| `samePartition_indivWithRep_insert` | 1242-1283 | §C.4b **Single-rep footprint = indexed `insert`.** For `r ∉ D`, `indivWithRep n D r` and `individualizedColouring n (insert r D)` induce the same partition (`r` globally unique either way). | — |
| `discrete_indivWithRep_of_discrete_insert` | 1285-1294 | §C.4b **The M-B depth-witness bridge.** M-B's `hdisc` follows from discreteness of the *indexed* `individualizedColouring (insert r D)` — connecting the depth witness to the `RecoverableByDepth` framework, class-agnostically. | — |
| `indivWithSet` | 1311-1316 | §C.5 **M-C — multi-step uniform individualization.** Individualize the committed set `S` by index, plus an explored *set* `R` with a single uniform fresh colour `n+1`. Generalizes `indivWithRep` (`R = {r}`); uniform on `R` is forced by transport (an orbit aut moves `R`). | Definition |
| `indivWithRep_eq_indivWithSet` | 1318-1321 | §C.5 `indivWithRep n S r = indivWithSet n S {r}` — the singleton bridge to M-B. | — |
| `indivWithSet_transport` | 1323-1342 | §C.5 **M-C transport.** An orbit aut `g` fixing `S` with `R₂ = R₁.image g` carries the branch-`R₁` colouring onto branch-`R₂` (`χ₂ ∘ g = χ₁`); the `indivWithRep_transport` generalization (uniform colour on the moved set is what makes it hold). | — |
| `IsColourMatchSet` | 1344-1348 | §C.5 The multi-step colour-match relation: `t` matches branch-`R₂`'s refined colours to branch-`R₁`'s. The `IsColourMatch` generalization. | Definition |
| `colourMatchSet_complete` | 1350-1357 | §C.5 **M-C completeness brick.** The orbit aut `g` (fixing `S`, `R₂ = R₁.image g`) *is* a colour-match (`warmRefine_transport ∘ indivWithSet_transport`). | — |
| `colourMatchSet_unique` | 1359-1369 | §C.5 **M-C uniqueness brick.** At a discrete branch-`R₂` footprint any colour-match `= g`, via the colouring-generic `colourMatch_eq_aut`. | — |
| `harvestSet_isAut_of_discrete` | 1371-1381 | §C.5 **M-C harvest brick.** At a discrete branch-`R₂` footprint the colour-match candidate verifies (`= g`) — the harvest now fires at a footprint discretized by an explored *set* (a sequence), not just one rep. | — |
| `colourMatchPermSet` | 1383-1390 | §C.5 **M-C — the multi-step colour-match permutation.** The rank composition `(rankPerm χ_{R₂})⁻¹ * (rankPerm χ_{R₁})` for set footprints; `colourMatchPerm` is the `R₁={v}, R₂={w}` case. | Definition, `noncomputable` |
| `colourMatchPermSet_eq_of_orbit` | 1392-1402 | §C.5 `colourMatchPermSet = g` at a recoverable set-footprint (`rankPerm_inv_mul_eq_of_match` ← `vertexRank_comp` + `colourMatchSet_complete`); the multi-step `colourMatchPerm_eq_of_orbit`. | — |
| `colourMatchSet_exists_of_cellsAreOrbits` | 1404-1417 | §C.5 **The multi-step firing certificate exists.** From `CellsAreOrbits` at a same-cell pair, for *any* exploration set `R₁` the orbit aut `g`, partner `R₂ = R₁.image g`, and the colour-match all exist. The open piece (M-D) is that the oracle's branch-`w` set *is* `R₁.image g` (lockstep). | — |
| `matchOracleSet` | 1430-1450 | §C.6 **M-D — the multi-step colour-match oracle.** Like `matchOracle` but individualizes a whole explored *set* `expand chain r` (per an exploration selector) on top of the committed path; constructs `colourMatchPermSet`, returns it **iff** it verifies `IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`. | Definition, `noncomputable` |
| `matchOracleSet_orbitMapSpec` | 1479-1489 | §C.6 **M-D soundness — `OrbitMapSpec`, unconditional.** When it fires the four checks *are* the `OrbitPartition` witness; no discreteness/recoverability/lockstep hypothesis. | — |
| `LockstepExpand` | 1491-1501 | §C.6 **The lockstep correspondence** as equivariance of the exploration rule: any `P`-preserving automorphism fixing the committed path carries one branch's exploration set onto the other's (`expand chain (g v) = (expand chain v).image g`). Discharged for `forcedExpand` (`Cascade.lean`). | Definition |
| `matchOracleSet_cellComplete` | 1503-1543 | §C.6 **M-D completeness — `CellComplete`.** Reduced to set-footprint discreteness (the multi-step depth witness) + `CellsAreOrbits` + `LockstepExpand`: the lockstep supplies `R₂ = R₁.image g`, so `colourMatchPermSet = g` and the oracle fires. | — |
| `matchOracleSet_cascadeComplete` | 1545-1557 | §C.6 **M-D capstone — `CascadeComplete`** (the multi-step oracle computes the orbit relation exactly), reduced to the three named-open hypotheses. | — |
| `matchOracleSet_verdictIsoInvariant` | 1559-1572 | §C.6 **M-D — flag iso-invariance, free** (via `verdictIsoInvariant_of_complete`). | — |
| `matchOracle_fires_of_insertDiscrete` | 1605-1628 | §C.7 **Honest per-node firing (`hco`-free).** At a node where committing the path plus the query rep discretizes (the indexed `RecoverableByDepth` form, bridged by §C.4b), `matchOracle` fires on **any** genuine `Aut_D` orbit pair `(v,w)` (`v,w ∉ D`) — the orbit witness is consumed directly, so no `CellsAreOrbits`. | — |
| `matchOracle_orbit_of_fire_mono` | 1630-1644 | §C.7 **Propagate via `mono`.** A merge certified at a node holds at every shallower committed set `S ⊆ chain.D` (`OrbitPartition.mono`) — the "fire deep, prune shallow" step. | — |
| `matchOracle_certifies_iff_orbit_of_insertDiscrete` | 1646-1672 | §C.7 **Exact orbit decider at the discretizing depth.** At a footprint-discretizing node, `matchOracle` fires on `(v,w)` **iff** they are a genuine `Aut_D` orbit pair (`hco`-free). Limits: holds only under the discreteness hypotheses (cascade depth), and decides the *path-fixing* `Aut_D`, not global `Aut`. | — |
| `indivWithSeq` | 1693-1698 | §C.8 **Level-coloured exploration sequence (Leg 1).** Committed `S` by index plus the `i`-th element of `rs` by its *position* colour `n+1+i`; the position colouring (not vertex index) is what transports under an orbit automorphism. | Definition |
| `samePartition_indivWithSeq` | 1709-1777 | §C.8 **A1: level-coloured sequence = indexed union.** `indivWithSeq n S rs` and the indexed `individualizedColouring n (S ∪ rs.toFinset)` induce the same partition (each `rs`-vertex globally unique); unconditional. | — |
| `discrete_indivWithSeq_of_discrete_union` | 1779-1790 | §C.8 **The Leg-1 depth-witness bridge (sequence).** Sequence-footprint discreteness follows from discreteness of the indexed `individualizedColouring n (S ∪ rs.toFinset)`, so `hdiscSeq ⟸ recoverableByDepth`. Sequence generalization of `discrete_indivWithRep_of_discrete_insert`. | — |
| `idxOf_map_of_injective` | 1804-1816 | §C.8 **Position preserved by `map`.** `(l.map g).idxOf (g a) = l.idxOf a` for a permutation `g` — the pure-list core of sequence transport. | — |
| `indivWithSeq_transport` | 1818-1839 | §C.8 **A2 transport.** An orbit aut `g` fixing `S` with `rs₂ = rs₁.map g` carries the branch-`rs₁` level colouring onto branch-`rs₂` (`χ₂ ∘ g = χ₁`) — position via `idxOf_map_of_injective`, off-sequence via `individualizedColouring` invariance. | — |
| `IsColourMatchSeq` | 1841-1844 | §C.8 The sequence colour-match relation (`IsColourMatchSet` analogue): `t` matches branch-`rs₂`'s refined colours to branch-`rs₁`'s. | Definition |
| `colourMatchSeq_complete` | 1846-1853 | §C.8 **Sequence completeness brick.** The orbit aut `g` (fixing `S`, `rs₂ = rs₁.map g`) *is* a colour-match (`warmRefine_transport ∘ indivWithSeq_transport`). | — |
| `colourMatchPermSeq` | 1855-1862 | §C.8 **The sequence colour-match permutation.** Rank composition `(rankPerm χ_{rs₂})⁻¹ * rankPerm χ_{rs₁}` for level-coloured footprints; `colourMatchPermSet` with the uniform set replaced by the sequence. | Definition, `noncomputable` |
| `colourMatchSeq_exists_of_cellsAreOrbits` | 1876-1889 | §C.8 **The level-coloured firing certificate exists.** From `CellsAreOrbits`, for any sequence `rs₁` the orbit aut `g`, partner `rs₂ = rs₁.map g`, and the colour-match exist. The open piece is the ordered lockstep (A2b). | — |
| `matchOracleSeq` | 1902-1922 | §C.8 **The multi-step sequence colour-match oracle.** Like `matchOracleSet` but individualizes the ordered sequence `expand chain r` via `indivWithSeq` (so its depth witness is A1-reducible); construct-and-check on `colourMatchPermSeq`. | Definition, `noncomputable` |
| `matchOracleSeq_orbitMapSpec` | 1950-1959 | §C.8 **Sequence soundness — `OrbitMapSpec`, unconditional.** When it fires the four checks *are* the `OrbitPartition` witness. | — |
| `LockstepExpandSeq` | 1961-1972 | §C.8 **The sequence lockstep.** The ordered (`map`, not `image`) `LockstepExpand` analogue: `expand chain (g v) = (expand chain v).map g`. Strictly stronger than the set lockstep; provably false in the multi-step regime (`lockstep_disc_imp_stab_trivial`). | Definition |
| `matchOracleSeq_cellComplete` | 1974-2013 | §C.8 **Sequence completeness — `CellComplete`.** Reduced to `hdiscSeq` (A1-reducible) + `hco` + `LockstepExpandSeq`. | — |
| `matchOracleSeq_cascadeComplete` | 2015-2027 | §C.8 **Sequence capstone — `CascadeComplete`**, reduced to the same three hypotheses (the last jointly unsatisfiable with `hdiscSeq` for multi-step — see `lockstep_disc_imp_stab_trivial`). | — |
| `matchOracleSeq_verdictIsoInvariant` | 2029-2042 | §C.8 **Sequence flag iso-invariance, free** (via `verdictIsoInvariant_of_complete`). | — |
| `lockstep_disc_imp_stab_trivial` | 2074-2108 | §C.8 **The discretizing-oracle limit (conservation of obstruction).** `LockstepExpandSeq ∧ hdiscSeq ⟹ stab_{Aut_D}(v) = 1`: the sequence oracle's completeness hypotheses hold jointly only in the single-rep regime, so the discretizing colour-match cannot harvest a multi-step moved orbit (→ cross-branch / Schreier–Sims). | — |
## ChainDescent/LinearOracle.lean

The linear-oracle / abelian-stripping work (tractable-buildout B2; plan + status in `docs/chain-descent-linear-oracle.md` §8.2). Built on the §15.8 scaffolding (`DirAssignment`/`flipPair`/`LinearOracleSpec`/`LeafTwistSpec`/`canonAdj`). Builds axiom-clean (`refineStep`/`refineStep_iff` + foundationals), no `sorry`. **B2 soundness core DONE 2026-05-30:** §L.1 soundness anchor, §L.2 the *forced* candidate twist (rank rebasing — the construction is determined, not searched; the `canonAdj_rebase` bridge), §L.3 abelian `Z₂^d` structure. Remaining: `canonForm` lex-min tie (needs descent-with-pruning model), completeness, lifting twists to subgroup `N` (Part A).

### §L.1 — Soundness anchor (B2.1)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RealizesFlip` | 51-60 | **Soundness anchor.** The relation "twist `t` relabels branch `σ`'s leaf to the flipped branch `flipPair σ a b`'s leaf" — the `LeafTwistSpec` conclusion with the partner branch pinned to the flip, i.e. the pruning justification. | Definition |
| `TwistWitness` | 62-82 | The verified data a twist discovery returns: the decided pair `(a,b)`, the candidate permutation `t`, its `IsAut` proof (the §4.5 edge-check, sole soundness anchor), and a `RealizesFlip` proof. | Structure |
| `twistOracle` | 84-94 | A concrete `LinearOracleSpec` parameterised by an abstracted `discover` function (C#-side canonical-id matching); returns the verified automorphism from a `TwistWitness`, `none` otherwise. Verification lives inside the witness, so every output is a genuine automorphism. | Definition |
| `twistOracle_leafTwist` | 96-115 | **Key theorem (B2.1 discharge).** `twistOracle` satisfies `LeafTwistSpec`, with the flipped branch as the explicit witness `σ' = flipPair σ` (sharper than the bare existential) — closing the pruning-justification contract for any sound discovery. | — |

### §L.2 — The forced candidate twist (B2.2 + most of B2.3)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `canonAdj_rebase` | 158-173 | **The rebasing bridge.** Relabelling `σ`'s canonical leaf by the rank rebasing `rankPerm π_{σ'} * (rankPerm π_σ)⁻¹` yields `σ'`'s leaf; the flip is the `σ' = flipPair σ` instance. | — |
| `candidateTwist` | 183-191 | **The forced candidate twist** for decision `(a,b)`: the rank rebasing `rankPerm π_flip * (rankPerm π_σ)⁻¹`. Always realises the flip; the twist is determined, not searched. | Definition, `noncomputable` |
| `candidateTwist_realizesFlip` | 193-200 | The forced candidate always realises the flip — the construction is forced, with no ambiguity. | — |
| `candidateTwist_unique` | 202-214 | **Determinacy.** The candidate is the unique permutation rank-aligning `σ` to the flipped branch — the leaf-level iso-invariance gate, making twist discovery deterministic in iso-invariant rank data. | — |
| `twistWitness_of_isAut` | 216-233 | The oracle reduces to one check: a verified-automorphism forced candidate yields a complete `TwistWitness`. Discovery is a single decidable edge-check. | Definition, `noncomputable` |
| `canonicalTwistOracle` | 234-248 | **The canonical twist oracle.** A fully concrete `LinearOracleSpec`: for the selected pair, compute the forced candidate and return it iff it verifies as an automorphism. The only abstracted piece is pair selection (soundness-irrelevant). | Definition, `noncomputable` |
| `canonicalTwistOracle_leafTwist` | 250-258 | **Key theorem.** `canonicalTwistOracle` satisfies `LeafTwistSpec` (it is a `twistOracle`) — a concrete verified linear oracle, sound by construction. | — |

### §L.3 — Abelian structure (B2.4, partial)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `candidateTwist_flip_inv` | 281-290 | **`Z₂` involution.** The forced candidate for the flip-back is the inverse of the candidate for the flip; with `flipPair_comm` this is the elementary-abelian `Z₂^d` structure of the residual. | — |

### §L.4 — Completeness / effectiveness (when the oracle fires)

Characterizes *when* the oracle fires and proves firing is semantically justified. The
oracle is complete exactly on the **abelian regime** (forced candidate ∈ Aut) — the
calculator §6 boundary; the general converse fails (conjugation gap). The
abelian-sufficiency lemma (forced candidate IsAut for genuine abelian flips, via
`warm_6_2` rank machinery) is the open core scoped in the §L.4 doc-comment.

| Name | Description | Notes |
|------|-------------|-------|
| `isAut_candidateTwist_iff_aligned` | 328-343 | **Firing characterisation.** The forced candidate is an automorphism iff some automorphism is rank-aligned (`g · π_σ = π_flip`) — so the whole completeness question is "does a rank-aligned automorphism exist?" | — |
| `RealizableFlip` | 345-351 | The decision is a genuine `Aut(adj)` symmetry: some automorphism realises the flip (the two branches are isomorphic) — what pruning should require. | Definition |
| `realizableFlip_of_isAut_candidateTwist` | 353-364 | **Firing is semantically justified.** When the forced candidate verifies, the branches are genuinely `Aut(adj)`-equivalent (the candidate is the witness) — pruning reflects a real symmetry. | — |
| `canonicalTwistOracle_isSome_iff` | 366-382 | **Key theorem.** Given the pair selector returns `(a,b)`, the oracle fires iff the forced candidate is an automorphism — the entire completeness question is one decidable edge-check. | — |
| `candidateTwist_flipBack_isAut` | 384-395 | **`Z₂`-direction consistency.** If the forced candidate for `σ → flip` verifies, so does the candidate for the flip-back — the oracle prunes both directions of a genuine `Z₂` decision consistently. | — |

### §L.5 — Toward abelian sufficiency (partial)

The open core of completeness — *forced candidate ∈ Aut for abelian decisions* — needs
gadget-level rank-alignment (at a leaf both branches are discrete, so `warm_6_2`'s
partition equality is vacuous; the content is in the rank order). Provable progress:

| Name | Description | Notes |
|------|-------------|-------|
| `candidateTwist_eq_one_of_rankPerm_eq` | 423-434 | **Absorbed decision.** Equal leaf rank permutations force the candidate to be the identity — the degenerate end of the abelian regime. | — |

### §L.7 — The CFI bridge (M1b): candidate as a conjugate of a graph automorphism

Now that `refineStep` is concrete, the cross-config transport (`§16.2b` in ChainDescent.lean)
lets us express the forced candidate via a *real* automorphism. A **config-swap** `g` carries the
σ-branch config onto the flip-branch config; it forces `π_σ = π_flip · g`, so the candidate is the
`π_σ`-conjugate of `g⁻¹`. This reduces the opaque `IsAut candidate adj` to the structural gadget
rank-alignment, isolating the genuine CFI nut (shared with Tier-3a B1 `hwit`): (1) a config-swap
exists, (2) its `π_σ`-conjugate is an automorphism.

| Name | Description | Notes |
|------|-------------|-------|
| `ConfigSwap` | 586-598 | A config-swap for decision `(a,b)`: a graph automorphism carrying the σ-branch configuration onto the flip-branch configuration (fixes `χι`, sends `σ.σ` to `(flipPair σ).σ`). For CFI, the gadget twist swapping the decided pair. | Structure |
| `configSwap_rankPerm` / `_flip` | The leaf rank perms differ by `g`: `π_σ = π_flip · g` (resp. `π_flip = π_σ · g⁻¹`), from transport + `vertexRank_comp`. | axiom-light |
| `candidateTwist_eq_conjugate` | 626-636 | **The rank-space reduction.** Given a config-swap `g`, the forced candidate is the `π_σ`-conjugate of `g⁻¹` (`candidateTwist = π_σ · g⁻¹ · π_σ⁻¹`) — the opaque rebasing exposed as a conjugate of a genuine automorphism. | — |
| `isAut_candidateTwist_iff_conjugate` | 638-649 | **The reduction.** `IsAut candidate adj ↔ IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj` — the rank-space firing obligation is exactly the gadget rank-alignment, the concrete nut shared with Tier-3a B1. | — |

**§L.7b — vertex-model soundness (Approach C, the faithful C# model).** A config-swap is a real
graph automorphism, so both branches give the *same canonical leaf* — no rank-alignment needed. This
is the soundness the C# `TwistConstruction` actually uses (it verifies a vertex automorphism, not the
rank rebasing).

| Name | Description | Notes |
|------|-------------|-------|
| `canonAdj_eq_of_configSwap` | 660-675 | **Equal canonical leaves.** A config-swap implies both branches produce the identical canonical leaf — the vertex-model soundness statement (pruning the flip branch loses nothing), needing no rank-alignment. | — |
| `realizableFlip_of_configSwap` | 677-691 | A config-swap implies `RealizableFlip` (identity witness, since the leaves coincide) — the decision is a genuine `Aut(adj)` symmetry with no rank-alignment obligation. | — |

**§L.8 — CFI completeness: config-swap from a swapping automorphism (M1c step 3, the cascade-1b bridge).**
*Where a config-swap comes from.* A swapping automorphism `g` (`g a = b`, `g b = a`) is exactly an
`OrbitPartition adj P S a b` witness specialised to the size-2 decision cell — the cascade oracle's
currency. So linear-oracle CFI completeness reduces to the **shared cascade-1b** obligation
(bounded-depth half `recoverableByDepth_cfi` proved; decision-node-depth bridge open, *not* `GI∈P`).

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_aut` | 723-766 | **General constructor (the `hwit` entry point).** *Any* swapping automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and preserves `σ.σ` *off the flip pair* (`σ.σ (g v)(g u) = σ.σ v u` for `(v,u) ∉ {(a,b),(b,a)}`) is a `ConfigSwap` — `g` need **not** be a transposition (may move the whole coupled component). Removes the config-swap *packaging* from the open content: once the CFI gadget twist `g` and its off-pair `σ`-action are known, the `ConfigSwap` is built with no rank-alignment. | Definition |
| `configSwap_of_swap` | 768-819 | **Closed instance (the `Z₂` twin-swap).** A σ-cell-coherent transposition automorphism (`g` swaps `a,b`, fixes the rest and `χι`) is a `ConfigSwap` — the simplest genuine abelian decision. Now a thin specialisation of `configSwap_of_aut` (transposition ⇒ off-pair preservation = σ-cell-coherence). | Definition |
| `configSwap_of_twin` | 821-849 | **The twin → config-swap bridge.** An (adj, σ)-twin decision pair (adjacency-twin on a simple graph plus σ-cell-coherent, `χι a = χι b`) admits a `ConfigSwap` via the transposition `(a b)` — the linear-oracle analog of `cellsAreOrbits_of_twin_cells`, both oracles firing on the same twin/module class through one shared lemma. Not CFI (which has no twins). | Definition |
| `ConfigSwapRecoverable` | 851-861 | **Decision-node recoverability** (the named cascade-1b obligation for the linear oracle): every leaf decision admits a config-swap. The graph-level analog of `AbelianSufficiencyHolds`; open discharge `configSwapRecoverable_of_cfi` is downstream. | Definition |
| `canonAdj_eq_of_configSwapRecoverable` | 863-874 | **Capstone (pruning soundness).** Config-swap-recoverability implies both branches give the identical canonical leaf at every decision — reducing the oracle's effectiveness to the single `ConfigSwapRecoverable` hypothesis. | — |
| `realizableFlip_of_configSwapRecoverable` | 876-887 | **Capstone (real symmetry).** Config-swap-recoverability implies every leaf decision is a genuine `Aut(adj)` symmetry — vertex-model completeness, no rank-alignment needed. | — |

**§L.9 — CFI gadget twist fires the oracle (Phase 6a: wiring the Stage-3 cycle-space flip).** The
Stage-3 gadget flip (`CFI.lean §15`, `IsCFI'.cfiFlipAut`) is now constructed; this section wires it into
`configSwap_of_aut` and reduces `ConfigSwapRecoverable` for CFI to the existence of the right cycle `F`
per decision.

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_cfiFlipAut` | 910-925 | **The CFI gadget twist is a config-swap** (unconditional bridge). `configSwap_of_aut` instantiated with `g := cfiFlipAut F` (an `Aut(adj)` involution by `isAut_cfiFlipAut`): if the flip swaps `(a,b)`, fixes `χι`, and carries `σ` off the pair, it is a `ConfigSwap`. The concrete soundness — the vertex-space gadget twist (the C#'s witness) fires the oracle, no rank-alignment. | Definition |
| `CFIGadgetFlippable` | 927-941 | **The named cascade-1b residual.** Every leaf decision admits an even-symmetric cycle `F` whose gadget flip swaps `(a,b)`, fixes `χι`, carries `σ` off the pair. Commits the CFI witness to the gadget-flip mechanism (matching the C#); the open content is purely `F`'s existence per decision (cascade-1b). | Definition |
| `configSwapRecoverable_of_cfi` | 943-953 | **`ConfigSwapRecoverable` for CFI via the gadget flip.** `CFIGadgetFlippable h → ConfigSwapRecoverable` — the discharge reduced to its irreducible combinatorial core (the decision-local even cycle's existence). Feeds the capstones ⟹ oracle fires on every CFI decision. | — |

Open (not a `sorry`): **`CFIGadgetFlippable`** — that the decision-local even cycle `F` *exists* for every
decision (the flip is built and proven sound; what remains is the cycle through the decision edge, local
to the decided gadget). Its three per-decision obligations (swap `(a,b)`, fix `χι`, carry `σ` off the
pair) are the descent-coherence content of cascade-1b — the decision-node-depth half, shared with the
cascade oracle, *not* `GI∈P`.

**§L.9 follow-on — the conditions reduced to locality + cell-coherence.** Decouples the gadget-flip
mechanics from the descent's cell structure, so the residual is the cascade-1b shape (F-locality +
cell-coherence), not the opaque `configSwap_of_aut` package.

| Name | Description | Notes |
|------|-------------|-------|
| `swapsConfig_off_pair_of_local` | 965-1012 | **The σ-off-pair reduction (general `g`, reusable).** Any `g` swapping `(a,b)`, fixing decided vertices off `{a,b}`, preserving the decided set and `P₀`, satisfies the off-pair condition given only **σ-cell-coherence** at `(a,b)`. Off-D via `agrees_off` + P₀-invariance; on-D via the coherence case-analysis. | — |
| `preserves_D_of_involutive_local` | 1014-1034 | Decided-set preservation for an involutive local swap (`g x ∈ D ↔ x ∈ D` from `g²=id` + swap + fix-off-`{a,b}`). The `hgD` input above, discharged for the gadget flip. | — |
| `cfiFlipAut_fixesχι_of_support` | 1036-1049 | **The `hgχ` reduction.** The flip fixes `χι` once it does on the F-touched gadgets — Phase-4 locality fixes every `F`-free gadget outright. Reduces global `hgχ` to χι-coherence on the (small) F-support. | — |
| `configSwap_of_cfiFlipAut_local` | 1051-1078 | **The reduced bridge.** A `ConfigSwap` from {`F` even+symmetric, swap, **F is D-local**, σ-cell-coherent, `P₀` Aut-invariant, χι-coherent on F-support} — the three `configSwap_of_aut` conditions discharged via the reductions above. | Definition |
| `CFIGadgetFlippableLocal` | 1080-1095 | The reduced per-decision predicate: an even-symmetric **D-local** `F` whose flip swaps `(a,b)`, with σ cell-coherent and χι coherent on the F-support. The conditions are now the descent-coherence / cycle-locality (cascade-1b) facts. | Definition |
| `configSwapRecoverable_of_cfi_local` | 1097-1108 | `ConfigSwapRecoverable` from `CFIGadgetFlippableLocal` (+ `P₀` Aut-invariance) — the discharge via the decoupled hypotheses. | — |

**§L.9 (C1b.1) — the CFI glue: parity-pair decisions.** Reduces `CFIGadgetFlippableLocal` to the
explicit-edge form, discharging the swap obligation in advance (via C1b.0).

| Name | Description | Notes |
|------|-------------|-------|
| `CFIParityDecisionFlippable` | 1120-1136 | The reduced cascade-1b hypothesis: every decision `(a,b)` is the parity-pair of a base edge `{v,w}` (`a = e^{b₀}_{v→w}`, `b = e^{¬b₀}`) admitting an even-symmetric cycle `F` with `{v,w} ∈ F`, D-local, σ/χι cell-coherent. The swap is no longer an obligation (it's `cfiFlipAut_swaps_endpointVertex`); only cycle existence + coherence remain. | Definition |
| `cfiGadgetFlippableLocal_of_parity` | 1138-1151 | **The C1b.1 glue.** `CFIParityDecisionFlippable → CFIGadgetFlippableLocal` — the body's two swap conjuncts from `cfiFlipAut_endpointVertex` + `F v w = true`; the rest passes through. Open content narrows to C1b.2 (cycle exists) + C1b.3 (decisions are parity-pairs + coherence). | — |

Transport chain it builds on (ChainDescent.lean `§16.2b`): `signature_transport`, `sigKey_transport`,
`refineStep_transport`, `iterate_refineStep_transport`, `warmRefine_transport` — cross-config (two
`(P,χ)` related by an automorphism), the value-level generalisation of the `*_invariant_of_isAut`
chain, newly provable because `refineStep` is concrete. All axiom-light.

### §L.6 — Relativized completeness (the retargeting)

The general completeness statement ("forced candidate fires whenever the branches are
isomorphic") *provably* cannot close — a realizing aut agrees with the forced candidate only
up to a conjugate of `Aut(adj)` (`rankPerm_comp`), the split-or-Johnson wall *by design*, and
the **same gap the a-priori cascade oracle carries** (`CascadeOracle.lean` §4.3). The fix is
the cascade oracle's **Phase-B move**: relativize completeness to the recoverable/abelian
class and reduce it to orbit recovery. This scaffold names the relativized target and isolates
the one open obligation (`AbelianSufficiencyHolds` on the CFI class — the leaf-level instance
of orbit recovery, the same nut as Tier-3a B1's `hwit`).

| Name | Description | Notes |
|------|-------------|-------|
| `RankAligned` | 481-489 | The algebraic firing condition: a rank-aligned automorphism exists (`∃ g ∈ Aut(adj), g · π_σ = π_flip`). The oracle fires exactly when this holds. | Definition |
| `isAut_candidateTwist_iff_rankAligned` | 491-499 | **Interface.** The forced candidate is an automorphism iff `RankAligned` — the completeness question restated against the named predicate. | — |
| `AbelianSufficiency` | 501-511 | **The per-decision relativized completeness target.** `RealizableFlip → IsAut candidate`: if the flip is a real symmetry then the forced candidate verifies. False in the non-abelian regime (the wall); the claim to discharge on the abelian/cascade class. | Definition |
| `oracleFires_of_abelianSufficiency` | 513-528 | **Capstone (what suffices).** `AbelianSufficiency` plus a real symmetry implies the oracle fires — the linear-oracle analog of cascade's `cascadeComplete_of_localization`. | — |
| `abelianSufficiency_of_rankPerm_eq` | 530-541 | **Non-vacuous closed instance.** The absorbed decision is abelian-sufficient (candidate `= 1 ∈ Aut` outright) — validates the scaffold against a real instance. | — |
| `AbelianSufficiencyHolds` | 543-551 | The graph-level discharge target: every leaf decision is abelian-sufficient. Open obligation `abelianSufficiencyHolds_of_cfi` is downstream (via `theorem_1_HOR_cfi_oddDeg`, the same nut as Tier-3a B1's `hwit`). | Definition |
| `oracleFires_of_abelianSufficiencyHolds` | 553-567 | **Graph-level capstone.** `AbelianSufficiencyHolds` implies the oracle fires at every leaf decision that is a real symmetry — relativized completeness on the abelian class. | — |

## ChainDescent/Group.lean

Part A (A1–A3) of `docs/chain-descent-tier3-tractable-buildout.md` — the group object
the orbit-recovery program deliberately avoided, now needed for Tier-3 vocabulary
(`H₀ ⊵ … ⊵ H_k`, quotient graphs). Pure glue over Mathlib group theory + the existing
`IsAut` lemmas; **no `refineStep`** dependency (axioms `[propext, Classical.choice, Quot.sound]`).
A4 (the quotient *graph* `G/H` + cell = quotient-vertex lemma) is **not** here — it is the
medium-risk Mathlib gap gating B1.

### A1 — `Aut(G)` as a group

| Name | Description | Notes |
|------|-------------|-------|
| `AutGroup adj` | §A1 **The automorphism group.** `{π | IsAut π adj}` as a `Subgroup (Equiv.Perm (Fin n))` — the group object Tier-3 vocabulary (`H₀ ⊵ … ⊵ H_k`, quotient graphs) is stated over. | Definition |
| `mem_autGroup` | 69-70 | Membership in `AutGroup adj` is exactly `IsAut π adj` (`@[simp]` unfolding). | `@[simp]` |
| `orbitPartition_iff_autGroup` | 72-87 | §A1 **The `OrbitPartition` ↔ `AutGroup` bridge.** Repackages the bare permutation of the orbit relation as a genuine group element in the pointwise-`S`-stabilizer that preserves `P`, keeping `OrbitPartition` the working object while exposing the group element where the chain needs it. | — |

### A2 — Action on vertices + orbit bridge

| Name | Description | Notes |
|------|-------------|-------|
| `autGroup_smul` | 96-98 | §A2 The subgroup action's `smul` is permutation application: `g • v = (↑g) v` (`@[simp]`). | `@[simp]` |
| `mem_orbit_autGroup_iff` | 100-109 | §A2 **Orbit membership, unfolded.** `w` lies in `v`'s `AutGroup`-orbit iff some automorphism sends `v` to `w` (the pure-orbit form, before `OrbitPartition`'s `P`-preservation refinement). | — |
| `mem_orbit_autGroup_iff_orbitPartition` | 111-125 | §A2 **The orbit bridge.** Under `P`-invariance, `v`'s `AutGroup`-orbit coincides with the root relation `OrbitPartition adj P ∅` — the group-level reading of the support backbone's root case. | — |

### A3 — Normal subgroup chains

| Name | Description | Notes |
|------|-------------|-------|
| `LayerChain adj` | §A3 A finite descending chain `AutGroup adj = layer 0 ⊵ … ⊵ layer len = ⊥`, each layer relatively normal in its predecessor — the `H₀ ⊵ … ⊵ H_k` substrate Tier-3a (B1) reasons over. | Structure |
| `LayerChain.trivial` | 155-172 | §A3 **The trivial chain** `AutGroup adj ⊵ ⊥` (length 1); witnesses `LayerChain` is inhabited. | Definition |

### A4 — quotient graph + cell = quotient-vertex

| Name | Description | Notes |
|------|-------------|-------|
| `orbitSetoid adj P S` | §A4 The `Aut_S`-orbit relation `OrbitPartition adj P S` packaged as a `Setoid` from its proved `refl`/`symm`/`trans`. | Definition |
| `OrbitQuotient adj P S` | §A4 **The quotient vertex set** `V(G)/Aut_S` — the vertices of the quotient graph. | `abbrev` |
| `orbitMk` / `orbitMk_eq_iff` | The quotient map `v ↦ ⟦v⟧`; `orbitMk v = orbitMk w ↔ OrbitPartition adj P S v w`. | Definition / `Quotient.eq` |
| `cell_iff_orbitMk_eq` | 226-242 | §A4 **The cell = quotient-vertex lemma.** Under `CellsAreOrbits`, two vertices share a 1-WL cell of `(G, S)` iff they are the same quotient vertex — the correspondence B1's cascade-composition induction steps through. | — |
| `QuotientAdjCompatible` | 246-254 | §A4 **Quotient-adjacency compatibility.** The condition that `adj v w` is constant on `Aut_S`-orbit pairs — exactly when a simple induced adjacency on the quotient is well-defined (holds at discreteness, fails for coarser `S`). | Definition |
| `quotientAdj` / `quotientAdj_mk` | The induced adjacency on `OrbitQuotient`, well-defined under `QuotientAdjCompatible` (via `Quotient.lift₂`); `quotientAdj h ⟦v⟧ ⟦w⟧ = adj.adj v w` (`rfl`). | Definition / `@[simp]` |
| `quotientAdjCompatible_of_discrete` | 269-280 | §A4 At discreteness the quotient graph is always well-defined (orbits are singletons) — the recursion-bottom anchor, paralleling `cellsAreOrbits_of_discrete`. | — |
| `orbitPartition_empty_iff_orbitRel` | 290-302 | §A4 The root orbit relation `OrbitPartition adj P ∅` equals the `AutGroup` `MulAction` orbit relation (under `P`-invariance) — the relational form of the A2 orbit bridge, symmetrised for `orbitRel`. | — |
| `orbitQuotientEquivAutGroup` | 304-312 | §A4 **The root quotient is `V(G)/Aut(G)`.** Under `P`-invariance, `OrbitQuotient adj P ∅` is equivalent to the `MulAction` orbit quotient of `AutGroup adj`, tying A4's relational quotient back to A1/A2's group object. | Definition |

| `stabilizer_eq_bot_of_isPretransitive_comm` | 324-342 | **(seal core L1, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** A transitive, faithful, **abelian** action is **free**: every point-stabilizer is trivial ("transitive abelian ⟹ regular"). The textbook root of "no non-consumed abelian species". | — |
| `existsUnique_smul_of_isPretransitive_comm` | 344-355 | **(seal core L2)** Unique candidate: in a transitive faithful abelian action exactly one group element moves `a` to `b` (existence from transitivity, uniqueness from L1's trivial stabilizer). | — |
| `smul_eq_on_orbit_of_comm` | 357-366 | **(seal core L3 — load-bearing, axiom-free)** Quotient-free, faithfulness-free form: if `g, h` both move `a` to `b` then they agree on the **whole orbit** of `a` (`g•c = k•b = h•c` for `c = k•a`). The "unique-candidate-on-the-cell" the linear-oracle harvest reads — holds for an abelian residual even with non-trivial global stabilizers (CFI). | — |
| `aut_agree_on_orbit_of_comm` | 368-382 | **(seal instantiation)** L3 for `AutGroup adj`: an **abelian residual** ⟹ two automorphisms both sending `a ↦ b` agree on every `c` in `a`'s orbit, so the decision is determined on its cell (always consumable). | — |
| `not_comm_of_orbit_disagree` | 384-393 | **(seal headline — no non-consumed abelian species)** Contrapositive: a decision `a ↦ b` whose two candidate automorphisms **disagree** on the cell forces a **non-abelian** residual. With the §12 capstone (large primitive non-abelian ⟹ Cameron), the only non-consumed symmetry is a Cameron section — the bottom-up, citation-free half of the seal. | — |
| `card_eq_of_isPretransitive_comm` | 404-418 | **(seal Step 4 — order side, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** A transitive, faithful, **abelian** action has `Nat.card G = Nat.card α`: the orbit map `g ↦ g•a` is a bijection (free from L1, surjective from transitivity), so order = degree ("abelian primitive ⟹ regular, hence small"). | — |
| `not_comm_of_isPretransitive_of_stabilizer_ne_bot` | 420-426 | **(seal Step 4, qualitative)** A transitive faithful action with a **non-trivial** point stabilizer (not regular) is **non-abelian** — direct contrapositive of L1. | — |
| `not_comm_of_isPreprimitive_card_lt` | 428-437 | **(seal Step 4 — the headline: large primitive ⟹ non-abelian)** A **preprimitive** faithful action with `Nat.card α < Nat.card G` (group strictly larger than its degree) is **non-abelian**, since a transitive abelian action has order = degree. The order-side proof that a primitive abelian group is `Z_p` (never large); closes the bottom-up route's Step 4 with no citation. | — |
## ChainDescent/Cascade.lean

> **★ SEAL CAPSTONE MAP** (also at the top of the seal section in `Cascade.lean`). 22 public
> `reachesRigidOrCameron_*` capstones remain here (12 superseded ones were archived to
> `PrivateTheoremIndex.md`). **The one to use: `reachesRigidOrCameron_viaBoundedMinMult`**
> (`CascadeAffine.lean`; seal `modulo {G3 + hSmallAutThin + hcatch + hImprim}`, open content =
> `hSmallAutThin` = node 4). Other LIVE endpoints: `…_viaNoCover` (poly node-4 anchor),
> `…_viaSmallAutShatters` (sub-exp citation), `…_viaSpielman` (**the fully-citable Cameron-free sub-exp FLOOR
> — carries only `hSpielman`, no G3/Cameron/hImprim**), `…_viaG0powNeg` (closure discharged), `…_affineSlice`
> (cited 2-sep), `…_viaCompleteBase` / `…_viaRainbowRank` (node-2 rung). Everything else here is a load-bearing
> intermediate of the live proof chain; the 12 superseded capstones now live (full text) in `PrivateTheoremIndex.md`.

B1 (Tier 3a cascade composition) of `docs/chain-descent-tier3-tractable-buildout.md`,
Phases A + C. Build plan: `docs/chain-descent-tier3a-b1-build-plan.md`. The headline
"depths add" theorem, **conditional on the per-layer transfer** (`LayerStep`, = paper
§4.2.5, discharged in the not-yet-built Phase D). Stays on `Fin n` (no quotient
re-typing) by telescoping cumulative individualization sets. Axiom-clean (standard
basis; `refineStep` via `warmRefine`).

### Phase A — interface

| Name | Description | Notes |
|------|-------------|-------|
| `IsBase adj P T` | **Phase A interface.** `T` is a *base* of the `P`-preserving automorphism group: its pointwise stabilizer is trivial, so the `Aut_T`-orbit relation is equality — the chain's bottom `H_k = {1}`. | Definition |
| `LayerStep adj P T S` | **Phase A interface — the per-layer transfer obligation.** `CellsAreOrbits T → CellsAreOrbits (T ∪ S)`: individualizing the increment `S` brings cells down to `Aut_{T∪S}`-orbits (paper §4.2.5 transferred to `G`). The contract the composition induction consumes; discharged in Phase D. | Definition |
| (cascade-class predicate) | `RecoverableByDepth adj P bound` (in `CascadeOracle.lean`) — Tier-1 (`recoverableByDepth_cfi`) / Tier-2 (`recoverableByDepth_scheme`) instances already proved. | (existing) |

### Phase C — composition theorem

| Name | Description | Notes |
|------|-------------|-------|
| `discrete_of_cellsAreOrbits_base` | 70-77 | **(C1) Finish.** At a base `T` where cells already coincide with `Aut_T`-orbits, warm refinement at `T` is `Discrete` — the cascade reaching full canonization. | — |
| `cellsAreOrbits_compose` | 79-92 | **(C2) Composition induction.** From layer 1's unconditional `CellsAreOrbits` at `T 0` and a `LayerStep` at each subsequent layer, `CellsAreOrbits` holds at the final cumulative set `T k`. | — |
| `cumulative_card_le` | 94-100 | **Depths add (cardinality).** The cumulative individualization set `⋃_{i≤k} S i` has size at most `Σ_{i≤k} f i` when each layer is bounded by its depth `f i`. | — |
| `cascadeComposition` | 102-114 | **Theorem 3a (cascade composition) — headline, conditional form.** Cumulative sets with layer-1 recoverability, per-layer transfer steps, and the final set a base ⟹ warm refinement at `T k` reaches the discrete partition; with `cumulative_card_le` the cascade depth is `≤ Σ fᵢ`. Conditional on the `hstep` obligations (= §4.2.5, Phase D). | — |
| `cascadeComposition_single` | 122-125 | **Single-layer sanity check (k = 0).** One cascade-class layer that is a base reaches discreteness — recovers the Tier-1/Tier-2 orbit-recovery theorems as the composition's base case. | — |

### Phase D — discharging `LayerStep` (the §4.2.5 transfer), intrinsic route

Approach B (build-plan §3): stay on `Fin n`, reduce `LayerStep` to a witness-upgrade via
**set-monotonicity** of warm refinement (reusing `refineStep_iff`); the materialized-quotient
route was rejected (`refineStep` axiomatic, no cross-size API).

| Name | Description | Notes |
|------|-------------|-------|
| `Refines χ₁ χ₂` | `χ₁` refines `χ₂`: the partition of `χ₁` is finer (`χ₁ a = χ₁ b → χ₂ a = χ₂ b`). The partition order used for warm-refinement monotonicity. | Definition |
| `signature_refines` | 143-164 | **Crux of warm-refinement monotonicity.** If `χ₁` refines `χ₂`, equal `χ₁`-signatures give equal `χ₂`-signatures, since `signature χ₂` is the coarsening of `signature χ₁`. | — |
| `iterate_refineStep_refines` / `warmRefine_refines_initial` | warm refinement monotone in the initial colouring's partition order. | axiom-light |
| `individualizedColouring_refines` | 190-202 | Individualizing a superset gives a finer initial colouring: `T ⊆ T'` ⟹ `individualizedColouring n T'` refines `individualizedColouring n T`. | — |
| `warmRefine_indiv_mono` | 204-212 | **Set-monotonicity (the payoff).** Same `(T ∪ S)`-cell ⟹ same `T`-cell: 1-WL is monotone in the individualization set. The load-bearing lemma the docs had mis-cited as `warmRefine_refines`. | — |
| `WitnessUpgrade adj P T S` | **The genuine §4.2.5 content.** For `v, w` in the same `Aut_T`-orbit and the same `(T ∪ S)`-cell, the orbit relation upgrades to `Aut_{T∪S}`. The Phase-D interface predicate. | Definition |
| `layerStep_of_witnessUpgrade` | 226-233 | **The reduction — where Phase C meets the per-layer content.** A `WitnessUpgrade` discharges a `LayerStep`, via set-monotonicity then `CellsAreOrbits T` then the upgrade. | — |
| `layerStep_empty` / `layerStep_subset` / `layerStep_of_cellsAreOrbits` / `layerStep_of_discrete` | Trivial real instances: no-op layer (`S = ∅`), `S ⊆ T`, independently-recoverable target, and the discretizing recursion-bottom. | axiom-light |
| `witnessUpgrade_of_pathFixing` | 258-273 | **Bridge to harvested generators.** If every same-orbit, same-cell pair admits a `P`-preserving automorphism whose support avoids `T ∪ S` (fixes the committed path) and sends `v ↦ w`, the witness-upgrade holds — exactly what the cascade/linear oracles produce. | — |

### Step 5 — the synthesis (Theorem 3a reduced to harvested generators)

| Name | Description | Notes |
|------|-------------|-------|
| `cascadeComposition_pathFixing` | 292-313 | **Theorem 3a, reduced to harvested path-fixing generators.** Cumulative sets by increments, layer-1 recoverable, every layer's residual symmetry realized by path-fixing automorphisms (`hwit`), and the final set a base ⟹ discrete warm refinement at `T k`. Reduces all of Theorem 3a to the single hypothesis of per-layer path-fixing witness existence. | — |
| `cascadeComposition_twoLayer` | 315-330 | **Smallest genuine composition.** An outer cascade-class layer at `T₀`, an inner path-fixing layer with increment `S`, and the union a base ⟹ discreteness — the `CFI(scheme)` / `Scheme(CFI)` shape. | — |

**Phase 6b — CFI gadget flips discharge the Tier-3a `hwit`.** The Stage-3 gadget flip (`CFI.lean §15`)
discharges `cascadeComposition_pathFixing`'s `hwit` for a CFI layering, conditional only on the per-layer
existence of committed-set-avoiding gadget flips (the cascade-1b content).

| Name | Description | Notes |
|------|-------------|-------|
| `CFILayerGadgetFlippable` | 341-352 | Per-layer CFI gadget-flip existence: for each layer and same-orbit/same-cell pair `(v,w)`, an even-symmetric cycle `F` whose flip maps `v ↦ w` with `T i ∪ S i` in `F`-free gadgets. The `hwit` analog of the linear oracle's `CFIGadgetFlippableLocal`. | Definition |
| `cfiLayer_pathFixing_hwit` | 354-368 | **The `hwit` drop-in.** `CFILayerGadgetFlippable` (+ `P` Aut-invariant) ⟹ the Tier-3a `hwit` hypothesis, directly via `cfiFlipAut_pathFixing_witness`. | — |
| `cascadeComposition_cfi` | 370-382 | **Theorem 3a for CFI layers.** A CFI layering whose residual orbit maps are realised by committed-set-avoiding gadget flips reaches the discrete partition — `cascadeComposition_pathFixing` with `hwit` discharged by the Stage-3 flips (conditional only on the cascade-1b cycle existence). | — |
| `recoverableByDepth_of_pathFixing_layers` | 400-418 | **The harvest-window connector.** Lands `cascadeComposition_pathFixing`'s `Discrete` output onto the harvest `RecoverableByDepth` conclusion: a layer chain with per-layer path-fixing `hwit` and a base endpoint gives `RecoverableByDepth adj P b` at the chain-length bound. | — |
| `recoverableByDepth_of_cascadeComposition_cfi` | 420-433 | **CFI corollary of the connector.** `RecoverableByDepth` for a CFI layering via `cascadeComposition_cfi` — the connector with `hwit` discharged by the Stage-3 gadget flips. | — |
| `ResidualAut` | 448-454 | **Residual automorphism.** A `P`-preserving automorphism of `adj` fixing `S` pointwise — an element of the residual group `Aut_S^P`; the building block of the screen predicates. `OrbitPartition adj P S v w ↔ ∃ π, ResidualAut π ∧ π v = w`. | Definition |
| `ResidualAbelian` | 456-461 | **D2 — abelian residual.** The residual group `Aut_S^P` is abelian (any two residual automorphisms commute) — the screen's hidden-abelian / linear leg (calculator §6); the `¬IsBase`-guarded form is the D2 disjunct. | Definition |
| `orbitPartition_iff_residualAut` | 463-469 | `OrbitPartition adj P S v w` unfolds to a `ResidualAut` carrying `v ↦ w`. | — |
| `ResidualInvolutive` | 499-505 | **D2, the exponent-2 form.** Every residual automorphism is an involution — `Aut_S^P` has exponent ≤ 2 (an elementary-abelian `Z₂^d`, CFI's gauge group). The precise form of D2 the swap content needs; strictly stronger than `ResidualAbelian`. | Definition |
| `residualAbelian_of_involutive` | 507-516 | **Exponent-2 ⟹ abelian.** A residual group of involutions commutes — wiring the abstract `ResidualAbelian` predicate to the precise `ResidualInvolutive`. | — |
| `orbitPartition_swap_of_involutive` | 518-531 | **An involutive orbit witness is a swap.** With an exponent-2 residual, an `Aut_S`-orbit pair `a, b` has a residual automorphism with `g a = b` *and* `g b = a` — closing the map-vs-swap gap class-agnostically (the content the CFI route obtains from gadget involutions). | — |
| `swap_of_cellsAreOrbits_involutive` | 533-543 | **The class-agnostic swap certificate at a recoverable node.** Where orbit recovery holds (`CellsAreOrbits`) and the residual is exponent-2, every same-cell decision pair carries a swapping orbit automorphism — the linear oracle's 'a swap exists' input from recovery + D2, replacing the per-class `CFIGadgetFlippable` derivation. | — |
| `residualAut_eq_one_of_isBase` | 545-552 | Under a base (`IsBase`), every residual automorphism is the identity — it can move no point. | — |
| `residualAbelian_of_isBase` | 554-559 | **Trichotomy base case.** A trivial residual (under `IsBase`) is vacuously abelian, so `ResidualAbelian` holds at any base. | — |
| `residualAbelian_mono` | 561-568 | **D2 inherited down the descent.** `ResidualAbelian` passes from `S` to any `S' ⊇ S` (the residual shrinks to a subgroup of an abelian group). | — |
| `StabilizerAt` | 580-603 | **Part A (A1) — the residual group `Aut_S^P` as a `Subgroup`.** Carrier the `P`-preserving automorphisms fixing `S` pointwise (`ResidualAut`); closure via `ResidualAut.mul`. The group object underlying the stabilizer chain. | Definition |
| `mem_stabilizerAt` | 605-606 | Membership: `π ∈ StabilizerAt adj P S ↔ ResidualAut adj P S π` (`Iff.rfl`). | `@[simp]` |
| `stabilizerAt_smul` | 608-610 | The subgroup action is permutation application: `g • v = ↑g v`. | `@[simp]` |
| `mem_stabilizerAt_empty` | 612-618 | **Root = ambient `P`-preserving group.** `StabilizerAt adj P ∅` is exactly the `P`-preserving automorphisms (`FixesPointwise ∅` vacuous). | — |
| `stabilizerAt_mono` | 620-626 | **Stabilizer containment.** `S ⊆ S' → StabilizerAt adj P S' ≤ StabilizerAt adj P S` (fixing more gives a smaller group; subgroup form of `OrbitPartition.mono`). | — |
| `stabilizerAt_eq_bot_iff_isBase` | 628-642 | **`StabilizerAt = ⊥ ⟺ base.** The residual is trivial exactly when `S` is a base (`IsBase`). | **`StabilizerAt = ⊥ ⟺ base.** The residual is trivial exactly when `S` is a base (`IsBase`). | — |
| `mem_orbit_stabilizerAt_iff` | 644-655 | **Per-node orbit bridge.** `MulAction.orbit (StabilizerAt adj P S) v` is exactly the `OrbitPartition` relation at `S` (generalizes Group.lean's root bridge off `S = ∅`). | — |
| `residualAut_mem_stabilizerAt` | 677-680 | **(A2) Fold-in entry.** A verified `P`-preserving path-fixing automorphism is a member of `StabilizerAt adj P S`. | — |
| `closure_le_stabilizerAt` | 682-689 | **(A2) The harvested chain stays inside the true residual.** If every harvested generator is a verified path-fixing automorphism, `Subgroup.closure gens ≤ StabilizerAt adj P S` — the over-split-sound contract, group side. | — |
| `orbit_pathFixing_sound` | 691-700 | **(A2) Consumption soundness.** For `H ≤ StabilizerAt adj P S`, `v ∈ orbit H w ⟹ OrbitPartition adj P S w v` — pruning via the chain's orbits is sound. | — |
| `covered_sound` | 702-710 | **(A2) Covered ⟹ sound prune (capstone).** A candidate in the orbit (under verified path-fixing harvested gens) of an explored rep is genuinely `Aut_S^P`-equivalent to it — `CoveredByPathFixingAut` soundness. | — |
| `card_stabilizerAt_pos` | 729-731 | **(A3)** The residual group is finite, so `0 < Nat.card (StabilizerAt adj P S)`. | — |
| `card_stabilizerAt_eq_one_iff_isBase` | 733-738 | **(A3) The rigid verdict.** `Nat.card (StabilizerAt adj P S) = 1 ↔ IsBase adj P S` — residual trivial ⟺ rigid; its negation is the non-rigid/Tier-2-like side (the C# `Tier2Like`/`IrBlindSpot` flag diagnostic). | — |
| `exists_orbitPartition_of_not_isBase` | 751-758 | **RRU progress (brick 1).** Not-a-base ⟹ some ordered pair `v ≠ w` lies in one `Aut_T`-orbit — a consumable symmetry. First brick of the RRU phase-transfer. | — |
| `exists_nontrivial_residualAut_of_not_isBase` | 760-769 | **RRU progress — generator form.** Not-a-base ⟹ a nontrivial residual automorphism exists (fixes `T`, moves some point) — the generator the cross-branch harvest consumes. | — |
| `one_lt_card_stabilizerAt_of_not_isBase` | 771-779 | **RRU progress — cardinality form.** Not-a-base ⟺ the residual group is nontrivial (`1 < Nat.card (StabilizerAt …)`); the bridge to the flag/cost side (`spineResidualCard`). | — |
| `exists_warmRefine_cell_pair_of_not_isBase` | 781-790 | **RRU progress — same-cell form.** The moved pair shares a 1-WL cell — a non-singleton cell the descent's selector can target and the oracle consume. | — |
| `subgroupOf_insert_eq_stabilizer` | 792-805 | **(A3) Chain carrier match.** Inside `Aut_S^P`, the point-stabilizer of `b` is exactly `Aut_{insert b S}^P`. | — |
| `card_stabilizer_eq` | 807-814 | **(A3)** The point-stabilizer inside `Aut_S^P` has the same order as `Aut_{insert b S}^P` (via `subgroupOfEquivOfLe`). | — |
| `card_stabilizerAt_eq_orbit_mul` | 816-825 | **(A3) The order recursion.** `|Aut_S^P| = |orbit of b| · |Aut_{insert b S}^P|` — the inductive step of `order = ∏ basic-orbit sizes`, via `Subgroup.card_mul_index` + `index_stabilizer`. | — |
| `orbitSizeProd` | 836-842 | **(A3.5)** The basic-orbit-size product along an ordered base sequence `bs` from `S`: each `b` contributes `|orbit b under Aut_S^P|`, then the residual descends to `Aut_{insert b S}^P`. The right-hand side of `order = ∏ basic-orbit sizes`. | Definition, `noncomputable` |
| `card_stabilizerAt_eq_prod` | 844-856 | **(A3.5) The telescoping order identity.** For any sequence `bs`, `|Aut_S^P| = orbitSizeProd bs S · |Aut_(accumulated)^P|` — induction on `bs` over `card_stabilizerAt_eq_orbit_mul`; no computable BSGS. | — |
| `card_stabilizerAt_eq_prod_of_base` | 858-865 | **(A3.5) `order = ∏ basic-orbit sizes` at a base.** When `bs.foldl … S` is a base the trailing residual is trivial, so `|Aut_S^P|` is exactly the orbit-size product — the abstract `Order = ∏ OrbitSize` of `PermutationGroup.cs`, no computable BSGS. | — |
| `card_autP_eq_prod_of_base` | 867-874 | **(A3.5) `Aut(G)^P` order as a byproduct.** The `S = ∅` headline: `StabilizerAt adj P ∅` is the whole `P`-preserving Aut group, so a base sequence from `∅` reads off `|Aut(G)^P|` as the orbit-size product (strategy §6, the chain). | — |
| `exists_greedy_base_aux` | 886-941 | **(A3.6 — greedy-base existence, strong-induction core; step 2.1)** For every bound `N` on `|Aut_S^P|`, a base sequence `bs` from `S` with `2 ^ bs.length ≤ |Aut_S^P|`. Greedy: while `¬IsBase`, a residual aut moves a point `b` whose basic orbit is `≥ 2`, so inserting `b` strictly shrinks the residual order (`card_stabilizerAt_eq_orbit_mul`) and each layer doubles the lower bound. Axiom-clean. | — |
| `exists_greedy_base` | 943-950 | **(A3.6 — `2 ^ |base| ≤ |Aut(G)^P|`)** The `S = ∅` headline of `exists_greedy_base_aux`: a base sequence from `∅` whose length is logarithmic in the residual order. Axiom-clean. | — |
| `exists_greedy_base_le_log` | 952-960 | **(A3.6 — `base(G) ≤ log₂|Aut(G)^P|`, the conservation budget's base term banked; step 2.1)** The greedy base length is `≤ Nat.log 2 |Aut(G)^P|`; for a small (poly-order) residual this is `O(log n)`, so the seal's `bound` is `O(log n) + s(C)` with only the `s(C)` stickiness left open. Axiom-clean. | — |
| `gensAt` | 982-987 | **(A2-complete) Path-fixing generators at `S`.** The subset `{g ∈ gens | g ∈ StabilizerAt adj P S}` — generators fixing the committed path. Strong-generation realizes each level's orbit from *these*, not the full `closure gens` (the distinction that makes the witness non-circular). | Definition |
| `gensAt_anti` | 989-993 | **(A2-complete)** Path-fixing generators shrink as the path grows: `S ⊆ S' → gensAt … S' ⊆ gensAt … S` (via `stabilizerAt_mono`). | — |
| `closure_gensAt_le_stabilizerAt` | 995-998 | **(A2-complete)** Soundness, intrinsic to `gensAt`: `Subgroup.closure (gensAt adj P gens S) ≤ StabilizerAt adj P S`. | — |
| `closure_gensAt_anti` | 1000-1004 | **(A2-complete)** Monotonicity of the path-fixing closure: `S ⊆ S' → closure (gensAt … S') ≤ closure (gensAt … S)` — the step that makes the completeness induction descend the base. | — |
| `gensAt_empty_eq` | 1006-1010 | **(A2-complete)** At the empty path the path-fixing condition is vacuous: `gensAt adj P gens ∅ = gens` once every generator is a `P`-preserving automorphism. | — |
| `stabilizerAt_le_closure_gensAt_step` | 1012-1042 | **(A2-complete) The one-level completeness core (strong-generation step).** If the path-fixing closure at the next level contains `StabilizerAt (insert b S)` and the path-fixing closure at `S` realizes the full `Aut_S^P`-orbit of `b`, then it contains `StabilizerAt adj P S`. The dual of `closure_le_stabilizerAt`; the `closure_gensAt_anti` descent is where the path-fixing form is essential. | — |
| `CoversOrbits` | 1044-1056 | **(A2-complete) The harvest's strong-generating-set witness.** Recursive over a base sequence: at each head the *path-fixing* closure `closure (gensAt … S)` realizes the current residual orbit of the base point, recursing to a base at the tail. Genuinely stronger than "`gens` generate the top group" (non-circular); the honest analog of the within-cell depth witness, supplied by the per-level path-fixing harvest. | Definition |
| `coversOrbits_realize_of_mem` | 1058-1067 | **(A2-complete) Coverage step from path-fixing realizers (the harvest interface).** If the path-fixing *generators* `gensAt … S` themselves realize `b`'s orbit, the coverage clause holds (via `Subgroup.subset_closure`). The hook concrete gauge-generator work (CFI/schemes) plugs into. | — |
| `coversOrbits_isBase_foldl` | 1069-1075 | **(A2-complete)** The terminal accumulated set `bs.foldl insert S` of a coverage witness is a base (matches A3.5's `foldl`). | — |
| `stabilizerAt_le_closure_gensAt_of_coversOrbits` | 1077-1085 | **(A2-complete) Harvest completeness (`≤`).** A coverage witness gives `StabilizerAt adj P S ≤ Subgroup.closure (gensAt adj P gens S)` — iterates `stabilizerAt_le_closure_gensAt_step` down the base. The dual of `closure_le_stabilizerAt`. | — |
| `stabilizerAt_eq_closure_gensAt_of_coversOrbits` | 1087-1093 | **(A2-complete) Harvest completeness (equality).** Soundness (`closure_gensAt_le_stabilizerAt`) + coverage give `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` — the path-fixing closure is *exactly* the residual. No separate soundness hypothesis. | — |
| `CoversOrbitsAlong` | 1095-1107 | **(Partial coverage along a base-sequence segment — no terminal base)** The per-head orbit-coverage clauses of `CoversOrbits` for a segment `bs` from `S`, *without* requiring the accumulated set to be a base. Lets a base sequence be split into phases (`coversOrbits_append`): the structural tool for ordering the descent — block representatives first (quotient phase = partial coverage), then within-block points (fiber phase = full tail) — that the Route B imprimitive decomposition needs. | Definition |
| `coversOrbitsAlong_of_coversOrbits` | 1109-1115 | **(Weakening: full coverage ⟹ partial coverage)** A `CoversOrbits` witness yields `CoversOrbitsAlong` along its sequence — forget the terminal base. Induction on `bs`. | — |
| `coversOrbits_append` | 1117-1129 | **(Base-sequence phase split)** Partial coverage along `bs₁` from `S` (`CoversOrbitsAlong`) + a full `CoversOrbits` witness for `bs₂` from the accumulated set `bs₁.foldl insert S` glue to `CoversOrbits (bs₁ ++ bs₂) S`. The freedom to resolve one descent phase (quotient / block reps) before another (fibers / within-block), each phase's coverage supplied by a different smaller/coarser constituent's recovery — the Route B Approach-A enabler. Induction on `bs₁`. | — |
| `closure_eq_stabilizerAt_empty_of_coversOrbits` | 1131-1140 | **(A2-complete) Completeness at the root — the harvested chain *is* `Aut(G)^P`.** At `S = ∅`, coverage + soundness give `Subgroup.closure gens = StabilizerAt adj P ∅`. Closes the cross-branch harvest the way A2 closed soundness. | — |
| `card_closure_gensAt_eq_prod_of_coversOrbits` | 1142-1150 | **(A2-complete) Capstone — the chain reproduces the residual order.** With A3.5, coverage gives `Nat.card (Subgroup.closure (gensAt adj P gens S)) = orbitSizeProd adj P bs S` (= `∏ basic-orbit sizes`): the folded path-fixing generators recover both the residual group and its order. | — |
| `residualInvolutive_mono` | 1174-1180 | **(A2-complete, de-classed) `ResidualInvolutive` inherited down the descent.** `ResidualInvolutive S → S ⊆ S' → ResidualInvolutive S'` — a subgroup of an exponent-2 group has exponent ≤ 2; the involutive analogue of `residualAbelian_mono`, letting the de-classed coverage carry its hypothesis down the base sequence. | — |
| `coversOrbits_of_realizers` | 1182-1207 | **(A2-complete, de-classed — general/non-abelian) `CoversOrbits` from per-level path-fixing realizers.** If at every level `T ⊇ S` the harvested `gens` contains a residual-at-`T` realizer for each orbit-mate of each base point (`g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w`), and `bs` ends at a base, then `CoversOrbits adj P gens bs S`. **No group-structure hypothesis** — abelian *or* non-abelian (schemes, Cameron) — the honest "covers everything, no class ladder" coverage core; `coversOrbits_of_residualInvolutive` is its exponent-2 corollary. | — |
| `coversOrbits_of_realizers_symmetric` | 1209-1232 | **(Budget-split coverage builder.)** `CoversOrbits` from orbit realizers required **only at non-base prefixes** (`¬IsBase T`) — at a base prefix the per-head clause is free (orbits singletons, `1 ∈ closure`). Lets the group be reproduced from the symmetry phase alone, no IR-core. Axiom-clean. | — |
| `coversOrbits_of_visibleRealizers_symmetric` | 1234-1247 | Visible (`warmRefine`-cell) form of the budget-split builder — coverage from same-cell realizers at non-base prefixes only (what `RecoversWhileSymmetric` supplies). Axiom-clean. | — |
| `coversOrbits_of_visibleRealizers` | 1249-1266 | **(A2-complete, de-classed — harvest-facing) `CoversOrbits` from realizers keyed on the refinement-visible cell relation.** Same as `coversOrbits_of_realizers` but the realizer hypothesis ranges over same-`warmRefine`-cell pairs (polynomially computable) rather than `OrbitPartition` pairs (orbits refine cells, so it covers a fortiori). The shape the structural (scheme/recovery) harvest supplies: at a recoverable node cells *are* orbits, so visible cell-mates = orbit-mates. | — |
| `closure_eq_stabilizerAt_of_realizers` | 1268-1280 | **(A2-complete, de-classed — general) Harvest completeness from realizers.** `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` from per-level path-fixing realizers (`coversOrbits_of_realizers` + `stabilizerAt_eq_closure_gensAt_of_coversOrbits`). The general (non-exponent-2) analogue of `closure_eq_stabilizerAt_of_residualInvolutive`: the cross-branch harvest reproduces the residual group (and order, via A3.5) for the whole recoverable class, no group-structure hypothesis. | — |
| `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` | 1282-1300 | **(A2-complete, localisation core) Recovery makes the harvest refinement-decidable.** At a node `T` with `CellsAreOrbits`, the refinement-visible realizer hypothesis (same-`warmRefine`-cell pairs, computable) is *equivalent* to the orbit realizer hypothesis (`OrbitPartition` pairs). `→` free (`subset_warmRefine`), `←` uses recovery. Pins localisation as the **polynomiality layer**: coverage correctness holds from orbit realizers unconditionally (`coversOrbits_of_realizers`); recovery makes the equivalent target refinement-computable. Per-level recovery down the base sequence is the substrate-conditional remainder. | — |
| `closure_eq_stabilizerAt_of_visibleRealizers` | 1302-1317 | **(A2-complete, polynomiality capstone — group side, computable interface)** `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` from per-level path-fixing realizers keyed on **same-`warmRefine`-cell** pairs (refinement-computable), not `OrbitPartition` pairs. The honest harvest interface: `coversOrbits_of_visibleRealizers` + the A2-complete equality. Visible-realizer hypothesis satisfiable exactly on the recoverable class (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`). | — |
| `crossBranchHarvest_reproduces_residual` | 1319-1339 | **(A2-complete, the general polynomiality capstone)** From per-level path-fixing **visible** (cell) realizers + a terminal base, **both** `closure (gensAt adj P gens S) = StabilizerAt adj P S` **and** the order `Nat.card … = orbitSizeProd adj P bs S` (= `∏ basic-orbit sizes`). The polynomiality-layer analogue of `exhaustiveObstruction_scheme`: single substrate-conditional input = **recovery** (makes the visible-realizer hypothesis satisfiable); coverage→group→order chain unconditional, axiom-clean. Witnesses: `recoverableByDepth_pPolynomial` (metric/DRG), `recoverableByDepth_cfi` (CFI). | — |
| `autP_reproduced_of_visibleRealizers` | 1341-1358 | **(A2-complete, capstone root headline)** The `S = ∅` case (via `gensAt_empty_eq`): on the recoverable class the folded harvested generators generate **exactly** `Aut(G)^P` and `Nat.card (closure gens) = orbitSizeProd adj P bs ∅` — `Order = ∏ OrbitSize` computed end-to-end from the visible (cell) harvest, no group-structure hypothesis (abelian or non-abelian). | — |
| `orbitCoverage_of_blockDecomposition` | 1378-1398 | **(Route B Phase 1 core — swap decomposition of orbit coverage)** The closure-based coverage of base point `b`'s full residual orbit factors, along a partition `β` (block system), into **block-reach** `hreach` (closure sends `b` into every orbit-mate's block) + **within-block coverage** `hfiber` (closure realizes same-block orbit pairs). Realizer = composite `h * σ` (block-swap then fiber move) in the closure subgroup — handles the Aut-**permuted** (block-swapping) imprimitive case `noFusion_of_warmSeparatedPartition` cannot. Works because `CoversOrbits` keys on `closure (gensAt …)` (composition-closed), not single gens. | — |
| `coversOrbits_cons_of_blockDecomposition` | 1400-1412 | **(Route B Phase 1 wiring — `CoversOrbits` step from the block decomposition)** Assembles one `CoversOrbits (b :: bs) S` level: head clause from `orbitCoverage_of_blockDecomposition` (block-reach + within-block coverage at `b`), tail from the recursion on `insert b S`. The recursion-ready interface the Phase-2 size-induction iterates down the base sequence; `hreach`/`hfiber` discharged by quotient/fiber recovery (smaller, schurian by the §11.1 gate). | — |
| `coversOrbits_of_blockDecomposition` | 1414-1433 | **(Route B Phase 2 — assemble coverage from per-level block decomposition)** Iterating `coversOrbits_cons_of_blockDecomposition` down a base sequence: per-level block-reach (`hreach`, quotient) + within-block coverage (`hfiber`, fiber) + terminal base ⟹ `CoversOrbits adj P gens bs S`. Induction on `bs`, entirely on `Fin n` — `hreach`/`hfiber` are block-restricted quantifiers over the original vertex set, so **no sub-scheme is materialized** (the rejected quotient-`AdjMatrix` route is sidestepped; the recursion lives in the coverage predicate, not in new types). | — |
| `reachesRigid_of_blockDecomposition` | 1435-1452 | **(Route B Phase 2 — `ReachesRigid` from the block decomposition; the chain completed)** Per-level block-reach + within-block coverage + base ⟹ `closure (gensAt … S) = StabilizerAt adj P S` (the harvest reproduces `Aut_S` = ReachesRigid). The imprimitive residual's group is reproduced from quotient (block-reach) + fiber (within-block) coverage, each on the smaller constituent (transitive/schurian by the §11.1 gate), **no sub-scheme materialized**. Completes Route B's mechanical chain (gate → swap decomposition → assembly); remaining open content = discharging `hreach`/`hfiber` from constituent recovery (depth-graded block-visibility, the carried frontier). | — |
| `mem_closure_gensAt_of_realizer` | 1474-1479 | **(Route B supplier helper)** A harvested residual automorphism (`g ∈ gens`, `ResidualAut adj P T g`) lies in the path-fixing closure `Subgroup.closure (gensAt adj P gens T)` — the shared membership step of the `hreach`/`hfiber` suppliers. Via `Subgroup.subset_closure` + `mem_stabilizerAt.mpr`. | — |
| `hreach_of_quotientRealizers` | 1481-1494 | **(Route B `hreach` supplier — the weaker quotient interface)** Discharges the block-reach interface `hreach` from **quotient realizers**: residual auts in `gens` landing `b` in the *block* of every orbit-mate `w` (`β (σ b) = β w`, not `σ b = w`). Recovery of the coarser action on blocks only — strictly weaker than full orbit recovery, and the part of Route B that survives when the whole residual does not recover. Class-agnostic (any `β`, any `adj`/`P`). | — |
| `hfiber_of_fiberRealizers` | 1496-1508 | **(Route B `hfiber` supplier — the smaller fiber interface)** Discharges the within-block interface `hfiber` from **fiber realizers**: residual auts in `gens` exactly realizing every *same-block* orbit pair (`β u = β w → h u = w`). Recovery of the smaller within-block (`|B| < n`) action only — the second constituent of the imprimitive decomposition. Class-agnostic. | — |
| `hfiber_of_fiberVisibleRealizers` | 1510-1530 | **(Route B fiber half — `hfiber` from within-block visible realizers, Approach A)** Refinement-computable form of `hfiber_of_fiberRealizers`: the harvest need only realize same-`warmRefine`-cell pairs *within a block* (`β u = β w`), and `hfiber` follows (orbits refine cells, `OrbitPartition.subset_warmRefine`). **Strictly weaker than whole-graph recovery** — satisfiable exactly when *within each block* cells = orbits (the fiber recovers), even when globally cells ⊋ orbits (e.g. Shrikhande, whose 1-WL merges happen across blocks). The fiber half of the per-level quotient/fiber split; the quotient half (`hreach` from block-orbit recovery) needs a block-level 1-WL (next step). | — |
| `hreach_of_quotientVisibleRealizers` | 1532-1556 | **(Route B quotient half from VISIBLE realizers — the G2-A 'next step'.)** Supplies `hreach` from a visible block-move hypothesis (same `warmRefine{T}` cell ⟹ a `gens`-realizer landing `b` in `w`'s **block**). The content is cross-block same-cell pairs = recovery of the coarser **block action** (block-level 1-WL); discharges the shallow-phase (quotient) coverage for the imprimitive case. Quotient analogue of `hfiber_of_fiberVisibleRealizers`. | — |
| `reachesRigid_of_blockVisibleDecomposition` | 1558-1584 | **(imprimitive recovery from a refinement-computable block decomposition.)** Combines the visible quotient (`hreach_of_quotientVisibleRealizers`) and fiber (`hfiber_of_fiberVisibleRealizers`) halves to reproduce `closure (gensAt … S) = StabilizerAt adj P S`, no sub-scheme materialized. Carried content = the two visible hypotheses `hqvis`/`hfvis` (whether the quotient + fiber recover) — the substrate-conditional unit localized to the two smaller constituents. Axiom-clean. | — |
| `blockHarvest_of_realizers` | 1586-1603 | **(Route B subsumption / non-vacuity floor)** Full orbit realizers (`g b = w` for every orbit pair) supply **both** `hreach` and `hfiber`, for **any** `β` (left unused — an exact realizer is a fortiori block-accurate and within-block-exact). So any whole-residual-recoverable class satisfies the Route B interfaces; the decomposition's independent value is strictly the regime where quotient/fiber recover but the whole does not. Built from `hreach_of_quotientRealizers` + `hfiber_of_fiberRealizers`. | — |
| `blockHarvest_of_visibleRecovery` | 1605-1624 | **(Route B witness supplier — recovery + visible realizers ⟹ both interfaces)** The refinement-computable form: `CellsAreOrbits` recovery at every level + a path-fixing realizer for every visible cell-mate supply both `hreach` and `hfiber` (any `β`), via `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` + `blockHarvest_of_realizers`. The Route B analogue of `noFusion_of_visibleRecovery`: the metric/DRG (`recoverableByDepth_pPolynomial`) and CFI (`recoverableByDepth_cfi`) recovery witnesses plug straight in to discharge the imprimitive branch on the whole recoverable class. | — |
| `coversOrbits_of_residualInvolutive` | 1626-1644 | **(A2-complete) De-classed coverage — `CoversOrbits` from an exponent-2 residual.** If the residual is involutive (`ResidualInvolutive`) and `gens` contains every involutive residual automorphism (what the leaf-collision harvest supplies), `CoversOrbits adj P gens bs S` holds. **Now a corollary of `coversOrbits_of_realizers`** (the general non-abelian form): `orbitPartition_swap_of_involutive` supplies the involution realizer for each orbit-mate. Discharges the coverage witness for the whole elementary-abelian-residual class in one theorem — no per-class `Aut(CFI)≅Z₂^β⋊Aut(H)` structure theorem. | — |
| `closure_eq_stabilizerAt_of_residualInvolutive` | 1646-1660 | **(A2-complete) De-classed harvest completeness — the involutive residual *is* the closure of harvested involutions.** At an exponent-2 node, `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` (via `coversOrbits_of_residualInvolutive` + `stabilizerAt_eq_closure_gensAt_of_coversOrbits`). The cross-branch completeness for every elementary-abelian-residual class with no per-class structure theorem — the cross-branch analogue of `theorem_2_HOR_of_pPolynomial`; CFI's gauge regime is a witness supplying only `ResidualInvolutive` at a gauge-regime `S`. | — |
| `cfiFlipAut_residualAut` | 1676-1687 | **(A2-complete / CFI-cov.1) Gauge flip is a path-fixing residual aut.** A symmetric, even gauge flip `cfiFlipAut F` that is `F`-free on `S`'s gadgets is a `ResidualAut adj P S` (assembles `isAut_cfiFlipAut` + `cfiFlipAut_preserves_P` + locality). The bridge from the `CFI.lean` gauge-flip layer to the A2-complete residual vocabulary. | — |
| `cfiFlipAut_mem_stabilizerAt` | 1689-1695 | **(CFI-cov.1)** A path-fixing gauge flip is an element of the residual group `StabilizerAt adj P S`. | — |
| `cfiFlipAut_orbitPartition` | 1697-1705 | **(CFI-cov.1) Forward coverage.** A path-fixing gauge flip moves `v` within its `Aut_S^P`-orbit: `OrbitPartition adj P S v (cfiFlipAut F v)`. (Reverse — realizing the *full* orbit — is the staged cycle-space content.) | — |
| `cfiGaugeGens` | 1707-1713 | **(CFI-cov.1) The CFI gauge generating set.** All symmetric, even gauge flips `cfiFlipAut F` — the cycle-space `Z₂^β` generators the harvest folds in; `Subgroup.closure (cfiGaugeGens h)` is the gauge group. | Definition |
| `cfiGaugeGens_residualAut_empty` | 1715-1722 | **(CFI-cov.1) Root soundness.** Every gauge flip is a `P`-preserving automorphism (`ResidualAut adj P ∅`) — the Stage-A2 soundness hypothesis `closure_eq_stabilizerAt_empty_of_coversOrbits` consumes. | — |
| `cfiFlipAut_mem_gensAt` | 1724-1732 | **(CFI-cov.1)** A path-fixing gauge flip lies in the path-fixing generators `gensAt adj P (cfiGaugeGens h) S` — gauge generator + member of `StabilizerAt adj P S`. The hook the coverage discharge (CFI-cov.3) uses to realize orbits. | — |
| `isBase_of_discrete_warmRefine` | 1741-1747 | **(CFI-cov.2) Discreteness ⟹ base.** If `warmRefine adj P (individualizedColouring n S)` is discrete then `S` is a base — the orbit partition collapses to equality (`orbit_iff_eq_of_discrete_warmRefine`). The general bridge from cascade `Discrete` output to the `IsBase` terminal of `CoversOrbits`. | — |
| `foldl_insert_eq_union` | 1749-1755 | **(CFI-cov.2)** Folding `insert` over a list from `s` accumulates its elements: `l.foldl (insert) s = s ∪ l.toFinset`. | — |
| `foldl_insert_empty_eq_toFinset` | 1757-1760 | **(CFI-cov.2)** Folding `insert` over a list from `∅` rebuilds its underlying finset (`= l.toFinset`) — matches `CoversOrbits`/A3.5's `foldl`. | — |
| `cfi_exists_base_seq` | 1762-1771 | **(CFI-cov.2) CFI base sequence (odd-degree).** From the axiom-free cascade discreteness (`theorem_1_HOR_cfi_oddDeg`), an odd-degree CFI graph has an ordered base sequence `bs` with `bs.foldl insert ∅` a base — the `IsBase` terminal a `CoversOrbits` witness for CFI requires. | — |
| `gaugeSubgroup` | 1789-1813 | **(CFI-cov.3, de-classed) The CFI gauge group `Z₂^β` as a `Subgroup`.** `cfiGaugeGens h` is closed under the group ops (`cfiFlipAut_xorF` for `*`, `cfiFlipAut_one` for `1`, `cfiFlipAut_involutive` for inverses), so it forms a subgroup, not merely a generating set. | Definition |
| `mem_gaugeSubgroup` | 1815-1816 | **(CFI-cov.3)** Membership in `gaugeSubgroup h` is exactly membership in `cfiGaugeGens h` (`Iff.rfl`). | `@[simp]` |
| `closure_cfiGaugeGens_eq` | 1818-1822 | **(CFI-cov.3)** The closure of the gauge generators *is* the gauge subgroup — they already form a subgroup: `Subgroup.closure (cfiGaugeGens h) = gaugeSubgroup h`. | — |
| `cfiGauge_mul_self` | 1824-1831 | **(CFI-cov.3) The gauge group is exponent-2 (elementary-abelian).** Every gauge generator is a flip `cfiFlipAut F` and flips are involutions (`cfiFlipAut_involutive`), so `g * g = 1` — the exponent-2 input `coversOrbits_of_residualInvolutive` needs, supplied for the gauge group. | — |
| `cfi_coversOrbits` | 1833-1852 | **(CFI-cov.3) The CFI coverage witness, via de-classing (no structure theorem).** From **gauge-generation** `StabilizerAt adj P ∅ ≤ closure (cfiGaugeGens h)` (`hgen`) and odd degree, the gauge flips cover every level's residual orbit: `∃ bs, CoversOrbits adj P (cfiGaugeGens h) bs ∅`. Obtained from `coversOrbits_of_residualInvolutive` (gauge-generation ⟹ exponent-2 residual + `hgens`), with **no** `Φ(σ)` lift or semidirect decomposition. The long-sought `cfi_coversOrbits`, reduced to the single `hgen`. | — |
| `cfi_closure_eq_stabilizerAt` | 1854-1865 | **(CFI-cov.3) CFI cross-branch harvest completeness.** With gauge-generation, the harvested gauge chain *is* the residual: `Subgroup.closure (cfiGaugeGens h) = StabilizerAt adj P ∅` (`≤` free via `cfiGaugeGens_residualAut_empty`, `≥` is `hgen`). | — |
| `cfi_card_stabilizerAt_eq_prod` | 1867-1882 | **(CFI-cov.3) `|Aut(CFI(H))^P| = ∏ basic-orbit sizes`, via the gauge chain.** With gauge-generation, `∃ bs, Nat.card (StabilizerAt adj P ∅) = orbitSizeProd adj P bs ∅` — the `Order = ∏ OrbitSize` of `PermutationGroup.cs` for CFI, computed from the folded gauge generators. The genuine de-classed payoff (needs the full `cfi_coversOrbits` chain, not just the two containments). | — |
| `gadgetOf` | 1901-1902 | **(CFI-cov.4)** The gadget (base vertex) of a CFI vertex `x : Fin n`, through the CFI labelling: `h.H.gadget (h.e x) : Fin h.m`. | Definition |
| `CellSeparatesGadgets` | 1904-1914 | **(CFI-cov.4, colour model) `warmRefine` separates gadgets** — the colour-model "base layer resolved" hypothesis (same `warmRefine` cell after individualizing `S` ⟹ same gadget), matching the recovery framework. Dischargeable by the descent's actual mechanism: with the recovery framework's trivial `P`, a `P`-relation form of this hypothesis would be vacuously *false* (no `P`-relation distinguishes anything, and vacuous at `S=∅`); the `warmRefine` colouring does the separating, and the cascade discretizes it at a gadget-resolving `S`. | Definition |
| `gadgetPreserving_of_cellSeparates` | 1916-1929 | **(CFI-cov.4 Lemma A, colour model)** A residual automorphism preserves the `warmRefine` partition of the `S`-individualized colouring (`warmRefine (g x) = warmRefine x`, via `warmRefine_invariant_of_isAut` + `individualizedColouring_invariant`), so under `CellSeparatesGadgets` it fixes every gadget. Lemma A of the gauge-nut discharge, dischargeable by the cascade where a `P`-relation form is not. | — |
| `gadgetOf_subsetVertex` | 1937-1940 | **(CFI-cov.4 Lemma B)** `gadgetOf h (subsetVertex hS@v) = v`. | `@[simp]` |
| `gadgetOf_endpointVertex` | 1942-1945 | **(CFI-cov.4 Lemma B)** `gadgetOf h (endpointVertex hw b@v) = v`. | `@[simp]` |
| `exists_vertex_form` | 1947-1956 | **(CFI-cov.4 Lemma B) Vertex destructor.** Every `x : Fin n` is a subset vertex `subsetVertex hS` or an endpoint vertex `endpointVertex hw b` of the CFI graph (via `h.e x` and the bijection round-trips). | — |
| `endpointVertex_bool_inj` | 1958-1965 | **(CFI-cov.4 Lemma B)** Endpoints at the same gadget/direction are equal only for equal parity: `endpointVertex hw b₁ = endpointVertex hw b₂ → b₁ = b₂`. | — |
| `endpointVertex_inj` | 1967-1975 | **(CFI-cov.4 Lemma B)** Endpoints at gadget `v` are equal only for equal direction and parity: `endpointVertex hw₁ b₁ = endpointVertex hw₂ b₂ → w₁ = w₂ ∧ b₁ = b₂`. | — |
| `subset_mem_iff_adj` | 1977-1989 | **(CFI-cov.4 Lemma B) A subset vertex's membership is its adjacency to the `b=false` endpoints:** `e^0_{v→w} ~ a_S^v ↔ w ∈ S`. Lets `g²` (fixing endpoints) pin a subset vertex. | — |
| `isEndpt` | 1991-1994 | **(CFI-cov.4 Lemma B)** Has a cross-gadget neighbour — the structural distinguisher of endpoint vs subset vertices (`∃ y, adj x y = 1 ∧ gadgetOf y ≠ gadgetOf x`). | Definition |
| `isEndpt_endpointVertex` | 1996-2003 | **(CFI-cov.4 Lemma B)** An endpoint vertex has a cross-gadget neighbour (its bridge partner, in gadget `w ≠ v`). | — |
| `not_isEndpt_subsetVertex` | 2005-2012 | **(CFI-cov.4 Lemma B)** A subset vertex has no cross-gadget neighbour (all neighbours are endpoints at its gadget). | — |
| `isEndpt_equivariant` | 2014-2025 | **(CFI-cov.4 Lemma B)** `isEndpt` is automorphism-invariant for a gadget-fixing automorphism: `isEndpt h (g x) ↔ isEndpt h x` (substitute `y = g z`). | — |
| `gadgetFixingAut_endpoint` | 2027-2042 | **(CFI-cov.4 Lemma B, B1) Type preservation (endpoints).** A gadget-fixing automorphism maps an endpoint vertex to an endpoint vertex at the same gadget. | — |
| `gadgetFixingAut_subset` | 2044-2059 | **(CFI-cov.4 Lemma B, B1) Type preservation (subsets).** A gadget-fixing automorphism maps a subset vertex to a subset vertex at the same gadget. | — |
| `gadgetFixingAut_dir` | 2061-2077 | **(CFI-cov.4 Lemma B, B2) Direction preservation.** A gadget-fixing automorphism maps `e^b_{v→w}` to `e^{b'}_{v→w}` (bridge target `w` preserved); only the parity may change. | — |
| `mulSelf_endpoint` | 2079-2097 | **(CFI-cov.4 Lemma B, B2) `g²` fixes endpoints.** A gadget-fixing automorphism maps the parity pair `{e^0_{v→w}, e^1_{v→w}}` into itself; injective on a 2-set ⟹ squares to identity there. | — |
| `mulSelf_subset` | 2099-2128 | **(CFI-cov.4 Lemma B, B3) `g²` fixes subsets.** `g²` preserves adjacency and fixes endpoints, so a subset vertex and its `g²`-image have identical endpoint-adjacencies; a subset is determined by them, so `g²` fixes it. | — |
| `cfiAut_gadgetFixing_mul_self` | 2130-2141 | **(CFI-cov.4 Lemma B) A gadget-fixing CFI automorphism is an involution.** `IsAut g adj` + gadget-preservation ⟹ `g * g = 1` (every vertex is subset (B3) or endpoint (B2), both fixed by `g²`). The medium-risk core of the gauge-nut discharge. | — |
| `isBase_mono` | 2151-2157 | **(CFI-cov.4 harvest)** `IsBase` is upward-closed: `IsBase adj P S → S ⊆ T → IsBase adj P T` (individualizing more shrinks the residual; via `stabilizerAt_mono`). | — |
| `cfi_exists_base_seq_from` | 2159-2171 | **(CFI-cov.4 harvest) A base sequence from any `S`.** For an odd-degree CFI graph, `(allSeeds \ S).toList` is a base sequence from `S`: the cascade gives `IsBase allSeeds` (`theorem_1_HOR_cfi_oddDeg`) and `isBase_mono` lifts it to the superset. Generalizes `cfi_exists_base_seq` (`S = ∅`). | — |
| `cfi_residualInvolutive_cell` | 2183-2190 | **(CFI-cov.4 capstone, colour model — Lemma A colour + Lemma B)** `ResidualInvolutive adj P S` from `CellSeparatesGadgets`: gadget-preservation (`gadgetPreserving_of_cellSeparates`) + a gadget-fixing CFI aut is an involution (`cfiAut_gadgetFixing_mul_self`, reused verbatim). The **dischargeable** form keyed on the `warmRefine` colouring (a `P`-relation form would be vacuously false on the descent's trivial `P`). | — |
| `cellSeparatesGadgets_of_discrete` | 2192-2199 | **(CFI-cov.4, cascade bridge)** `CellSeparatesGadgets adj P S h` from `warmRefine` **discreteness** (same cell ⟹ same vertex ⟹ same gadget) — the connection from the proven CFI cascade (`theorem_1_HOR_cfi_oddDeg` at `allSeeds`) to the colour-model base-resolved hypothesis. The `P`-relation form had no such bridge. | — |
| `cfi_closure_eq_stabilizerAt_of_cellSeparates` | 2201-2215 | **(CFI-cov.4 harvest, colour model)** Where `warmRefine` separates gadgets at `S`, `Subgroup.closure {g | ResidualAut adj P S g ∧ g²=1} = StabilizerAt adj P S` — the harvested involutive residual auts generate the residual. Dischargeable by the cascade (`cellSeparatesGadgets_of_discrete`). | — |
| `cfi_card_stabilizerAt_of_cellSeparates` | 2217-2227 | **(CFI-cov.4 harvest, colour model)** Where `warmRefine` separates gadgets at `S`, `∃ bs, Nat.card (StabilizerAt adj P S) = orbitSizeProd adj P bs S` — the gauge-layer `Order = ∏ OrbitSize` from the folded involutive generators. | — |
| `gadget_mem_neighbors_of_adj_cross` | 2247-2263 | **(CFI base-graph projection, Brick 1)** A cross-gadget adjacency is a base-graph edge: `adj x y = 1` with `gadgetOf x ≠ gadgetOf y` ⟹ `gadgetOf y ∈ N_H(gadgetOf x)`. The only cross-gadget CFI edges are endpoint bridges (subset vertices have only same-gadget neighbours, `not_isEndpt_subsetVertex`), and bridges connect `H`-adjacent gadgets (`adj_endpointVertex_eq_one_iff`). The structural foundation for discharging `CellSeparatesGadgets` from base-graph identification (gadget-level analogue of `RecoverableByDepth`); the refinement-projection induction (Brick 2) + `Discrete`-`H` conclusion (Brick 3) build on it. | — |
| `endpoint_crossGadget_gadget` | 2265-2279 | **(CFI base-graph projection, Brick 1 sharpened)** A cross-gadget neighbour of `e^b_{v→w}` lands in gadget `w` *exactly* (the bridge target), not merely some `H`-neighbour gadget — each endpoint has a single cross-gadget (bridge) neighbour, in gadget `w`. Pins the projection's multiplicity (cross-gadget neighbourhood distributed over `N_H(gadget)`, one per outgoing endpoint direction). | — |
| `VisiblyRecoverable` | 2302-2318 | **D1 (explicit-chain form).** A single-vertex, per-step symmetry-only chain from `S₀` reaching `CellsAreOrbits` within a depth bound — the unconditional/cascade leg's structural witness, retained alongside the inductive `Findable`. | Definition |
| `recoverableByDepth_of_visiblyRecoverable` | 2320-2325 | **D1 leg (free).** `VisiblyRecoverable ⟹ RecoverableByDepth` — the chain ends on a `CellsAreOrbits` set within the bound. | — |
| `cellsAreOrbits_empty_of_schurian` | 2333-2346 | **Schurian scheme graphs are vertex-transitive: `CellsAreOrbits adj P ∅`.** The `Aut`-orbit relation at `∅` is total (witness from `schurian_transitive` at the diagonal `R₀`), unblocking the symmetry-only first step. | — |
| `visiblyRecoverable_of_cellsAreOrbits_singleton` | 2348-2361 | **`CellsAreOrbits` at a singleton + vertex-transitivity ⟹ D1 at depth 1.** The one-step chain `∅ → {v}` is symmetry-only with `CellsAreOrbits {v}` as endpoint recovery. | — |
| `visiblyRecoverable_scheme` | 2363-2373 | **D1 instance — rank-2, `|J|=1` schurian scheme is visibly recoverable.** Validates `VisiblyRecoverable` against the proved depth-1 scheme orbit recovery (`orbitRecoverable_scheme`). | — |
| `SymmetryOnlyStep` | 2377-2390 | **D1 per-decision primitive (§6.10).** Individualizing `v` commits no real decision: `v`'s 1-WL cell is non-singleton and a single `Aut_S`-orbit. The non-singleton conjunct is load-bearing (forces `v ∉ S`); lifted out of `VisiblyRecoverable`. | Definition |
| `symmetryOnlyStep_empty_scheme` | 2404-2425 | **Scheme validation of the primitive.** A vertex-transitive schurian scheme is one orbit at `∅`, so individualizing any `v` (with `n ≥ 2`) is a `SymmetryOnlyStep`. | — |
| `Findable` | 2444-2456 | **The harvest-window screen (sequential D1/D2, §6.10+§6.11).** Least-fixed-point inductive: `recovered` (`Discrete` — the F1-correct stop), `abelian` (`ResidualAbelian ∧ ¬IsBase` — guarded D2), `step` (`SymmetryOnlyStep` + recurse). Bound-free classification; `¬Findable` is the seal's wall (IR-blind-spot / Cameron by residual order). | Inductive |
| `FindableWithin` | 2467-2485 | **`Findable` with its recovery depth (Phase 0).** Bound-indexed companion: `recovered`→`b=S.card`, `step` propagates `b`, `abelian` carries `RecoverableByDepth adj P b` as a field (the D2-bridge interface). De-vacuates the `∃ b` conclusion (`recoverableByDepth_univ`). | Inductive |
| `recoverableByDepth_of_findableWithin` | 2487-2497 | **Screen soundness — non-vacuous.** `FindableWithin adj P S b ⟹ RecoverableByDepth adj P b` at the carried bound: `recovered`/`step` free, `abelian` returns its carried recoverability field. | — |
| `findableWithin_cfi_gauge` | 2536-2546 | **D2-bridge anchor (CFI gauge).** For an odd-degree CFI graph, a hidden non-trivial abelian residual (`ResidualAbelian ∧ ¬ IsBase`, the screen's D2 predicate) discharges `FindableWithin` at `cfi_depth_bound h` via the axiom-free `recoverableByDepth_cfi` — the D2 analogue of `visiblyRecoverable_scheme`. | — |
| `recoverableByDepth_of_cfi_gauge` | 2548-2556 | **The CFI gauge is `RecoverableByDepth`.** Bound-carrying soundness applied to `findableWithin_cfi_gauge`: a hidden non-trivial abelian CFI residual recovers by depth `cfi_depth_bound h`, routed through the screen so the D2 leg is certified non-vacuous end-to-end. | — |
| `findable_cfi_gauge` | 2558-2566 | **The CFI gauge is `Findable`** (bound-free classification): a hidden non-trivial abelian CFI residual lands in the screen's D2 leg — the abelian disjunct populated by the central recoverable, non-Cameron example. | — |
| `soStep` | 2586-2590 | Leg A — one round of the symmetry-only closure: individualize a symmetry-only vertex if one exists, else stay put. Extensive; strictly grows until no symmetry-only step remains. | Definition, `noncomputable` |
| `symmetryOnlyStep_not_mem` | 2598-2607 | A symmetry-only step's vertex is not yet committed (`v ∉ S`): a committed vertex is a warm-refinement-preserved singleton, so its cell could not be non-singleton. This is what makes `soStep` strictly grow until stuck. | — |
| `exists_symmetryOnly_saturated` | 2614-2631 | **Leg A — bounded termination of the symmetry-only process.** Iterating the symmetry-only closure from any `S₀` reaches a saturated node `S* ⊇ S₀` with no symmetry-only step available, within `≤ n − |S₀|` rounds — the engine-powered, class-agnostic half of the harvest-window trichotomy's termination. | — |
| `MovedAt` | 2642-2647 | Leg A — a vertex moved by some residual automorphism at `S`; weaker than a symmetry-only step (its cell may be coarser than its orbit), so the right object for the general support induction. | Definition |
| `isBase_of_no_moved` | 2653-2663 | A node with no moved vertex is a base (trivial residual). | — |
| `movedStep` | 2664-2668 | Leg A — one round of the moved-vertex closure: individualize a moved vertex if one exists, else stay. Extensive; strictly grows until the residual is trivial (a base). | Definition, `noncomputable` |
| `exists_isBase_saturated` | 2679-2696 | **Leg A — the general support induction (every graph reaches a base).** Individualizing moved vertices from any `S₀` reaches a base `S* ⊇ S₀` (trivial residual) within `≤ n − |S₀|` rounds, via the `Saturation` engine — holding for every graph (CFI, schemes, rigid alike). | — |
| `MovedAt.anti` | 2709-2718 | **Moved-set anti-monotonicity.** A residual automorphism fixing `S` also fixes any `S₀ ⊆ S`, so a vertex moved at `S` is already moved at `S₀` — the moved-set shrinks as the individualized set grows, which makes it a saturation bound. | — |
| `movedSet` | 2719-2724 | **The residual support at `S₀`:** the vertices moved by some residual automorphism fixing `S₀` (the support of `Aut_{S₀}^P`). Disjoint from `S₀`; its cardinality is the harvest-window depth `|support(g)|`. | Definition, `noncomputable` |
| `mem_movedSet` | 2726-2728 | Membership in `movedSet`: `v ∈ movedSet adj P S₀ ↔ MovedAt adj P S₀ v`. | — |
| `movedStep_subset_bound` | 2730-2743 | Interval invariance of the support bound: on every `f`-reachable set `S₀ ⊆ s ⊆ S₀ ∪ movedSet`, `movedStep` stays inside `S₀ ∪ movedSet` — the hypothesis feeding the interval-invariant saturation engine. | — |
| `exists_isBase_saturated_support` | 2745-2768 | **Leg A — the tight support bound (`base(g) ≤ |support|`).** Sharpens `exists_isBase_saturated`: the moved-vertex closure reaches a base within `≤ |movedSet adj P S₀|` rounds — the residual support, not the full `n`. | — |
| `forcedNode` | 2788-2793 | **The canonical forced node:** `S₀ ∪ movedSet adj P S₀`, individualizing the whole residual support at once. Choice-free — the deterministic, iso-invariant counterpart of the `Classical.choice`-driven `movedStep` saturation. | Definition, `noncomputable` |
| `forcedNode_isBase` | 2795-2805 | **The forced node is a base — choice-free.** Individualizing the full residual support trivializes the residual group, so `forcedNode adj P S₀` is a base with no `Classical.choice`. | — |
| `movedAt_image` | 2807-2832 | **Automorphism-equivariance of `MovedAt`** (one direction). A `P`-preserving automorphism `g` carries a vertex moved at `S₀` to one moved at `S₀.image g`, via the conjugate `g π g⁻¹`. | — |
| `movedAt_image_iff` | 2834-2846 | **Automorphism-equivariance of `MovedAt`** (iff form): `MovedAt adj P (S₀.image g) (g v) ↔ MovedAt adj P S₀ v` for a `P`-preserving automorphism `g`. | — |
| `movedSet_image` | 2848-2864 | The residual support commutes with automorphisms: `movedSet adj P (S₀.image g) = (movedSet adj P S₀).image g`. | — |
| `forcedNode_image` | 2866-2873 | **The forced node is automorphism-equivariant (iso-invariance).** `forcedNode` commutes with every `P`-preserving automorphism — a canonical function of iso-invariant data, not an arbitrary `Classical.choice`. | — |
| `forcedNode_residual_invariant` | 2875-2888 | **The forced node is fixed by the residual group it resolves.** Every residual automorphism at `S₀` maps `forcedNode adj P S₀` to itself setwise. | — |
| `recoverableAt_base_iff_discrete` | 2902-2913 | **Recovery at a base ⟺ discreteness.** At a base `S`, `OrbitRecoverableAt adj P S` holds iff `warmRefine` is `Discrete` — separating the (consumed) symmetry axis from the sole remaining IR-stickiness axis. | — |
| `forcedNode_recoverable_iff_discrete` | 2915-2924 | **Tying the two axes at the canonical node.** At `forcedNode` (a base), orbit recovery is exactly discreteness of `warmRefine`: symmetry consumed plus no IR-stickiness ⟺ recovery. | — |
| `mem_movedSet_iff_nonsingleton_cell_of_recoverable` | 2933-2950 | **The support is the non-singleton cells, at a recoverable node.** Where `OrbitRecoverableAt adj P S`, a vertex is moved iff it shares its 1-WL cell with another — so refinement computes `movedSet`/`forcedNode`. | — |
| `movedSet_eq_nonsingletonCells_of_recoverable` | 2951-2962 | `movedSet` is refinement-computed at a recoverable node (Finset form): it equals the union of the non-singleton 1-WL cells. | — |
| `relabelAdj` | 2973-2975 | **Relabel a graph by `σ`:** the adjacency where `σ v` plays the role `v` did. `σ` is the canonical graph isomorphism `adj → relabelAdj σ adj`. | Definition |
| `relabelAdj_adj` | 2977-2978 | Unfolding lemma: `(relabelAdj σ A).adj i j = A.adj (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `relabelP` | 2980-2982 | **Relabel a `P`-matrix by `σ`:** `Q (σ⁻¹ ·) (σ⁻¹ ·)`. | Definition |
| `relabelP_apply` | 2984-2985 | Unfolding lemma: `relabelP σ Q i j = Q (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `residualAut_relabel` | 2987-3004 | **Residual automorphisms transport along a relabelling** (forward), via the conjugate `σ π σ⁻¹`: a residual aut at `S` becomes one at `S.image σ` in the relabelled graph. | — |
| `residualAut_relabel_symm` | 3006-3023 | **Residual automorphisms transport back from a relabelling** (reverse), via `σ⁻¹ π σ`. | — |
| `movedAt_relabel_iff` | 3025-3040 | **`MovedAt` is equivariant under relabelling:** `MovedAt (relabelAdj σ adj) (relabelP σ P) (S₀.image σ) (σ v) ↔ MovedAt adj P S₀ v`. | — |
| `movedSet_relabel` | 3042-3057 | The residual support is equivariant under relabelling: `movedSet (relabel… σ) (S₀.image σ) = (movedSet adj P S₀).image σ`. | — |
| `forcedNode_relabel` | 3059-3067 | **Forced node equivariant under arbitrary relabelling — full iso-invariance.** Relabelling the input by any `σ` (not just an automorphism) maps the canonical forced node correspondingly. | — |
| `rigidResidue` | 3085-3089 | **The RRU rigid residue `R(G)`.** The canonical base the Seal Phase hands to Phase 2: `forcedNode` at `∅` (individualize the whole residual support of `Aut(adj)`). Choice-free, deterministic. | Definition, `noncomputable` |
| `rigidResidue_isBase` | 3091-3095 | **RRU — rigid (unconditional).** `R(G)` is always a base — the residual automorphism group is trivial there, for every `adj`. | — |
| `rigidResidue_relabel` | 3097-3104 | **RRU — iso-invariant.** `R(G)` transports under every relabelling `σ` (`rigidResidue (relabelAdj σ adj) = (rigidResidue adj).image σ`). | — |
| `exists_movedAt_of_not_isBase` | 3106-3113 | **RRU progress → moved vertex.** Not-a-base ⟹ the residual support is nonempty (`∃ v, MovedAt adj P S v`); brick-1 bridge to `MovedAt`/`forcedNode`, converse of `isBase_of_no_moved`. | — |
| `visiblyRecoverable_pPolynomial` | 3123-3135 | **D1 for every P-polynomial (metric / DRG) scheme graph.** Generalizes `visiblyRecoverable_scheme` (rank-2 / `|J|=1`) to the whole distance-regular family via the depth-1 metric recovery `theorem_2_HOR_of_pPolynomial`. | — |
| `forcedExpand` | 3145-3151 | **M-D instance — the canonical exploration rule.** For rep `r` at a node, explore `r` together with its residual support: `insert r (movedSet adj chain.P (insert r chain.D))`. Iso-invariant and automorphism-equivariant (the per-rep forced node). | Definition, `noncomputable` |
| `lockstepExpand_forcedExpand` | 3153-3171 | **M-D — the lockstep is a theorem.** `forcedExpand` satisfies `LockstepExpand` — the residual-support half is exactly `movedSet_image`, the committed prefix is fixed setwise by `g`. So `matchOracleSet (forcedExpand …)` needs no lockstep hypothesis, only the depth witness. | — |
| `schemeAdj` | 3190-3195 | **(LargenessBridge discharge — scheme→graph encoding)** Encodes a scheme `S` as a *labelled* `AdjMatrix`, entry `(v,w) ↦ (relOfPair v w).val` (edge labels = relation indices). The single graph whose `IsAut` coincides with `IsSchemeAut`, bridging schemes to the graph-side stabilizer-chain machinery. | Definition, `noncomputable` |
| `isAut_schemeAdj_iff` | 3197-3212 | **(LargenessBridge discharge — faithfulness)** `IsAut π (schemeAdj S) ↔ IsSchemeAut S π`: preserving the labelled adjacency is exactly preserving every relation index (forward via `rel_iff_relOfPair`, reverse via `IsSchemeAut.relOfPair_eq`). | — |
| `stabilizerAt_schemeAdj_empty_eq` | 3214-3222 | **(LargenessBridge discharge — group identification)** With the trivial all-`unknown` `P`, `StabilizerAt (schemeAdj S) ⊥ ∅ = SchemeAutGroup S` (the `P`-condition is vacuous, `IsAut`=`IsSchemeAut`). Carries `Nat.card` equality across the bridge, letting the graph-side `isLargeAutP_of_noFusion` speak about the scheme group. | — |
| `exists_greedy_base_scheme` | 3224-3236 | **(A3.6 — `2 ^ |base| ≤ |SchemeAutGroup S|`, the scheme floor's base term; step 2.1)** Transports `exists_greedy_base` across the `schemeAdj` bridge (`stabilizerAt_schemeAdj_empty_eq`): the scheme's root residual order is `|SchemeAutGroup S|`, so the greedy base over `schemeAdj S` has length `≤ log₂` of it. Banks `base(G)` for the scheme floor — for small `|SchemeAutGroup|` the base is `O(log n)`. Axiom-clean. | — |
| `iterate_refineStep_colour_refines` | 3250-3261 | **(iterated refinement is split-only, colour-equality form)** The general `k`-fold form of `warmRefine_refines`: equal colour after `k` `refineStep` rounds implies equal colour before. The peeling tool for `relOfPair_eq_of_warmRefine_singleton`. | — |
| `relOfPair_eq_of_warmRefine_singleton` | 3272-3323 | **(`warmRefine` from `{v}` separates by the relation to `v`)** For non-`v` vertices `w, u` in the same `warmRefine (schemeAdj S) … {v}` cell, `relOfPair v w = relOfPair v u`. Peels `warmRefine` to one `refineStep` round, reads off `signature` equality (`refineStep_iff`), and uses the count bridge (`signature_eq_card_eq`): the individualized `v`'s unique colour makes its neighbour-tuple the only one with first component `χ v`, so the two `v`-neighbour edge labels coincide — on `schemeAdj`, `(relOfPair v w).val = (relOfPair v u).val`. The cells ⊆ `relOfPair(v,·)`-classes half of single-base recovery. | — |
| `cellsAreOrbits_schemeAdj_singleton` | 3325-3352 | **(single-base recovery is FREE — the self-detection base case, §13a.)** For *every* schurian scheme, the `warmRefine` cells after individualizing a single vertex `v` coincide with the `Stab(v)`-orbits (`CellsAreOrbits (schemeAdj S) … {v}`). **Insight:** single-base recovery is unconditional, so the entire self-detection crux is the *multi-base* extension (`|T|≥2`, the `s(C)` gap). Axiom-clean. | — |
| `IsLargeSchemeViaAut` | 3354-3358 | **(LargenessBridge discharge — concrete largeness)** The instantiation of §12's abstract `IsLargeScheme` parameter: a scheme is large when `Nat.card SchemeAutGroup` satisfies the abstract super-polynomiality citation `IsLarge : Nat → Prop` (the genuine Cameron driver). | Definition |
| `reachesRigidOrCameron` | 3381-3400 | **(THE SEAL CAPSTONE — the project goal as one theorem, general form)** Every rank-≥3 schurian scheme residual `ReachesRigid ∨ IsCameronScheme` — reaches a rigid residual (consumed by the cascade/abelian oracles, legs A/B) or is a Cameron section (flag, leg C). Pure assembly of `exhaustiveObstruction_scheme_nonCascade_trichotomy`: `¬IsPrimitive`→`hImprimitive` (the open primitivity reduction), `¬NonCascade`→`hCascade` (leg-A recovery, well-supported), Cameron→landed. `ReachesRigid` abstract (descent outcome); hypotheses = the exact honest remainder. | — |
| `reachesRigidOrCameron'` | 3402-3423 | **(seal capstone, primitivity-carrying — the self-detection wiring)** Identical to `reachesRigidOrCameron` but the cascade reduction is sharpened to the **primitive floor**: `hCascade : IsPrimitive ∧ ¬ NonCascade → ReachesRigid`. The honest shape of the open content — the cascade obligation is *self-detection* (a primitive small residual recovers), not an all-`¬NonCascade` claim (imprimitive small residuals route through `hImprimitive` first). Wires `exhaustiveObstruction_scheme_nonCascade_trichotomy'`. Axiom-clean. | — |
| `SchemeRecovered` | 3484-3501 | **(NON-VACUOUS `ReachesRigid` — replaces the vacuous `SchemeReproduced`)** `S` is *recovered* when ∃ harvested `gens` (path-fixing) + base `bs` such that at **every** level every same-`warmRefine`-cell pair is realized by a residual aut in `gens`. The **visible** (same-cell) realizer clause is the non-vacuity: satisfiable only where cells = orbits (recovery), **false for high `s(C)`** (a same-cell non-orbit pair has no realizing aut). Machine-checked that the old `∃ gens, closure gens = SchemeAutGroup` was trivially true (`⟨↑SchemeAutGroup, closure_eq⟩`) and that this is not. | Definition |
| `schemeAutGroup_eq_closure_of_recovered` | 3503-3516 | **(Recovery ⟹ group reproduced — a theorem now, not a free existential)** From `SchemeRecovered` (visible realizers + base), the harvested `gens` generate exactly `SchemeAutGroup S`, via `closure_eq_stabilizerAt_of_visibleRealizers` + the `schemeAdj` bridge. The content the vacuous `SchemeReproduced` asserted for free, here *earned* from the non-vacuous visible-recovery witness. | — |
| `schemeRecovered_of_visibleRealizers` | 3518-3537 | **(Discharge `SchemeRecovered` from the visible-realizer harvest)** Bundles path-fixing soundness + per-level visible (same-cell) realizers + a terminal base into a recovery witness. The single tool both non-Cameron branches of the seal use; the visible-realizer hypothesis is satisfiable on the recoverable class (`recoverableByDepth_pPolynomial`/`_cfi`) and false off it — exactly the non-vacuity. | — |
| `AbelianConsumed` | 3612-3625 | **(leg B — the hidden-abelian consumption certificate, G1b.)** A residual is *abelian-consumed* when its root residual is non-trivial (`¬IsBase`) and every decision is uniquely determined on its cell (any two automorphisms `a↦b` agree on `a`'s whole orbit) — the linear oracle's 'unique candidate' property. Non-vacuous: the determinacy clause is genuinely false for a non-abelian residual with disagreeing candidates. | Definition |
| `abelianConsumed_of_residualAbelian` | 3627-3645 | **(leg-B core — abelian residual ⟹ consumed, citation-free)** From an abelian (`ResidualAbelian`) non-trivial (`¬ IsBase`) root residual, derives `AbelianConsumed`: the decisions are uniquely determined on their cells. The determinacy is **earned** via `aut_agree_on_orbit_of_comm` (L3, `Group.lean`) — bridging `ResidualAbelian (schemeAdj S) unknown ∅` to `AutGroup`-commuting through `mem_autGroup` + the trivial `ResidualAut`↔`IsAut`-at-∅. No citation, no WL-dimension content; survives CFI's non-trivial global stabilizers because L3 is faithfulness/quotient-free. Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `SchemeRecoveredByDepth` | 3707-3728 | **(depth-graded recovery, G1a.)** `S` is *recovered by depth `bound`* when a harvested `gens` + a two-phase base sequence reproduce the residual: a shallow phase builds the bounded set `S₀` (`|S₀|≤bound`) with orbit-coverage, then a deep phase from `S₀` realizes every same-`warmRefine`-cell pair (visible recovery) to a base. Generalizes `SchemeRecovered` (the `S₀=∅` case) to the depth-graded family (CFI at `tw`, Shrikhande at 2). Non-vacuous (deep visible clause + the bound). | Definition |
| `schemeAutGroup_eq_closure_of_recoveredByDepth` | 3730-3744 | **(depth-graded recovery ⟹ group reproduced)** From `SchemeRecoveredByDepth`, the harvested `gens` generate exactly `SchemeAutGroup S`: the deep phase gives `CoversOrbits bs₂ S₀` (`coversOrbits_of_visibleRealizers`), `coversOrbits_append` glues the carried shallow `CoversOrbitsAlong bs₁ ∅` to it (`CoversOrbits (bs₁++bs₂) ∅`), then `closure_eq_stabilizerAt_empty_of_coversOrbits` + `stabilizerAt_schemeAdj_empty_eq`. The full root group reproduced from a depth-graded harvest, with the shallow ∅→S₀ coverage the only carried (localisation) input. Axiom-clean. | — |
| `schemeRecoveredByDepth_of_schemeRecovered` | 3746-3754 | **(per-level recovery is the depth-0 case — strict generalization)** `SchemeRecovered n S → SchemeRecoveredByDepth n S 0`: empty shallow phase (`bs₁=[]`, `S₀=∅`, `CoversOrbitsAlong [] ∅` is `True`), the original `∀ T ⊇ ∅` visible realizers as the deep phase. So `SchemeRecovered ⊆ SchemeRecoveredByDepth … 0` — the depth-graded predicate captures everything the per-level one does plus the depth-graded family it could not. | — |
| `exists_foldl_insert_eq` | 3772-3785 | **(materialize a finset as a `foldl`-insert sequence)** For any `S U`, some list inserts `U`'s elements into `S` (`∃ l, l.foldl insert S = S ∪ U`). Used to express the shallow set `S₀` and the terminal base as the `foldl`-insert base sequences `SchemeRecoveredByDepth` demands. | — |
| `StablyRecoverable` | 3787-3793 | **(the semantic self-detection target — Increment 2)** `S₀` is a set above which 1-WL recovers the orbits: at *every* `T ⊇ S₀`, `warmRefine` cells coincide with `Aut_T`-orbits (`CellsAreOrbits`). The honest semantic match to `SchemeRecoveredByDepth`'s per-`T` deep clause, with the **localisation made explicit** (recovery is *stable* above `S₀`, not just present at `S₀` — a single `CellsAreOrbits S₀` does not give per-`T` realizers fixing `T`'s extra points, insight 7). **Non-vacuous** (cells = orbits, false for high `s(C)`), not orbit-level coverage; exactly what separability monotonicity yields, so the right Phase-2 target. | Definition |
| `RecoversWhileSymmetric` | 3818-3823 | **(The G2-B residue.)** Recovery (`CellsAreOrbits`) at the **non-base** prefixes above `S₀` — while residual symmetry is still present to consume. Empirically `O(1)` (depth-growth probes: small non-abelian primitive flat at depth ≤ 4). Single-base free (schurian); open content = the multi-base `JointProfileRecoversAt`. | Definition |
| `DiscretizesAtBases` | 3825-3829 | **(The IR-core term.)** Recovery at the **base** prefixes above `S₀` (`IsBase`). By `discretizesAtBases_iff` = discretization of the rigid post-base residual — the multipede / IR-blind-spot quantity (can be unbounded), the **second guarantee**'s concern, *not* a symmetry-completeness obligation. | Definition |
| `stablyRecoverable_iff_symmetric_and_bases` | 3831-3843 | **(The conservation budget split.)** `StablyRecoverable ↔ DiscretizesAtBases ∧ RecoversWhileSymmetric` — separates the IR-core term from the G2-B residue. Case-split on `IsBase`; the content is the separation it names: the seal's open `StablyRecoverable` is the bounded residue **plus** the flag-allowed IR-core, revealing `StablyRecoverable` over-requires (folds the IR-core into the seal). Axiom-clean. | — |
| `discretizesAtBases_iff` | 3845-3859 | The IR-core term is exactly discretization at the bases: for `IsBase T`, `CellsAreOrbits T ↔ Discrete (warmRefine … T)` (via `recoverableAt_base_iff_discrete` + `orbitRecoverableAt_iff_cellsAreOrbits`). Confirms `DiscretizesAtBases` is the multipede/second-guarantee quantity, not a seal obligation. Axiom-clean. | — |
| `isBase_of_subset_of_isBase` | 3871-3878 | **(step 2.2 — base sets are upward-closed)** `S ⊆ S' ∧ IsBase S ⟹ IsBase S'` (the residual `StabilizerAt` shrinks under `stabilizerAt_mono`, so trivial stays trivial). Contrapositive — **non-base is downward-closed** — is the engine of the layer-step reduction. Axiom-clean. | — |
| `LayerRecovers` | 3880-3886 | **(step 2.2 — the per-layer recovery transfer)** `∀ T x, S₀ ⊆ T → x ∉ T → ¬IsBase (insert x T) → CellsAreOrbits T → CellsAreOrbits (insert x T)`: one further individualization keeps cells = orbits (the single-insertion, non-base-guarded `LayerStep`). The local form of the `s(C)` content — the per-step bridge `JointProfileRecoversAt {T,x}` (`Scheme.lean §S1.c`) discharges (step 2.3). | Definition |
| `recoversWhileSymmetric_of_layerRecovers` | 3888-3929 | **(THE LAYER-STEP REDUCTION, step 2.2)** `RecoversWhileSymmetric S₀` from a **base case** (`¬IsBase S₀ → CellsAreOrbits S₀`) plus a **per-layer transfer** (`LayerRecovers`). Strong induction on `T.card`: a non-base `T ⊋ S₀` erases `x ∈ T \ S₀` to a smaller non-base prefix (non-base downward-closed), the IH recovers it, the transfer lifts to `T`. Localizes the global WL-dimension claim (`∀ non-base T ⊇ S₀`) to a per-step condition — the form step 2.3 attacks. Axiom-clean. | — |
| `coversOrbitsAlong_stabilizerAtEmpty` | 3931-3945 | **(the root group covers every orbit along any base sequence)** `CoversOrbitsAlong` holds for `gens = ↑(StabilizerAt … ∅)` (all `P`-preserving auts): an orbit-mate at `S` is realized by the residual automorphism itself, which lies in `gensAt … S`. The (genuinely true, non-load-bearing) orbit-level coverage; the non-vacuous content of recovery is the *visible* deep clause, not this. | — |
| `schemeRecoveredByDepth_of_stablyRecoverable` | 3947-3974 | **(THE SEMANTIC RECOVERY BRIDGE — `StablyRecoverable ⟹ SchemeRecoveredByDepth`.)** From stable recovery above a bounded set `S₀` (`|S₀|≤bound`), the scheme is recovered by depth `bound`. Converts the seal's semantic recovery (cells = orbits above `S₀`) into the harvest-witness object Phase 2 attacks. Axiom-clean. | — |
| `schemeAutGroup_eq_closure_of_recoversWhileSymmetric` | 3976-4010 | **(The rewiring's heart — the IR-core is NOT needed.)** The full root group is reproduced from `RecoversWhileSymmetric` (symmetry-phase recovery) **alone**: deep phase via `coversOrbits_of_visibleRealizers_symmetric` (non-base realizers), shallow `∅→S₀` via free orbit coverage. So the (unbounded, flag-allowed) IR-core discretization that `StablyRecoverable` over-required is dropped. Axiom-clean. | — |
| `SelfDetectsStably` | 4012-4020 | **(the SEMANTIC self-detection proposition — `SelfDetectsAtDepth` on `StablyRecoverable`)** A schurian residual *self-detects stably at depth `bound`* when, *if primitive and small*, it recovers stably above some bounded set (`∃ S₀, |S₀| ≤ bound ∧ StablyRecoverable S₀`). The cleanest semantic form of the self-detection lemma — the object the affine module-theory argument (Phase 2 §5.1) produces and the catalogue probe measures (cells = orbits above `base + O(1)` individualizations). | Definition |
| `stablyRecoverable_of_discrete` | 4035-4048 | **(Phase 2, M2 reduction — general)** If `warmRefine` from `S₀` is `Discrete`, then `StablyRecoverable adj P S₀`. Discreteness propagates to every `T ⊇ S₀` (`individualizedColouring_refines` + `warmRefine_refines_initial`: finer initial colouring stays discrete) and `Discrete ⟹ CellsAreOrbits` (`cellsAreOrbits_of_discrete`). Reduces the multi-base recovery crux to a pure "reaches singletons at bounded depth" statement. Non-vacuous (false for any nontrivial residual symmetry above `S₀`). | — |
| `selfDetectsStably_of_discretizes` | 4050-4064 | **(Phase 2, M2 — the crux reduced to discretization)** `SelfDetectsStably` follows from *"primitive small ⟹ ∃ bounded `S₀` with `warmRefine`-from-`S₀` discrete"* — a refinement-only (orbit-free) statement, for **any** schurian scheme. The M2 target the affine module argument (and any Phase-2 family) now produces; the catalogue/affine probes measure exactly this discretization depth. | — |
| `individualizedColouring_mem_sep` | 4080-4094 | (Phase 2, M2-B helper) Each individualized `t ∈ T` carries a colour unique to it under `individualizedColouring n T` (the `Finset`-set analogue of `individualizedColouring_singleton_sep`). | — |
| `discrete_of_jointProfileSeparates` | 4096-4125 | **(Phase 2, M2-B — the depth-1 discreteness producer.)** If the joint profile `(relOfPair t ·)_{t∈T}` is injective, then `warmRefine (schemeAdj S)` from `T` is `Discrete` (cells refine the joint profile). Feeds `stablyRecoverable_of_discrete`. **Scope:** the depth-1 (`s(C)=1`) producer — covers depth-1-separating primitives; the iterated (`s(C)≥2`, cyclotomic) extension is open. | — |
| `DepthOneSeparable` | 4127-4149 | **(Phase 2, M2-B — the `s(C)=1` predicate, a NAMED SPECIAL CASE not the closed crux)** `∃ T, T.card ≤ bound ∧ the depth-1 joint profile `(relOfPair t ·)_{t∈T}` separates all vertices`. Strictly stronger than what `SelfDetectsStably` needs (separation after one round from `T`); covers the depth-1-recoverable primitives, **not** `s(C)≥2` (cyclotomic). **⚠️ The open engine slots in beside `selfDetectsStably_of_depthOneSeparable` as a bounded-depth/iterated producer — this predicate is NOT the closed crux.** Bound-non-vacuity hinge: `DepthOneSeparable S n` is trivially true (`T=univ`), content lives at small bound (cf. `recoverableByDepth_univ`). | Definition |
| `selfDetectsStably_of_depthOneSeparable` | 4151-4164 | **(Phase 2, M2-B — the depth-1 route into self-detection / THE SLOT)** `(primitive ∧ small → DepthOneSeparable S bound) → SelfDetectsStably S IsLarge bound`, via `discrete_of_jointProfileSeparates` + `selfDetectsStably_of_discretizes`. The `s(C)=1` route; the open engine adds a *sibling* `…_of_boundedDepthSeparable` for `s(C)≥2`, not a replacement of the seal. | — |
| `SelfDetectsAtDepth` | 4205-4216 | **(the self-detection proposition — the seal's single open content, named.)** A schurian residual *self-detects at depth `bound`* when, if primitive and small, it recovers at bounded depth (`SchemeRecoveredByDepth`). The seal closes (modulo cited G3 + landed imprimitive recovery) exactly when this holds for all primitive small residuals. Non-vacuous; the conjecture that it holds at `bound = base + O(1)` is the self-detection lemma. | Definition |
| `selfDetectsAtDepth_of_selfDetectsStably` | 4235-4243 | **(semantic ⟹ harvest-witness self-detection)** `SelfDetectsStably ⟹ SelfDetectsAtDepth`, via `schemeRecoveredByDepth_of_stablyRecoverable`. So the seal's entire open content discharges from the clean semantic recovery predicate (cells = orbits above a bounded set). Axiom-clean. | — |
| `SchemeRecoveredWhileSymmetric` | 4273-4281 | **(The IR-core-free rigid predicate.)** Recovery throughout the symmetry phase from a bounded start (`∃ S₀ ≤ bound, RecoversWhileSymmetric S₀`). Group reproduced from it, no IR-core obligation. Non-vacuous at `bound ≪ n`. | Definition |
| `schemeAutGroup_eq_closure_of_schemeRecoveredWhileSymmetric` | 4283-4290 | The group-reproduction payoff: `SchemeRecoveredWhileSymmetric ⟹ ∃ gens, closure = SchemeAutGroup` (unpacks + `schemeAutGroup_eq_closure_of_recoversWhileSymmetric`). Axiom-clean. | — |
| `schemeRecoveredWhileSymmetric_of_stablyRecoverable` | 4292-4299 | **(The symmetric seal subsumes the stable one.)** `StablyRecoverable ⟹ SchemeRecoveredWhileSymmetric` (drop the `DiscretizesAtBases` conjunct). So the rewiring only weakens the obligation — every scheme the old seal placed is placed here. Axiom-clean. | — |
| `SelfDetectsWhileSymmetric` | 4301-4305 | **(The IR-core-free crux.)** Primitive small ⟹ `SchemeRecoveredWhileSymmetric` — the genuine open content after the split (bounded `O(1)` G2-B residue), weaker than `SelfDetectsStably` (no IR-core). | Definition |
| `schemeRecoveredWhileSymmetric_of_layerRecovers` | 4307-4316 | **(step 2.2 — scheme layer-step reduction)** `SchemeRecoveredWhileSymmetric n S bound` from a bounded start `S₀` (`|S₀| ≤ bound`), its base case, and per-layer recovery (`recoversWhileSymmetric_of_layerRecovers` over `schemeAdj`). The seal's rigid side reduced to the local per-step condition. Axiom-clean. | — |
| `selfDetectsWhileSymmetric_of_layerRecovers` | 4318-4331 | **(step 2.2 — self-detection reduced to per-layer recovery)** `SelfDetectsWhileSymmetric S IsLarge bound` from "primitive small ⟹ ∃ bounded `S₀` with base case + `LayerRecovers`" — the seal's entire open content localized to the per-step bridge (`JointProfileRecoversAt`, step 2.3), with `base(G)` banked (step 2.1) into the `bound`. Axiom-clean. | — |
| `SchemeBlockRecovered` | 4371-4401 | **(the imprimitive branch's earned rigid predicate — scheme-seal wiring)** `S` is *block-recovered* when for some `ClosedSubset I` block system `β_I v := {y | schemeEquiv I v y}` there is a harvested `gens` + base with **refinement-computable** quotient coverage (same-`warmRefine`-cell pairs have a `gens`-realizer landing `b` in `w`'s **block**) + fiber coverage (same-cell *same-block* pairs have an exact `gens`-realizer). **Non-vacuous**: keying `β` on a `ClosedSubset` forces a *primitive* scheme to trivial `β` ({0}⟹singletons⟹quotient=full recovery; univ⟹one block⟹fiber=full recovery), false on the G2-B leak; subsumes `SchemeRecovered` as the `I={0}` case. | Definition |
| `schemeAutGroup_eq_closure_of_blockRecovered` | 4403-4418 | **(block-visible recovery ⟹ group reproduced, earned)** From `SchemeBlockRecovered`, `gens` generate exactly `SchemeAutGroup S` via `reachesRigid_of_blockVisibleDecomposition` on `β_I` (quotient + fiber, both visible) + the `schemeAdj` bridge. Imprimitive analogue of `schemeAutGroup_eq_closure_of_recovered`; no sub-scheme materialized. Axiom-clean. | — |
| `schemeBlockRecovered_of_visibleRealizers` | 4420-4456 | **The block-recovery PRODUCER — `hImprim` localized to the two visible constituent-recovery interfaces.** Seal-facing counterpart of the consumer `schemeAutGroup_eq_closure_of_blockRecovered`: a block system `I` (`ClosedSubset`) + sound `gens` + base `bs` + the block-visible quotient (`hqvis`, block-move) and fiber (`hfvis`, within-block) realizers keyed on `β_I = schemeEquiv I` ⟹ `SchemeBlockRecovered`. With `exists_nontrivial_closedSubset_of_not_isPrimitive`, shows the carried `hImprim : ¬IsPrimitive → SchemeBlockRecovered ∨ AbelianConsumed` reduces to **exactly** the two constituent-recovery interfaces (the substrate-conditional **A2-ii** content) on the smaller constituents (schurian by the §11.1 gate), via the Route B block tower (≤ log₂ n layers, no sub-scheme materialized). So `hImprim` is **not** independent — like `hcatch` it collapses onto the same WL-recovery core as the primitive floor. Axiom-clean. | — |
| `reachesRigidOrCameron_viaFusedSeal` | 4480-4522 | **(THE FUSED SEAL — single headline capstone.)** `((SchemeBlockRecovered ∨ AbelianConsumed) ∨ SchemeRecoveredByDepth) ∨ IsCameronScheme` for every rank-≥3 schurian residual: each non-Cameron branch via its strongest form (cascade → `SchemeRecoveredByDepth`, the G2-B core; imprimitive → earned `SchemeBlockRecovered ∨ AbelianConsumed`; else cited Cameron). Carries `{hSelfDetect (G2-B crux) + hImprim + G3}` as one statement. Axiom-clean. | — |
| `twoRoundCount_eq_of_warmRefine` | 1499-1547 | §13b **(the depth-2 separation primitive, E1.)** For `w,u` in the same `warmRefine (schemeAdj S)`-cell after individualizing a base **set** `T`, the depth-2 count profile coincides: for every one-round colour `c` and relation `b`, `#{z≠w : refineStep z=c ∧ relOfPair w z=b} = #{z≠u : …}`. The multi-base depth-2 brick of the affine-cyclic engine (beyond depth-1's single-base intersection-number collapse). Axiom-clean. | — |
| `discrete_of_twoRoundProfileSeparates` | 1549-1569 | **(§13b — the depth-2 discreteness producer, E1)** If the depth-2 count profile separates all vertices, `warmRefine (schemeAdj S)` from `T` is `Discrete`. The depth-2 analogue of `discrete_of_jointProfileSeparates` (depth-1, insufficient for `s(C) ≥ 2`): same-cell vertices share the depth-2 profile (`twoRoundCount_eq_of_warmRefine`), so an injective profile forces singletons. Composes with `stablyRecoverable_of_discrete` → `selfDetectsStably_of_discretizes`; the producer the affine-cyclic (`s(C) ≥ 2`) bound proof discharges (exhibit a separating `T` of size `base + O(1)`). Axiom-clean. | — |
| `relOfPair_eq_of_refineStep_base` | 1571-1621 | **(§13b — Lemma A, the colour→relation bridge)** The one-round colour `refineStep (schemeAdj S) … (individualizedColouring n T)` determines the relation `relOfPair t ·` to each base point `t ∈ T`: same one-round colour ⟹ `relOfPair t z = relOfPair t z'`. Mirrors `relOfPair_eq_of_warmRefine_singleton`'s isolation at **one** round and a base **set** (individualized `t∈T` carries a unique colour, `individualizedColouring_mem_sep`, isolating its signature tuple). The ingredient that lets the depth-2 counts be re-grouped by relation, not colour. Axiom-clean. | — |
| `twoRoundCountP_eq_of_warmRefine` | 1623-1665 | **(§13b — aggregate countP form of `twoRoundCount_eq_of_warmRefine`)** Same `warmRefine`-from-`T` cell ⟹ for any colour predicate `q` and relation `b`, equal counts of `z` with `q(one-round colour z) ∧ relOfPair · z = b`. Same peel-to-`refineStep^[2]` proof via the aggregate `signature_eq_countP_eq`. The vehicle that lets the colour grouping be re-expressed by any predicate. Axiom-clean. | — |
| `twoRoundProfileCount_eq` | 1667-1708 | **(§13b — the colour→relation conversion, the payoff)** Re-groups `twoRoundCount` by the **joint relation profile** `(relOfPair t z)_{t∈T}`: same cell ⟹ for every profile `ρ` and relation `b`, equal counts of `z` matching `(relOfPair t z = ρ t)_{t∈T} ∧ relOfPair · z = b`. Combines `twoRoundCountP_eq_of_warmRefine` (aggregate) with `relOfPair_eq_of_refineStep_base` (Lemma A), via the colour predicate `q c := ∃ z₀, colour z₀ = c ∧ profile z₀ = ρ`. **The relation-indexed depth-2 count the Frobenius/affine separability argument consumes** (not opaque colours). Axiom-clean. | — |
| `discrete_of_twoRoundRelationSeparates` | 1710-1731 | §13b **(the relation-form depth-2 discreteness producer.)** If the joint relation-profile counts separate all vertices, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. The producer the Frobenius/affine `s(C)` bound discharges (a bounded Galois-breaking `T` ⟹ `Discrete` ⟹ the seal); relation-form analogue of `discrete_of_twoRoundProfileSeparates`. Axiom-clean. | — |
| `kRoundCount_eq_of_warmRefine` | 1745-1787 | **(§13c — depth-`k` engine, count primitive)** For `w, u` in the same `warmRefine (schemeAdj S)` cell after individualizing `T`, the depth-`(k+1)` count profile coincides: for every `k`-round colour `c` (`(refineStep)^[k]` of the individualized colouring) and relation `b`, `#{z≠w : kcol(z)=c ∧ relOfPair w z=b} = #{z≠u : …}`. Peel `warmRefine` to `refineStep^[k+1]` (needs `k+1≤n`), read `signature` at `(refineStep)^[k]`. Generalises `twoRoundCount_eq_of_warmRefine` (`k=1`). Axiom-clean. | — |
| `discrete_of_kRoundProfileSeparates` | 1789-1808 | **(§13c — depth-`k` producer, colour form)** If the depth-`(k+1)` count profile separates all vertices, `warmRefine (schemeAdj S)` from `T` is `Discrete`. Generalises `discrete_of_twoRoundProfileSeparates` (`k=1`); composes to `selfDetectsStably_of_discretizes`. The general primitive-floor / §5.3 producer (build-for-generality; affine-cyclic needed only `k=1`). Axiom-clean. | — |
| `relOfPair_eq_of_iterateRefineStep_base` | 1810-1828 | **(§13c — iterated Lemma A)** If `z, z'` share their `k`-round colour `(refineStep)^[k] χ` (`k≥1`), then `relOfPair t z = relOfPair t z'` for every `t∈T`. Via `refineStep_iter_le_eq` (`^[k]`-eq ⟹ `^[1]`-eq) + one-round Lemma A. The colour→relation bridge at depth `k`. Axiom-clean. | — |
| `kRoundCountP_eq_of_warmRefine` | 1830-1869 | **(§13c — depth-`k` countP form)** Predicate-indexed generalization of `kRoundCount_eq_of_warmRefine` (depth-`k` analogue of `twoRoundCountP_eq_of_warmRefine`): same-cell `w,u` agree on `#{z : q(kcol z) ∧ relOfPair · z = b}` for any colour predicate `q`. Vehicle for the colour→relation conversion. Axiom-clean. | — |
| `kRoundProfileCount_eq` | 1871-1909 | **(§13c — depth-`k` joint-relation form)** Re-groups `kRoundCount` by the joint relation profile `(relOfPair t z)_{t∈T}` instead of the opaque `k`-round colour. Depth-`k` analogue of `twoRoundProfileCount_eq`, combining `kRoundCountP_eq_of_warmRefine` with iterated Lemma A. The relation-indexed depth-`k` count a general separability argument consumes. Axiom-clean. | — |
| `discrete_of_kRoundRelationSeparates` | 1911-1927 | **(§13c — depth-`k` producer, relation form)** If the joint relation-profile counts separate all vertices, `warmRefine (schemeAdj S)` from `T` is `Discrete`. Depth-`k` analogue of `discrete_of_twoRoundRelationSeparates` (`k=1`). The general engine for the primitive-floor / §5.3 crux (stated for any `AssociationScheme`; bound proof slice-specific). Axiom-clean. | — |
| `affineE` | 2092-2094 | (Phase 2, M0.3) The transport `F_p^d ≃ Fin (p^d)` (the scheme lives on `Fin (p^d)`). | Definition, `noncomputable` |
| `affineEquivV` | 2096-2102 | (Phase 2, M0.3) The affine permutation `x ↦ g₀ x + t` of `V = F_p^d` (explicit inverse `y ↦ g₀⁻¹(y−t)`). | Definition |
| `affinePermFin` | 2104-2107 | (Phase 2, M0.3) `affineEquivV` transported to `Perm (Fin (p^d))` via `affineE.permCongr`. | Definition, `noncomputable` |
| `affinePermFin_one` | 2114-2117 | (Phase 2, M1.0) The identity is the trivial affine perm (`affinePermFin 1 0 = 1`). | — |
| `affinePermFin_mul` | 2119-2126 | (Phase 2, M1.0) **Affine perms compose to affine perms**: `affinePermFin g₀ t * affinePermFin h₀ s = affinePermFin (g₀h₀) (g₀s+t)`. | — |
| `affinePermFin_inv` | 2128-2136 | (Phase 2, M1.0) The inverse of an affine perm is affine (`(affinePermFin g₀ t)⁻¹ = affinePermFin g₀⁻¹ (−g₀⁻¹t)`). | — |
| `affineGenSet` | 2138-2140 | (Phase 2, M0.3) The affine permutations whose linear part lies in `G₀` — the generating set of `V ⋊ G₀`. | Definition |
| `affineG` | 2142-2154 | **(Phase 2, M0.3/M1.0)** The affine group `V ⋊ G₀` as a `Subgroup (Perm (Fin (p^d)))` — the *carrier-set* subgroup of affine perms (closed under `*`/`⁻¹`/`1` by `affinePermFin_mul`/`_inv`/`_one`), so membership is transparently "is an affine perm with linear part in `G₀`". | Definition, `noncomputable` |
| `mem_affineG_iff` | 2156-2160 | **(Phase 2, M1.0)** Membership in `affineG` ⟺ being an affine perm with linear part in `G₀` (`σ = affinePermFin g₀ t`, `g₀ ∈ G₀`). The transparent characterization the orbital argument needs. | — |
| `affineG_isPretransitive` | 2167-2177 | **(Phase 2, M0.3)** Transitivity — translations act transitively on `F_p^d`. Supplies `orbitalScheme`'s `htrans`. | — |
| `affineG_generous` | 2179-2197 | **(Phase 2, M0.3)** Generous transitivity — with `-1 ∈ G₀`, `orbMk x y = orbMk y x` (the affine swap `u ↦ -u + (x+y)`), making the scheme symmetric. Supplies `orbitalScheme`'s `hsymm`. | — |
| `affineScheme` | 2199-2207 | **(Phase 2, M0.3 — THE BEACHHEAD MODEL)** The affine scheme `V ⋊ G₀` over `F_p^d` as a `SchurianScheme (p^d)`, via `orbitalScheme (affineG G₀)`. Relations = `G₀`-orbits on differences; `relOfPair x y` = orbit of `y−x`. Pluggable into `SelfDetectsStably`/the seal. Requires `-1 ∈ G₀`. Next: M1 (`IsPrimitive` ⟺ `G₀` irreducible), M2 (irreducible ⟹ recovers). Axiom-clean. | Definition, `noncomputable` |
| `orbMk_affine_eq_iff` | 2216-2247 | **(Phase 2, M1.0b — THE SCHUR-RING CHARACTERIZATION)** Two pairs lie in the same orbital of `affineG G₀` ⟺ some `g₀ ∈ G₀` carries the difference `e⁻¹y′−e⁻¹x′` to `e⁻¹y−e⁻¹x`. I.e. relations of `affineScheme` ↔ `G₀`-orbits on `V` (differences) — the "translation scheme = orbit Schur ring `A(G₀)`" identity. The bridge M1's block ⟺ invariant-subspace argument runs on. | — |
| `affineScheme_rel_iff` | 2264-2269 | **(Phase 2, M1.1a)** A pair `(x,y)` lies in relation `i` of `affineScheme` ⟺ `orbitalIdx i = orbMk x y`. Unfolds the orbital-scheme `decide` `rel` field. | — |
| `affineScheme_relOfPair` | 2271-2276 | (Phase 2, M1.1a) `relOfPair x y = orbitalIdx.symm (orbMk x y)` — the relation index is the pair's orbital. | — |
| `affineScheme_relOfPair_eq_iff` | 2278-2286 | **(Phase 2, M1.1a)** Two pairs share a relation ⟺ they share an orbital (`relOfPair`-level form of `orbMk_affine_eq_iff`, via `orbitalIdx.symm` injective). | — |
| `G₀Irreducible` | 2288-2293 | **(Phase 2, M1.1b)** `G₀` acts irreducibly: the only `G₀`-invariant subspaces of `F_p^d` are `⊥`/`⊤`. Self-contained (no `IsSimpleModule`). The hypothesis M2's recovery argument consumes. | Definition |
| `affineRelDiff` | 2295-2300 | (Phase 2, M1.2 helper) The difference `y₀−x₀` of relation `i`'s representative pair. Well-defined as a `G₀`-orbit (`affineRelDiff_mem_iff`). | Definition, `noncomputable` |
| `affineRelDiff_zero` | 2302-2316 | (Phase 2, M1.2 helper) The diagonal relation `R₀` has difference `0` (representative pair `(v,v)`, via `rel_zero_iff_eq`). | — |
| `affineRelDiff_mem_iff` | 2318-2343 | **(Phase 2, M1.2 — the well-definedness lemma)** For a `G₀`-invariant `W`, `affineRelDiff i ∈ W ⟺ (e⁻¹y−e⁻¹x) ∈ W` for any `(x,y) ∈ R_i`. Where invariance does the work: all pairs of `R_i` differ by a `G₀`-translate (`orbMk_affine_eq_iff`), which an invariant subspace cannot tell apart. | — |
| `isPrimitive_affineScheme_imp_irreducible` | 2345-2417 | **(Phase 2, M1.2 — THE BRIDGE, primitive ⟹ `G₀` irreducible)** From a proper `G₀`-invariant subspace `W`, builds the closed subset `I := {i | affineRelDiff i ∈ W}` (block system) — closure via composable-triple differences adding (`exists_composable_of_intersectionNumber` + `W.add_mem`), `≠ {0}`/`≠ univ` from a nonzero `w ∈ W` / a `v ∉ W` — contradicting `IsPrimitive`. The §5.3 "block = sub-structure; primitivity forbids it" template instantiated (`Submodule` ↔ block / `ClosedSubset`). What M3 consumes. Axiom-clean. | — |
| `discrete_affineScheme_of_jointSeparates` | 2419-2437 | **(Phase 2, M2-B — affine depth-1 discreteness, `G₀`-orbit-of-difference form)** Specializes `discrete_of_jointProfileSeparates` to `affineScheme`: if individualizing `T` makes the `G₀`-orbits of the differences `(u−t)_{t∈T}` jointly separate `V` (`∀ u u'`, if `∀ t∈T, ∃ g₀∈G₀, g₀(e⁻¹u′−e⁻¹t)=e⁻¹u−e⁻¹t` then `u=u'`), then `warmRefine` from `T` is `Discrete`. The finite, checkable **depth-1 affine separability** target the probe measures; with `stablyRecoverable_of_discrete` + `selfDetectsStably_of_discretizes` discharges the seal for any depth-1-separating primitive small affine residual. Open remainder = its iterated (`s(C)≥2`) version. | — |
| `affineScheme_relOfPair_translation` | 2439-2450 | **(F2a — translation-invariance, the depth-2 → coset bridge)** `relOfPair t z` depends only on the difference `e⁻¹z − e⁻¹t` — it equals the relation of that difference from the origin (`g₀ = 1`). So the depth-2 profile `(relOfPair t z)_{t∈T}` is exactly **multi-coset membership** `(e⁻¹z − e⁻¹t ∈ C_·)_{t∈T}` — the object the Frobenius `s(C)` count lives in. Axiom-clean. | — |
| `discrete_affineScheme_of_twoRoundDiffSeparates` | 2452-2496 | **(F2a — the depth-2 affine discreteness producer, difference/coset form)** Specializes the general depth-2 engine `discrete_of_twoRoundRelationSeparates` to `affineScheme`, rewriting (via `affineScheme_relOfPair_translation`) the relation conditions as **difference-relation** conditions: if for every difference profile `ρ` and tail `b` the multi-coset-intersection counts separate `u, u'` only when `u = u'`, then `warmRefine` from `T` is `Discrete`. The clean **multi-coset-intersection injectivity** target the Frobenius `s(C)` bound (F2b) discharges; what `Probe_RoundsToDiscrete_Cyclotomic` measures. Axiom-clean. | — |
| `reachesRigidOrCameron_viaAffineIrreducible` | 2498-2534 | §S-gate2 **(E3 — the seal on irreducible affine residuals; CONDITIONAL.)** Specializes `…viaFusedSeal` to `affineScheme G₀`, reducing the seal on **all irreducible affine** residuals to one open hypothesis `hbound` (*irreducible `G₀` ∧ small ⟹ a bounded individualization discretizes* = the cyclotomic/Schur-ring `s(C)` target). Carries `{G3 + hImprim + open hbound}`; not 'seal closed for affine'. Axiom-clean. | — |
| `efield` | 3355-3358 | Phase 2 / F0: the field basis isomorphism `F_q ≃ₗ[ZMod p] F_p^d` (`q = p^d`), from `GaloisField.finrank = d`; carries the cyclic instance from `GaloisField p d` to the coordinate space. | Definition, `noncomputable` |
| `mulUnitHom` | 3360-3369 | F0: multiplication-by-a-unit as an `F_p`-linear automorphism of `F_q`, packaged as a **monoid hom** `F_qˣ →* (F_q ≃ₗ F_q)` (so `σ^k` reduces to `α^k` via `map_zpow`). | Definition, `noncomputable` |
| `conjHom` | 3375-3381 | F0: conjugation by `efield` as a **monoid hom** `(F_q ≃ₗ F_q) →* (F_p^d ≃ₗ F_p^d)`; transports `mulUnitHom α` to the coordinate-space generator `σ`. | Definition, `noncomputable` |
| `fqGen` | 3387-3389 | F0: a chosen multiplicative generator of the cyclic group `F_qˣ`. | Definition, `noncomputable` |
| `fqGen_spec` | 3391-3392 | F0: `fqGen` generates `F_qˣ` (every unit is in `zpowers fqGen`). | — |
| `sigmaCyc` | 3394-3396 | F0: `σ` — multiplication by `fqGen`, transported to `F_p^d`; the generator of the cyclic `G₀`. | Definition, `noncomputable` |
| `G0cyc` | 3398-3400 | F0: the cyclic affine group `G₀ = ⟨σ⟩ ≤ GL(F_p^d)` (the cyclotomic Singer subgroup). | Definition, `noncomputable` |
| `neg_mem_G0cyc` | 3422-3429 | F0: **`hneg`** for the cyclic instance — `neg ∈ G0cyc` (since `-1 = α^k`, `neg = σ^k`); supplies `affineScheme`'s symmetry hypothesis. | — |
| `G0cyc_irreducible` | 3431-3462 | F0: **`G₀Irreducible (G0cyc)`** — EARNED via the multiplicative-orbit argument (a `σ`-invariant nonzero subspace contains a full `F_qˣ`-orbit = all nonzero elements ⟹ `⊤`); no `IsSimpleModule`/`F_p[α]=F_q` algebra needed. | — |
| `cyclicAffineScheme` | 3464-3471 | F0: the **cyclic affine scheme** — `affineScheme` at `G0cyc`; a genuinely primitive, symmetric, small affine instance (the cyclotomic beachhead the Frobenius `s(C)` bound F2b and the affine probe target). | Definition, `noncomputable` |
| `frobLinear` | 3483-3496 | F1: Frobenius `x ↦ x^p` as a `ZMod p`-**linear** automorphism of `F_q` (linear since `c^p = c` on the prime field); the algebraic automorphism witnessing the `Ĝ ⊋ G` separability gap. | Definition, `noncomputable` |
| `frobCoord` | 3518-3521 | F1: Frobenius transported to `F_p^d` — an element of `GL(d,p)` (the linear part of a Galois twist of the affine group). | Definition, `noncomputable` |
| `frobCoord_conj_sigmaCyc` | 3523-3529 | F1: **the normalizing relation** `frobCoord · σ · frobCoord⁻¹ = σ^p` — Frobenius normalizes `G0cyc = ⟨σ⟩` but lies in it only when `φ ∈ ⟨σ⟩`; in general `⟨σ, frobCoord⟩ = ΓL(1,q) ⊋ ⟨σ⟩`, the `Ĝ ⊋ G` gap, here finite and explicit. **General-theorem shadow:** an algebraic automorphism not in the group = what the `s(C)` leak is in general. | — |
| `CyclicAffineSeparates` | 3541-3560 | **(F2b frame — the single open crux as a named proposition)** A bounded `T` whose depth-2 **difference profile** is injective (multi-coset-intersection counts separate every vertex pair) = the Frobenius `s(C)` bound. **OPEN** — the probe-confirmed but uncited counting core. | Definition |
| `reachesRigidOrCameron_viaCyclicSeparation` | 3562-3595 | **(F2b frame — the seal on the cyclic-affine family reduced to `CyclicAffineSeparates`; A CONDITIONAL CAPSTONE)** Instantiates `reachesRigidOrCameron_viaAffineIrreducible` at `G₀ = G0cyc`, discharging `hbound` from `CyclicAffineSeparates` via `discrete_affineScheme_of_twoRoundDiffSeparates`. **⚠️ Carries `hClassify` (G3) + `hne`/`hrank` (per-instance) + `hImprim` + the OPEN `hsep : CyclicAffineSeparates`.** Closing the seal on this family ⟺ proving `CyclicAffineSeparates`, open `s(C)` math. Not "seal closed for cyclic." Axiom-clean. | — |
| `sigmaPow` | 3610-3614 | **(F2b target correction)** `σ_β` — multiplication by an arbitrary unit `β`, transported to `F_p^d`; generalizes `sigmaCyc` (`= sigmaPow fqGen`). | Definition, `noncomputable` |
| `G0pow` | 3616-3620 | **(F2b target correction)** the cyclic affine group `G₀ = ⟨mul β⟩` for arbitrary `β` — the **proper-subgroup / genuine cyclotomic** case when `β = α^m` (vs `G0cyc = G0pow fqGen` = the degenerate rank-2 `K_q`). Generalizes `G0cyc`. | Definition, `noncomputable` |
| `neg_mem_G0pow` | 3630-3639 | F2b: **`hneg`** for the proper cyclic instance — `neg ∈ G0pow β` when `-1 ∈ ⟨β⟩`. Generalizes `neg_mem_G0cyc`. | — |
| `G0pow_irreducible` | 3641-3680 | **(F2b target — `G₀Irreducible (G0pow β)` via FIELD-GENERATION; the §5.3 subfield template)** If `span_{F_p}{β^k} = ⊤` (`β` field-generates `F_q`), then `⟨mul β⟩` is irreducible: a `mul·β`-invariant nonzero `W` contains `f '' {β^k}` (`f : c ↦ efield(x₀·c)`, `x₀ = e⁻¹w₀`), which spans `⊤` (since `span{β^k} = ⊤` and `f` surjective), so `W = ⊤`. The **proper-subgroup** irreducibility the orbit argument (`G0cyc_irreducible`) could not give — the genuine cyclotomic case. The §5.3 "invariant subspace ⟺ subfield" instance. Axiom-clean. | — |
| `G0pow_irreducible_of_adjoin` | 3682-3695 | **(F2b witness — bridge)** `G₀Irreducible (G0pow β)` from the clean hypothesis `Algebra.adjoin (ZMod p) {β} = ⊤` (β field-generates), via `Algebra.adjoin_eq_span` (adjoin's submodule = span of powers). The form a concrete witness discharges. | — |
| `affineDepth2Count` | 4062-4075 | **(F2b — the depth-2 count, factored)** The depth-2 difference (multi-coset-intersection) count for vertex `u` over `affineScheme (G0pow hd β)` at relation-profile `ρ` and relation `b`: `#{z ≠ u : (∀ t∈T, diff-rel(z,t)=ρt) ∧ diff-rel(z,u)=b}` (= `|⋂_t(t+C_{ρt}) ∩ (u−C_b)|`). Factored out of `PowAffineSeparates`/`TwinsAreFrobenius` so they share one count. Axiom-clean. | Definition, `noncomputable` |
| `PowAffineSeparates` | 4077-4086 | **(F2b crux, genuine target)** The depth-2 difference (multi-coset-intersection) profile is injective over `affineScheme (G0pow hd β)` from some bounded base `T`. The `G0pow` analogue of `CyclicAffineSeparates`, stated over the **rank-≥3 leak candidate** (proper `β = α^m`) rather than the degenerate rank-2 `K_q` (`G0cyc`). The Frobenius `s(C)` bound for the genuine cyclotomic scheme — the open uncited core (F2b); `relOfPair_frobPerm_hom` is its step 1. | Definition |
| `reachesRigidOrCameron_viaPowSeparation` | 4088-4118 | **(F2b seal capstone, genuine target — ⚠️ CONDITIONAL)** The seal on the genuine cyclotomic family `affineScheme (G0pow hd β)`, reduced to the single crux `PowAffineSeparates`. Re-targets `reachesRigidOrCameron_viaCyclicSeparation` from the degenerate rank-2 `K_q` (`G0cyc`) to the rank-≥3 leak candidate where the Frobenius work + `clebschWitness_irreducible` live. Instantiates `reachesRigidOrCameron_viaAffineIrreducible` at `G₀ := G0pow hd β`. Carries `hClassify` (G3), `hne`/`hrank`, `hImprim` (earned), and the **open** `hsep : PowAffineSeparates`. Axiom-clean. | — |
| `adjoin_eq_top_of_orderOf` | 4120-4169 | **(F2b witness — the finite-field core, reusable)** Field-generation from element order: if `β ∈ F_qˣ` has order `r` and no *proper* divisor `e ∣ d` has `r ∣ p^e − 1`, then `Algebra.adjoin (ZMod p) {↑β} = ⊤`. Proof: `K' = F_p⟮β⟯` is a subfield of size `p^e` (`e = finrank ∣ d`) containing order-`r` `β`, so `β^(p^e)=β` ⟹ `r ∣ p^e−1`, forcing `e=d`, `K'=⊤`. Axiom-clean. | — |
| `orderOf_fqGen` | 4171-4176 | F2b witness: the generator `fqGen` has order `p^d − 1` (`= |F_qˣ|`). | — |
| `G0pow_pow_irreducible` | 4178-4186 | **(F2b witness family)** `G0pow (fqGen^m)` is irreducible whenever `fqGen^m` has order `r` field-generating (no proper `e∣d` has `r∣p^e−1`). For *proper* `m` (so `⟨fqGen^m⟩ ⊊ F_qˣ`) = the genuine rank-≥3 cyclotomic leak candidate (vs `G0cyc = G0pow fqGen` = rank-2 `K_q`). | — |
| `frobCoord_conj_sigmaPow` | 4212-4216 | (separation step 1) `frobCoord · σ_β · frobCoord⁻¹ = σ_β^p` (generalizes `frobCoord_conj_sigmaCyc`) — so `frobCoord` normalizes `G0pow β = ⟨σ_β⟩`. | — |
| `frobCoord_conj_mem_G0pow` | 4218-4227 | (separation step 1) **`frobCoord` normalizes `G0pow β`**: `g ∈ G0pow β ⟹ frobCoord·g·frobCoord⁻¹ ∈ G0pow β` (conjugation maps `σ^k ↦ σ^{pk}`). | — |
| `frobPerm` | 4229-4232 | (separation step 1) the **Frobenius permutation** of `V = F_p^d` — `frobCoord` transported to `Fin (p^d)` (additive, zero translation). | Definition, `noncomputable` |
| `affineE_symm_frobPerm` | 4234-4237 | (separation step 1) `e⁻¹(frobPerm x) = frobCoord (e⁻¹ x)` — Frobenius is additive on difference-coordinates. | — |
| `relOfPair_frobPerm_hom` | 4239-4257 | **(SEPARATION STEP 1 — the `Ĝ ⊋ G` configuration automorphism)** `frobPerm` preserves the scheme's relation partition: `relOfPair x y = relOfPair x' y' → relOfPair (frobPerm x)(frobPerm y) = relOfPair (frobPerm x')(frobPerm y')`. Because `frobCoord` normalizes `G0pow β` and is additive, `frobPerm` is an automorphism of the coherent configuration the group `V ⋊ G0pow β` does NOT realize — the concrete `Ĝ ⊋ G` separability gap, the obstruction the `s(C)` leak exploits. **General shadow:** "a normalizing algebraic automorphism is a configuration automorphism" = the general `s(C)` obstruction shape. Axiom-clean. | — |
| `frobLinear_pow_apply` | 4277-4283 | **(F2b separation step 2 — helper)** `frobLinear^j` acts as `x ↦ x^(p^j)` (iterating Frobenius), by induction on `j`. Axiom-clean. | — |
| `frobLinear_pow_eq_one_of_adjoin` | 4285-4321 | **(F2b separation STEP 2, field core — "Γ-breaking kills Frobenius symmetry")** If `frobLinear^j` fixes every element of `S` and `Algebra.adjoin (ZMod p) S = ⊤` (`S` field-generates `F_q`), then `frobLinear^j = 1`. Proof: the fixed points `{x | x^(p^j) = x}` form a subalgebra (closed under `+` by `add_pow_char_pow`, contains `F_p` by `ZMod.pow_card_pow`), so a generating `S` forces it to `⊤`. The citation-clean half of the remaining separation proof. Axiom-clean. | — |
| `frobCoord_pow_apply` | 4333-4337 | **(F2b step 2 — iso alignment)** `frobCoord^j` is `frobLinear^j` conjugated through `efield` (`= efield (frobLinear^j (efield⁻¹ u))`), via `conjHom` monoid-hom `map_pow`. Aligns the linear part across the field iso. Axiom-clean. | — |
| `affineE_symm_frobPerm_pow` | 4339-4347 | **(F2b step 2 — iso alignment)** `affineE⁻¹ ((frobPerm^j) x) = (frobCoord^j)(affineE⁻¹ x)` — the `j`-fold iterate of `affineE_symm_frobPerm` (frobPerm = additive frobCoord transported, zero translation). Axiom-clean. | — |
| `frobPerm_pow_eq_one_of_adjoin` | 4349-4373 | **(F2b separation STEP 2, on scheme points — the directly-usable form)** If the field coordinates `efield⁻¹(affineE⁻¹ t)` of the base `T` generate `F_q` (Γ-breaking) and `frobPerm^j` fixes `T` pointwise, then `frobPerm^j = 1`. Lifts `frobLinear_pow_eq_one_of_adjoin` to `Fin (p^d)` via the alignment lemmas (resolving the two-iso `affineE`/`efield` alignment). The form step-4 wiring consumes once the open step 3 supplies the fixing `φ^j`. Axiom-clean. | — |
| `clebschWitness_irreducible` | 4545-4550 | **(THE CONCRETE WITNESS)** `G0pow (fqGen³)` over `F₁₆` is irreducible — `β = fqGen³` (order 5) field-generates `F₁₆` (`5 ∤ 2^e−1` for `e ∈ {1,2}`, by `decide`). The index-3 Clebsch family: a genuinely primitive, **proper-subgroup (rank ≥ 3)**, small affine scheme = the real F2b leak candidate (NOT `K₁₆`). Demonstrates the witness machinery is non-vacuous. Axiom-clean. | — |
| `clebschWitness_neg_mem` | 4552-4558 | The Clebsch witness is symmetric — `neg ∈ G0pow (fqGen³)` (free in char 2, `-1 = 1 ∈ ⟨β⟩`). | — |
| `not_isPrimitive_of_nontrivial_closedSubset` | 4581-4591 | **(P3 converse, trivial half)** A non-trivial `ClosedSubset` (`I ≠ {0}`, `I ≠ univ`) refutes `IsPrimitive` (whose only closed subsets are exactly those two). The easy "block ⟹ imprimitive" direction; the content is constructing the block (`PersistentTwinYieldsBlock`). Axiom-clean. | — |
| `SeparatesAtBoundedBase` | 4593-4600 | The engine interface (positive form): ∃ base `S₀`, `|S₀| ≤ bound`, with `warmRefine (schemeAdj S)` from `S₀` `Discrete`. Its negation is a **base-homogeneous twin** (a same-cell pair at every bounded base). The existential `selfDetectsStably_of_discretizes` consumes. | Definition |
| `TwinsRealizedByResidualAut` | 4602-4617 | **The separability sink (warmRefine-local form) — the general Thm-4.1 deliverable.** Every same-`warmRefine`-cell twin `(u,u')` from `T` is realised by a `T`-fixing residual automorphism (`ResidualAut`) carrying `u↦u'`. The §S.17 `Separable` transported into the project's `warmRefine` model, localised at `T`; the general analogue of the affine `TwinsAreSemilinear`. Definitionally `CellsAreOrbits (schemeAdj …) T` (see next). | Definition |
| `separatesAtBoundedBase_of_twinsRealized` | 4619-4635 | **THE SEAL-BRIDGE (Thm-4.1 finding 3): separability sink + bounded group base ⟹ the seal consumer.** `TwinsRealizedByResidualAut T ∧ IsBase T ∧ |T|≤bound ⟹ SeparatesAtBoundedBase S bound`: a twin gives a `T`-fixing aut (separability), an `OrbitPartition` pair the base kills to `u=u'`. General form of the affine `powAffineSeparates_of_twinsAreSemilinear`. Axiom-clean. | — |
| `twinsRealizedByResidualAut_iff_cellsAreOrbits` | 4637-4653 | The separability sink **is** the recovery predicate: `TwinsRealizedByResidualAut S T ↔ CellsAreOrbits (schemeAdj …) T`, via `orbitPartition_iff_residualAut`. Wires the Thm-4.1 sink into all existing recovery infrastructure; pins the transport obligation to `Separable ⟹ CellsAreOrbits at T`. Axiom-clean. | — |
| `PersistentTwinYieldsBlock` | 4655-4668 | **(THE OPEN CRUX — mechanism-agnostic P3 converse / G2-B.)** `¬ SeparatesAtBoundedBase → large ∨ ∃ nontrivial ClosedSubset`: a base-homogeneous twin forces a block (→ imprimitive) unless large (→ Cameron). The seal's sole irreducible open content, restated as a positive block-construction — `Discrete`/`ClosedSubset`-only, **no Frobenius/spectral substrate**, general over any `SchurianScheme`. Uncited open math, carried visibly. Realization half (`no twin ⟹ separates`) landed as `discrete_of_kRoundRelationSeparates`. | Definition |
| `selfDetectsStably_of_persistentTwinYieldsBlock` | 4670-4686 | **(The reduction — provable.)** `PersistentTwinYieldsBlock ⟹ SelfDetectsStably`: for a primitive small residual, persistent non-separation yields large (contradicts small) or a block (contradicts primitive), so some bounded base discretizes. Mirror of `selfDetectsStably_of_depthOneSeparable`, P3-converse crux in the slot. Axiom-clean. | — |
| `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive` | 4688-4712 | On a primitive scheme the block disjunct of `PersistentTwinYieldsBlock` is vacuous (no nontrivial proper `ClosedSubset`), so the open crux collapses to the largeness-only form `¬SeparatesAtBoundedBase → IsLarge` — the fusion/closed-subset (`schemeEquiv_trans`) discharge cannot close the primitive floor (only the imprimitive case, already `hImprim`); the primitive crux is irreducibly the 2-closure/`s(X)` wall. | — |
| `reachesRigidOrCameron_viaPersistentTwinBlock` | 4714-4741 | **(Phase-2 headline — CONDITIONAL.)** The fused seal with self-detection discharged via the general P3-converse crux `hCrux`. Carries `hClassify` (G3), `hImprim`, and the **open** `hCrux` (G2-B). Routes the primitive floor through the *general*, mechanism-agnostic crux, replacing the retracted Frobenius-specific `PowAffineSeparates` path. Axiom-clean. | — |
| `schemeRecoveredByDepth_of_separatesAtBoundedBase` | 4743-4754 | **Separation at a bounded base ⟹ depth-graded recovery (the positive bridge).** A bounded base whose warm refinement is `Discrete` recovers the scheme at that depth: `stablyRecoverable_of_discrete` (discrete ⟹ every cell a singleton ⟹ trivially an orbit at every `T ⊇ S₀`) then `schemeRecoveredByDepth_of_stablyRecoverable`. The *positive* form of the recovery content — where `PersistentTwinYieldsBlock` derives separation by refuting a persistent twin (the open crux), this consumes separation supplied **outright** (a discretization citation, e.g. Spielman, or the δ′ engine). Axiom-clean. | — |
| `reachesRigidOrCameron_viaSpielman` | 4756-4789 | **THE SEAL VIA SPIELMAN — the citable sub-exponential floor (scope CORRECTED 2026-07-16).** Carries the single hypothesis `hSpielman : SeparatesAtBoundedBase S bound` (the residue individualizes a `≤bound` base to `Discrete`); the seal holds via the rigid branch outright (`Or.inl (Or.inr …)` of `schemeRecoveredByDepth_of_separatesAtBoundedBase`). **Carries ONLY `hSpielman` — no G3 (`hClassify`), no `hImprim`, no largeness/Cameron routing.** Citation scope: Spielman STOC 1996 / BCSTW FOCS'13 give the `Õ(n^{1/3})` (resp. `n^{1/5}`) base for **claw-bounded** primitive SRGs only — the Neumaier-exceptional Steiner/Latin-square families (`T(m)`, `L₂(m)`) have base `Θ(√n)`, so `hSpielman` is FALSE there and those exit via the Cameron branch (see the corrected docstring). Imprimitive = block tower, conference = leg B. `Õ(n^{1/3})` is the floor (claw-bounded); `O(log n)` is the open rank-3 base case (node 4, no citation). Does **not** close the polynomial seal. Axiom-clean. | — |
| `intraCellRelations` | 4803-4812 | The scheme relations `R_k` entirely inside the `warmRefine (schemeAdj S)`-from-`S₀` cells (every `R_k`-pair shares a cell colour). Discrete base ⟹ `{R₀}`; one-cell base ⟹ everything; in between = the block candidate for the P3 converse. | Definition, `noncomputable` |
| `mem_intraCellRelations` | 4814-4823 | Membership unfolding for `intraCellRelations`: `k ∈ … ↔ ∀ x y, rel k x y → warmRefine x = warmRefine y`. | — |
| `intraCellRelations_isClosed` | 4825-4847 | **(THE CONVERSE'S PROVABLE CORE — the fusion closure.)** `intraCellRelations S S₀` is a `ClosedSubset`: `R₀` intra-cell (diagonal reflexive); composites stay intra-cell via `intersectionNumber_well_defined` (extract the intermediate `y`) + transitivity of cell-equality. Generalizes `schemeEquiv_trans` to the whole intra-cell set = the WL-stable-congruence ⟹ closed-subset fact. Any `AssociationScheme` (no schurity/Frobenius). Axiom-clean. | — |
| `intraCellRelations_ne_univ_of_sep` | 4849-4863 | **(Properness, free.)** A base containing `t` with any `w ≠ t` makes `intraCellRelations ≠ univ`: `relOfPair t w` crosses cells since `t` keeps a unique individualized colour (`individualizedColouring_mem_sep`) that `warmRefine` only refines (`warmRefine_refines`). So the `≠ univ` half is automatic; the open residue is nontriviality alone. Axiom-clean. | — |
| `intraCellRelations_eq_singleton_zero_of_primitive` | 4865-4881 | **(The intra-cell route's boundary.)** For a *primitive* scheme and any base individualizing a point (`t ∈ S₀`, `w ≠ t`), `intraCellRelations S S₀ = {0}` identically: it's a `ClosedSubset` (`intraCellRelations_isClosed`) so primitivity forces `{0}`/`univ`, and `≠ univ` is free (`intraCellRelations_ne_univ_of_sep`). So the intra-cell block can never witness the nontriviality kernel on the primitive floor — it discharges only the imprimitive case; the open G2-B floor needs a non-congruence object (the amorphic WL-fusion), not a block. Axiom-clean. | — |
| `PersistentTwinGivesIntraCellBlock` | 4883-4897 | **(The sharpened open kernel — G2-B isolated to nontriviality.)** Persistence (`¬ SeparatesAtBoundedBase`) ⟹ large, or a bounded base whose `intraCellRelations` is `≠ {0}` and `≠ univ`. `PersistentTwinYieldsBlock` with the `ClosedSubset` construction (and `≠ univ`) discharged, so the *only* open content is nontriviality `≠ {0}` (a persistent twin gives a **whole** intra-cell non-diagonal relation, not one pair). Carried visibly. | Definition |
| `persistentTwinYieldsBlock_of_intraCellBlock` | 4899-4910 | **(The reduction — provable.)** `PersistentTwinGivesIntraCellBlock ⟹ PersistentTwinYieldsBlock`; the block *is* `intraCellRelations S S₀` (closed by `intraCellRelations_isClosed`, nontrivial+proper by the kernel). Banks the fusion-closure core of the P3 converse. Axiom-clean. | — |
## ChainDescent/Saturation.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Saturation.iterate_subset_succ` | 37-41 | One iterate of an extensive operator is contained in the next. | — |
| `Saturation.iterate_mono` | 43-51 | Iterates of an extensive operator are monotone in the step count. | — |
| `Saturation.iterate_eq_of_isFixed` | 53-58 | Once a fixpoint is reached, further iteration is inert. | — |
| `Saturation.iterate_subset_of_invariant` | 60-65 | Iterates stay inside any `f`-invariant set containing the seed. | — |
| `Saturation.iterate_subset_of_invariant'` | 67-81 | **Interval-invariant containment.** Iterates of an extensive `f` stay inside a bound `B` when `f` preserves `B` only on the `f`-reachable sets `s₀ ⊆ s ⊆ B` — the weakened hypothesis Leg A's support induction needs. | — |
| `Saturation.exists_iterate_isFixed_within'` | 97-124 | **Saturation within a bound, interval-invariant form.** As `exists_iterate_isFixed_within` but invariance is required only on the `f`-reachable sets `s₀ ⊆ s ⊆ B`; yields the tight `base(g) ≤ |support|` depth for the moved-vertex closure. | — |
| `Saturation.exists_iterate_isFixed_within` | 126-140 | **Saturation within a bound (the general form).** An extensive operator preserving a bound `B ⊇ s₀` reaches a fixpoint within `|B| − |s₀|` steps from `s₀`; the form scheme convergence uses with `B = occursFromV` (depth `≤ n`) and Leg A uses with `B` the support set. | — |
| `Saturation.exists_iterate_isFixed` | 142-150 | **Saturation.** Iterating an extensive operator from `s₀` reaches a fixpoint within `|α| − |s₀|` steps — the `B = univ` case of `exists_iterate_isFixed_within`. | — |
## ChainDescent/CascadeAffine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `numCells` | 38-39 | §S-stab Number of cells (distinct colours) of a `Colouring`, `(univ.image χ).card` — the monovariant for warmRefine stabilization. | Definition |
| `refineStep_samePartition` | 41-53 | §S-stab One `refineStep` round preserves `samePartition`: the refined partition depends only on the current partition, not the colour labels. | — |
| `numCells_le_of_refines` | 65-74 | §S-stab Refinement does not increase the cell count: `Refines χ₁ χ₂ → numCells χ₂ ≤ numCells χ₁`. | — |
| `samePartition_of_refines_of_numCells_le` | 76-100 | §S-stab A refinement that doesn't grow the cell count is partition-trivial. | — |
| `numCells_lt_of_not_samePartition` | 102-108 | §S-stab A non-trivial refinement strictly increases the cell count. | — |
| `numCells_le` | 110-114 | §S-stab The cell count is at most `n`. | — |
| `numCells_pos` | 116-120 | §S-stab With at least one vertex, every colouring has at least one cell. | — |
| `numCells_iter_bound` | 122-141 | §S-stab Cell-count growth bound: if the refinement chain strictly refines at every step below `k`, `numCells` grows by at least `k`. | — |
| `exists_samePartition_step` | 143-151 | §S-stab The refinement chain reaches a plateau (`samePartition` between consecutive rounds) within the first `n` steps — pigeonhole on the bounded, monotone cell count. | — |
| `samePartition_step_stable` | 153-166 | §S-stab Once the refinement chain plateaus it stays put — a `refineStep`-fixpoint up to partition is stable forever. | — |
| `warmRefine_refineStep_samePartition` | 168-179 | **Stabilization (the PV-bridge prerequisite).** `warmRefine` is a `refineStep`-fixpoint up to partition (one more round splits no cell), letting the bridge read signatures one round past `warmRefine` where a `Determined` vertex's colour is already unique. | — |
| `relOfPair_eq_of_warmRefine_determined` | 192-240 | **B1.** Relation to a *determined* point is cell-determined: if `x` is in a singleton `warmRefine` cell, same-cell `w,u` satisfy `relOfPair x w = relOfPair x u`. The determined-point analogue of `relOfPair_eq_of_warmRefine_singleton`. | — |
| `determined_of_mem_individualized` | 242-253 | **B2.** The base case: every `t ∈ T` sits in a singleton `warmRefine` cell after individualising `T` — the seed of the PV propagation. | — |
| `determined_of_saAdj` | 255-288 | **B3 — forced-triangle propagation (PV Lem 3.2).** `Determined α ∧ Determined β ∧ saAdj α β γ ⟹ Determined γ`: the rigid `c=1` triangle pins `γ` from its relations to two determined points. | — |
| `determined_of_forcedTriangle` | 290-328 | **B3′ — the forced-triangle step, smax-free (the δ′ engine's primitive).** `Determined α ∧ Determined β ∧ c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1 ⟹ Determined γ`: the content of `determined_of_saAdj` with `saAdj`'s `smaxAdj` conjuncts stripped (the proof discarded them, using only the intersection-number-`=1` fact). The general `c=1` two-endpoint dominator pinning, valid off the maximal-valency locus — exactly the step the catch-up probe-gate found discretizes from every minimal base of the dense residue. | — |
| `DeterminedAt` | 334-338 | §S-bridge A vertex sits in a singleton `warmRefine` cell (PV's Γ — a singleton fiber of the point extension); the bridge's propagation predicate. | `abbrev` |
| `determinedAt_of_reflTransGen` | 340-346 | **B4a.** Determinacy propagates along an `sα`-path (iterate B3 over `ReflTransGen (saAdj α)`). | — |
| `determinedAt_of_smaxAdj` | 348-353 | **B4b (PV claim (17)).** If some `αsmax`-neighbour of `α` is determined, all of `αsmax` is — via `SaConnected`. | — |
| `discrete_of_connectivity` | 355-382 | **B4 — PV Lem 3.3 (Γ=Ω).** An `smaxAdj` edge + `SmaxConnected` + all `SaConnected` ⟹ individualising the edge makes `warmRefine` `Discrete` (seed determined, spread across `αsmax`, then to all of Ω by `smax`-closure). | — |
| `separatesAtBoundedBase_of_connectivity` | 384-395 | **B5 — the bridge, packaged for the seal.** `smax`/`sα` connectivity at a maximal-valency edge ⟹ `SeparatesAtBoundedBase S 2`, the `PersistentTwinYieldsBlock` / `reachesRigidOrCameron` consumer. | — |
| `separatesAtBoundedBase_of_sparseSeparable` | 397-423 | **PV Theorem 3.1 (the sparse on-ramp), complete.** `SparseSeparable ∧ k≥2 ⟹ SeparatesAtBoundedBase S 2` — the full combinatorial `b(X)≤2`, both connectivity legs discharged from sparsity and wired to the seal consumer. | — |
| `DominatorReachable` | 440-450 | §S-bridge-δ **The forced-triangle closure of a base `T`** — the least set of points reachable from `T` by iterating the `c=1` two-endpoint dominator step (`base`: every `t∈T`; `step`: `γ` pinned by a rigid coloured triangle against two reachable `α,β`). The smax-free, dense-side generalisation of PV's `sα`-path reachability; `DominatorReachable S T = Ω` is the structural hypothesis the probe-gate verified at every minimal base of the residue. | Inductive |
| `interNum_eq_one_of_forcedUnique` | 452-473 | §S-bridge-δ **The general forced-triangle criterion (any scheme).** `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` exactly when `γ` is the unique `u` with `r(α,u)=r(α,γ) ∧ r(u,β)=r(γ,β)` — the forced-triangle filter `{u : …}` always contains `γ` (`rel_relOfPair`) and `=1` collapses it to `{γ}`. The scheme-agnostic core; `affineScheme_interNum_eq_one_of_unique` is its orbit-difference specialisation. Axiom-clean. | — |
| `dominatorReachable_step_of_unique` | 475-485 | §S-bridge-δ **The general `DominatorReachable` step builder (any scheme).** Two reachable points + the `relOfPair`-profile uniqueness pinning `γ` ⟹ `γ` reachable. Subsumes `dominatorReachable_affine_step` (its orbit-difference `huniq` unfolds to this) and covers non-affine residues directly; with `DominatorReachable.base` the scheme-agnostic closure-derivation toolkit. Axiom-clean. | — |
| `dominatorReachable_step_of_stab` | 487-508 | §S-bridge-δ **The schurian forced-triangle criterion — the `Stab(α)·γ ∩ Stab(β)·γ = {γ}` reading.** On a schurian scheme, `relOfPair`-profile equality is a point-stabiliser-orbit relation (schurian axiom), so `γ` is pinned by `α, β` exactly when the only point in both `Stab(α)·γ` and `Stab(β)·γ` is `γ`. Builds a step from the stabiliser-orbit `huniq` — the geometric handle for the single-base closure (a base has `⋂ Stab(t) = 1`). Axiom-clean. | — |
| `dominatorReachable_of_rank` | 510-540 | §S-bridge-δ **The single-base closure from a well-founded pinning rank (the δ′ iteration engine).** To prove `∀ v, DominatorReachable S T v` it suffices to give `rank : Fin n → ℕ` with every rank-`0` point in `T` and every positive-rank `γ` forced-triangle-pinned by two strictly-lower-rank points. Strong induction on rank. The missing brick between the step builders (`dominatorReachable_step_of_unique`/`_of_stab`/`_affine_step`) and the consumer (`separatesAtBoundedBase_of_dominatorClosure`): reduces the family-level open content from "closure exhausts Ω" to the checkable "exhibit a pinning rank" — the clean sufficient condition the δ′ Stage-3 endpoint targets. Axiom-clean. | — |
| `dominatorReachable_of_basePinsAll` | 542-569 | §S-bridge-δ **One-round closure (the cleanest checkable sufficient condition).** If every non-base point `γ` is forced-triangle-pinned by *two base points* `α,β ∈ T`, then the dominator closure of `T` exhausts Ω in one round: `∀ v, DominatorReachable S T v`. The `rank ∈ {0,1}` instance of `dominatorReachable_of_rank` — the simplest discharge of the seal's `hclo`, for the odd-char / non-midpoint regime (char-2 residues need genuine multi-round). Axiom-clean. | — |
| `dominatorReachable_of_rank_interNum` | 571-596 | §S-bridge-δ **The `interNum`-keyed pinning-rank engine (general public form of `ClebschConcrete`'s private `domReach_of_rank_pin`).** Like `dominatorReachable_of_rank` but the per-level pinning is the `decide`-friendly Nat-equality `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` directly (no nested-implication `huniq`, which has no synthesizable `Decidable`). The form concrete schemes (`decide`) and the rainbow-rigid family (counting) discharge through. Axiom-clean. | — |
| `RainbowRigid` | 598-607 | §S-bridge-δ **Rainbow rigidity** — the structural pinning mechanism the ℤ₄² Clebsch probe extracted: every *rainbow* triangle (three pairwise-distinct non-diagonal edge colours) has `≤ 1` common neighbour, hence is forced (`c=1`). The operational form of "the indistinguishing number `c(X)` is small / forced triangles abundant" (build doc §1B). Carried as a hypothesis (a structural property of the `(16,5,0,2)` parameter family), never an `axiom`. | Definition |
| `interNum_eq_one_of_rainbow` | 609-627 | §S-bridge-δ **A rainbow triangle is forced.** Under `RainbowRigid`, a triangle `(α,γ,β)` with three pairwise-distinct non-diagonal edge colours pins `γ`: `interNum = 1` (`≤1` from rigidity, `≥1` because `γ` realises the triangle). The bridge from the combinatorial rainbow colour condition to the δ′ `interNum = 1` pinning premise. Axiom-clean. | — |
| `dominatorReachable_of_rainbowRank` | 629-648 | §S-bridge-δ **The rainbow-rigid FAMILY closure (δ′) — lifts `clebschZ4_closure` from one scheme to the rainbow-rigid family.** A `RainbowRigid` scheme with a *rainbow rank* (rank-0 in `T`; every positive-rank `γ` reached by a rainbow triangle against two strictly-lower-rank points) has its forced-triangle closure exhaust Ω. Per-point pinning is now a purely combinatorial colour condition; the `c=1` arithmetic is supplied once by `interNum_eq_one_of_rainbow`. Remaining open content for a family = (a) `RainbowRigid` + (b) a rainbow rank from a bounded base = the operational `c(X_T)`-boundedness of §1B. Axiom-clean. | — |
| `determinedAt_of_dominatorReachable` | 650-658 | §S-bridge-δ **Every dominator-reachable point is determined.** Induction over `DominatorReachable`: base = B2 (`determined_of_mem_individualized`), step = B3′ (`determined_of_forcedTriangle`). The bridge from combinatorial reachability to the WL-singleton-cell fact. | — |
| `discrete_of_dominatorClosure` | 660-669 | §S-bridge-δ **The δ′ engine — closure exhausts Ω ⟹ discrete.** If every vertex is dominator-reachable from `T`, individualising `T` discretises the scheme. Citation-free, dense-side analogue of `discrete_of_connectivity` (which got universal determinacy from `smax`/`sα` connectivity); here it is the named structural hypothesis the family-level math discharges. | — |
| `separatesAtBoundedBase_of_dominatorClosure` | 671-680 | §S-bridge-δ **δ′ packaged for the seal consumer.** A base `T` of size `≤ bound` whose forced-triangle closure exhausts Ω discretises the scheme: `SeparatesAtBoundedBase S bound`. The citation-free sibling of `separatesAtBoundedBase_of_connectivity` / `…_of_extensionPointed` — lands directly on the consumer with **no** group base, no CC-extension, no catch-up. Axiom-clean. | — |
| `dominatorReachable_map` | 682-695 | §S-bridge-δ **The dominator closure is scheme-automorphism-equivariant.** A scheme automorphism `π` mapping base `T` into `T'` maps `T`-reachable points to `T'`-reachable points. Induction over `DominatorReachable`: base = `hT`; step survives because `IsSchemeAut.relOfPair_eq` makes the forced-triangle intersection-number premise `π`-invariant. The structural fact reducing "closure exhausts Ω" to one base per automorphism-orbit. Axiom-clean. | — |
| `dominatorReachable_univ_image` | 697-708 | §S-bridge-δ **Complete dominator closure transports across automorphic base images.** If base `T`'s closure exhausts Ω and `π` is a scheme automorphism, the image base `T.image π` also has complete closure. For a vertex-transitive residue, proving `∀ v, DominatorReachable S T v` for ONE base discharges the whole `Aut(S)`-orbit of bases — the family-argument leverage. Axiom-clean. | — |
| `SeparabilityTransports` | 733-743 | **The seal-bridge transport obligation (B) — the open content Thm 4.1 must clear.** `S.toAssociationScheme.Separable → TwinsRealizedByResidualAut S T` (= `Separable ⟹ CellsAreOrbits at T` = EP fact `s(X)=1 ⟹ b(X)≤b(G)`). NOT automatic: §S.17 `Separable` is relation-level on homogeneous `X`, the twin lives in the multi-fiber extension `X_T` — its proof needs general-CC separability (the live build, `chain-descent-general-cc-separability.md`). | Definition |
| `separatesAtBoundedBase_of_separable` | 745-755 | **The seal-bridge anchored on Thm 4.1's output.** (A) `Separable` + (B) the transport `SeparabilityTransports T` + (C) a bounded group base `IsBase T` ⟹ `SeparatesAtBoundedBase S bound`. Composes the transport into `separatesAtBoundedBase_of_twinsRealized`. Axiom-clean. | — |
| `card_foldl_insert_le` | 757-767 | Helper: folding `insert` over a list grows a `Finset` by at most the list length (`(bs.foldl insert T).card ≤ T.card + bs.length`). Bounds the greedy base size by `log₂|Aut|` in `separatesAtBoundedBase_of_separable_of_small`. | — |
| `separatesAtBoundedBase_of_separable_of_small` | 769-790 | **The seal-bridge with the group base (C) DISCHARGED — `b(G)` is FREE for small schemes.** Given (A) `Separable` + (B) the transport at every base + the "small" bound `log₂|Aut(X)| ≤ bound`, the scheme discretises at a bounded base; the group base is supplied internally from `exists_greedy_base_le_log` (`b(G) ≤ log₂|Aut|`). Net: the seal-bridge's residual open content is exactly {(A) `Separable` + (B) transport}. Axiom-clean. | — |
| `WarmTwinsAreFiberTwins` | 825-840 | §S-gate2 **The Stage-2 catch-up predicate — THE isolated open model gap.** Every same-`warmRefine`-cell pair from `T` lies in one fiber of the extension `E`. REFUTED at arbitrary `T` by the 2026-06-12 direction check (ℤ₄² bullseye `T={0}`: 4 cells vs 10 fibers), TRUE at every tested `|T| ≥ 2` — carried per-base. The project-model half of the CFI-1992 Thm-5.2 `dimWL(X) ≤ dimWL(X_α)+1` exchange. | Definition |
| `isSchemeAut_of_relOfPair_eq` | 842-853 | §S-gate2 `relOfPair` preservation upgrades to a scheme automorphism — the Bool-level converse of `IsSchemeAut.relOfPair_eq`. | — |
| `twinsRealized_of_extensionPointed` | 855-882 | §S-gate2 **STAGE 2, THE TRANSPORT — landed modulo the catch-up.** Pointed separability of a point extension at `T` (on non-singleton fibers) + `WarmTwinsAreFiberTwins` ⟹ the separability sink `TwinsRealizedByResidualAut S T`: warm twin → fiber-twin (catch-up) → realized by a `T`-fixing extension automorphism (§CC.9) → descends to a `T`-fixing scheme automorphism (`isSchemeAut_of_relOfPair_eq`). | — |
| `separatesAtBoundedBase_of_extensionPointed` | 884-898 | §S-gate2 The pointed gate: catch-up + pointed extension separability + a bounded base ⟹ `SeparatesAtBoundedBase`. The general-CC-keyed sibling of `separatesAtBoundedBase_of_separable` — resolves the Stage-4 keying note (no homogeneous `Separable`/`SeparabilityTransports` in the chain). | — |
| `separatesAtBoundedBase_of_extensionPointed_of_small` | 900-922 | §S-gate2 The pointed gate with the group base picked internally ((C) free via `exists_greedy_base_le_log`), against the **constructed** extension `pointExtension` (§CC.8): pointedness + catch-up at every base + the "small" bound ⟹ `SeparatesAtBoundedBase`. Mirrors `separatesAtBoundedBase_of_separable_of_small`. | — |
| `reachesRigidOrCameron_viaDominatorClosure` | 956-979 | §S-gate2 **THE CITATION-FREE CHECKPOINT (Route δ′) — the seal via the forced-triangle dominator closure.** The conditional seal of `reachesRigidOrCameron_viaExtensionSeparability`, but the separation input is the **citation-free** dominator closure (`hclo : ∀ v, DominatorReachable S T v`). Carries exactly {G3 `hClassify` + `hImprim` + `hclo`} — no `Theorem41Statement`, no conditions-on-the-extension, no catch-up, no group base. The probe-gate verified `hclo` at every minimal base of both residue instances; Stage 3's family-level "the `c=1` closure completes from a bounded base" discharges it — the same open content as the extension-separability route, citation-free. Axiom-clean. | — |
| `reachesRigidOrCameron_viaRainbowRank` | 981-1018 | §S-gate2 (node-2 rung, family level) **The seal via a UNIFORM rainbow rank — the seal-level lift of `clebschZ4`'s mechanism to the whole rainbow-rigid family.** Any schurian scheme that is `RainbowRigid` (every rainbow triangle — three pairwise-distinct non-diagonal colours — has `≤ 1` common neighbour: the amorphic-NLS `(16,5,0,2)`-grade structure) and carries a **rainbow rank** from a bounded base `T` (`rank : Ω → ℕ`, rank-`0` points in `T`, every positive-rank `γ` reached by a rainbow triangle against two strictly-lower-rank points) seals. Composes `dominatorReachable_of_rainbowRank` (closure in `S`'s **own** colours) into the catch-up-free `reachesRigidOrCameron_viaDominatorClosure`. **Carries only {G3 `hClassify` + `hne` + `hrank` + `hImprim`}** — no `hSmallAutThin`/largeness/Cameron citation and **no `hcatch`** (forced triangles in own colours ⟹ 1-WL discretises). The previously-missing connective tissue (the rainbow lift stopped at `DominatorReachable`; no seal capstone consumed it). Per-family residual = exhibit `RainbowRigid` + a rainbow rank; rank ≥ 4 is structural (rainbow needs 3 distinct non-diagonal colours), so this carves the rank-≥4 amorphic residue and **cannot reach node 4's rank-3 SRG core**. Axiom-clean. | — |
| `discrete_warmRefine_of_extensionComplete` | 1034-1046 | §S-gate2 **Bridge: complete extension + catch-up ⟹ `warmRefine` discrete.** Every point a singleton fiber of `E` + `WarmTwinsAreFiberTwins S T E` ⟹ same-warm-cell points coincide (catch-up sends them to one `E`-fiber, completeness makes it a point). The δ′-route analogue of `twinsRealized_of_extensionPointed`, consuming *completeness* not *separability*, so the catch-up is the only carried hypothesis. Axiom-clean. | — |
| `warmTwinsAreFiberTwins_of_warmDiscrete` | 1048-1063 | §S-gate2 **The catch-up is free once `warmRefine` is discrete** (any `E`): same-cell points are equal, so share every reflexive `E`-relation. With `discrete_warmRefine_of_extensionComplete` this gives the **honest accounting**: at a complete extension, `WarmTwinsAreFiberTwins ↔ Discrete (warmRefine …)` — the catch-up carries no information beyond the 1-WL discreteness the seal concludes, so for `n ≥ 25` (δ′ gives only 2-WL completeness) discharging `hcatch` ≡ proving 1-WL discreteness (the dimWL/`c(X_T)` content), not plumbing. Axiom-clean. | — |
| `warmTwinsAreFiberTwins_of_dominatorClosure` | 1065-1075 | §S-gate2 **The catch-up holds wherever the scheme-level δ′ closure does** (in particular the order-16 residue, `c=1` triangles in `S`'s own colours ⟹ 1-WL discretises). Makes `reachesRigidOrCameron_viaExtensionDominatorClosure` non-vacuous (`hcatch` free where the scheme-level engine closes; the routes agree). Does **not** extend to `n ≥ 25`, where 1-WL discreteness is the open content. `warmTwinsAreFiberTwins_of_warmDiscrete ∘ discrete_of_dominatorClosure`. Axiom-clean. | — |
| `warmTwinsAreFiberTwins_of_jointProfileSeparates` | 1077-1101 | **`hcatch` discharged from the checkable depth-1 joint profile — the direct-close handle (route B).** If the joint profile `(relOfPair t ·)_{t∈T}` is injective (`discrete_of_jointProfileSeparates`, the `DepthOneSeparable`/`s(C)=1` condition), then `WarmTwinsAreFiberTwins S T E`. By the honest accounting (at a complete extension `hcatch ⟺ Discrete (warmRefine …)`), discharging `hcatch` **is** establishing 1-WL discreteness — exactly what the joint-profile engine produces. Strictly generalizes `…_of_dominatorClosure` (δ′ is one way to separate the profile). **Closes `hcatch` on the depth-1-separable sub-class**; the residual `s(C)≥2` (iterated/cyclotomic) case is the *same open content as the seal's self-detection `s(C)` layer* (the not-yet-built bounded-depth engine), **not** a separate WL-dim citation. So `hcatch` is not an independent gap — it collapses onto the project's 1-WL self-detection content. Axiom-clean. | — |
| `separatesAtBoundedBase_of_extensionDominatorClosure` | 1103-1117 | §S-gate2 **δ′-on-the-extension, packaged for the seal.** A bounded base `T` whose forced-triangle closure exhausts Ω **on `X_T = pointExtension`** (`hclo`) + the catch-up at `T` ⟹ `SeparatesAtBoundedBase S bound`. `Sharp` discharged internally (`sharp_pointExtension`), so the open input is `hclo` (the `c(X_T)` content) + the probe-green catch-up. The `n ≥ 25` sibling of `separatesAtBoundedBase_of_dominatorClosure`. Axiom-clean. | — |
| `reachesRigidOrCameron_viaExtensionDominatorClosure` | 1119-1139 | §S-gate2 **The δ′-on-the-extension seal checkpoint (`n ≥ 25` citation-free path).** Same plumbing as `reachesRigidOrCameron_viaDominatorClosure`, fed by the **extension** closure + catch-up, covering the residue where `S`'s own colours have no `c=1` triangles. Carries exactly {G3 + `hImprim` + `hclo` (open `c(X_T)` content on `X_T`) + `hcatch` (probe-green 1-WL↔fiber catch-up)}. Axiom-clean. | — |
| `reachesRigidOrCameron_viaBoundedExtensionParams` | 1141-1169 | §S-gate2 **THE SEAL VIA THE A2 PARAMETER INEQUALITY (honest conditional capstone).** Same conclusion as `…viaExtensionDominatorClosure`, but the abstract `hclo` is replaced by the concrete **A2 bound** `(k(X_{T₀})−1)·c(X_{T₀}) < |T|` at a small base `T₀ ⊆ T` (via `dominatorReachable_of_card_gt_subset`). Carries `{G3 + bounded-extension-params + hcatch + hImprim}`; the A2 piece = the residue's **bounded WL-dimension** (confirmed open/not-citable by the rank-3/4 SRG research, 2026-06-14). Axiom-clean. | — |
| `reachesRigidOrCameron_viaPotentialDrop` | 1171-1203 | §S-gate2 **THE SEAL VIA THE POTENTIAL-DROP HYPOTHESIS (the uniform A2 route, `docs/chain-descent-a2-potential-route.md`).** Same conclusion as `…viaBoundedExtensionParams`, but the A2 inequality is replaced by its *uniform generator* `hdrop : PotentialDrops B` (every base whose potential `(k−1)c` exceeds `B` has an individualization halving it). The `§CC.20` iteration engine produces a small base `T₀` with potential `≤ B`, padded (`§CC.18/19`) to a base of size `B+1`. Carries `{G3 + PotentialDrops + hcatch(∀T) + hImprim}` — the open content concentrated into the per-step drop (the probe's "shattering" on the non-geometric residue). Axiom-clean. | — |
| `reachesRigidOrCameron_viaShattering` | 1205-1232 | §S-gate2 (Stage 1b) **THE SEAL VIA THE SHATTERING HYPOTHESIS — A2's open content sharpened to `c`-halving.** Same conclusion as `…viaPotentialDrop`, but the per-step drop on the product `(k−1)c` is replaced by its cleaner generator `IndistinguishingHalves B` (some individualization halves the indistinguishing number `c(X_T)` alone; `k` rides free by `maxValency_mono`). Via `potentialDrops_of_indistinguishingHalves` → `…viaPotentialDrop`. Seal conditional `modulo {G3 + IndistinguishingHalves + hcatch + hImprim}`; a `c`-class resisting halving is a partial-geometry line system (probe `Probe_SmallestEigenvalueAxis`, route doc §3/§5). Axiom-clean. | — |
| `reachesRigidOrCameron_viaBoundedMultiplicity` | 1234-1267 | §S-gate2 **The seal via bounded confusion multiplicity — 'the residue cascades ⟹ polynomial'.** Carries `BoundedConfusionMultiplicity B M` (a `≤M`-set halves `c`); the `§CC.20b` engine turns it into an `O(M·log n)` base. Seal `modulo {G3 + BoundedConfusionMultiplicity + hcatch + hImprim}`; strictly weaker than `IndistinguishingHalves` (its `M=1` case). Axiom-clean. | — |
| `reachesRigidOrCameron_viaCompleteBase` | 1269-1300 | §S-gate2 (node-2 rung) **The seal via a discrete bounded base — validates the `…viaBoundedMultiplicity` pipeline end-to-end.** Carries `hcomplete`: a bounded base `T₀` (`|T₀|≤M`) discretizes the extension (the δ′ engine's deliverable). **No largeness guard** — a thin family discretizing at an `O(log n)` base cascades outright (node 4 never invoked). Seal `modulo {G3 + hcatch + hImprim}`. Axiom-clean. | — |
| `reachesRigidOrCameron_viaBoundedMinMult` | 1302-1338 | ★ **LIVE CANONICAL CAPSTONE.** §S-gate2 **The seal via small-Aut bounded multiplicity (the `minMult`-form dichotomy).** Carries `hSmallAutThin : ¬IsLarge → BoundedMinMult B M` (small Aut ⟹ bounded `minMult`); large→cited G3→Cameron/`hImprim`, small→cascade. `hSmallAutThin` = the `minMult`-form of Babai's SRG structure theorem = the entire open content of node 4 (primitive non-Cameron ⟹ thin), in the computable quantity the probe measures. Seal `modulo {G3 + hSmallAutThin + hcatch + hImprim}`. Axiom-clean. | — |
| `reachesRigidOrCameron_viaSmallAutShatters` | 1398-1446 | §S-gate2 **The seal via small-Aut shattering — the FAITHFUL-direction citation.** Carries `hSmallAutDiscretizes : ¬IsLarge → ∀ over-`B` base, ¬BigConfusionCover(X_T)` (= 'small Aut ⟹ shatters', the literature-true Babai/Kivva direction) and `by_cases` on `IsLarge`. Faithful sibling of the archived `…viaNoConfusionCover` (whose 'cover ⟹ large' direction is CGGP-false). Seal `modulo {G3 + Babai-SRG + hcatch + hImprim}`, sub-exp threshold. Axiom-clean. | — |
| `reachesRigidOrCameron_viaNoCover` | 1448-1479 | §S-gate2 **The seal via direct shattering — the POLYNOMIAL target (node 4), no largeness citation.** Carries the single crux `hShatter : ∀ over-`B` base, ¬BigConfusionCover(X_T)` with no largeness guard or Cameron routing; discharging it makes the seal **polynomial**. **`hShatter` IS node 4** (a primitive non-geometric non-conference SRG never develops a big-confusion cover). Carries `{G3 (unused) + hShatter + hcatch + hImprim}`. Axiom-clean. | — |
| `warmTwinsAreFiberTwins_of_kRoundRelationSeparates` | 1929-1955 | **`hcatch` at full engine strength — from the depth-`k` relation-count separation certificate.** If the joint relation-profile counts separate all vertices (the `discrete_of_kRoundRelationSeparates` certificate), then `WarmTwinsAreFiberTwins S T E`. Composes the landed depth-`k` discreteness producer with `…_of_warmDiscrete`. **Strictly stronger** than `…_of_jointProfileSeparates`: the count profile is the inherently multi-base, two-round invariant that separates the cyclotomic/affine residues where the depth-1 joint profile is a coset twin, and it is **k-independent** (k only drives peeling) = the strongest separation the engine gives. **It is the same certificate as the seal's open self-detection content** (`RelCountsDetermineOrbit`/`PersistentTwinYieldsBlock`) — so `hcatch` is free wherever that discharges (δ′, affine cyclotomic via `discrete_affineScheme_of_twoRoundDiffSeparates`): `hcatch` and `s(C)` are one object. Axiom-clean. | — |
| `RelCountsDetermineOrbit` | 1975-1988 | **(step 2.3 — the open `s(C)` hypothesis, counting form)** Two vertices with equal relation-profile counts relative to base `T` (the bounded-depth invariant of `discrete_of_kRoundRelationSeparates`: neighbours `z` histogrammed by `(T`-profile of `z`, relation to the vertex`)`) lie in the same `Stab(T)`-orbit. The orbit-analogue of that engine's separation hypothesis (`= u'` weakened to "same orbit", for the non-base symmetric phase). **Genuinely open (G2-B)** — FALSE for high-`s(C)` schemes; conjectured to hold from base+`O(1)` for primitive small. | Definition |
| `cellsAreOrbits_of_relCountsDetermineOrbit` | 1990-1999 | **(step 2.3 — the counting producer)** `CellsAreOrbits (schemeAdj S) T` from `RelCountsDetermineOrbit S T` — the orbits (non-base) analogue of `discrete_of_kRoundRelationSeparates` (which produces singletons at bases). A same-cell pair shares its relation-count profile (`kRoundProfileCount_eq` at `k=1`), and the hypothesis lifts that to an orbit relation. Needs `2 ≤ n`. Axiom-clean. | — |
| `recoversWhileSymmetric_of_relCountsDetermineOrbit` | 2001-2011 | **(step 2.3 — seal symmetric-phase recovery from per-prefix counting)** `RecoversWhileSymmetric S₀` from: every non-base prefix `T ⊇ S₀` has relation counts determining the `Stab(T)`-orbit. Each prefix's `CellsAreOrbits` via the counting producer. Axiom-clean. | — |
| `selfDetectsWhileSymmetric_of_relCountsDetermineOrbit` | 2013-2029 | **(step 2.3 — THE SEAL'S OPEN CONTENT AS A FINITE COUNTING NON-EXISTENCE)** `SelfDetectsWhileSymmetric` from "primitive small ⟹ ∃ bounded `S₀`, every non-base `T ⊇ S₀` has its `Stab(T)`-orbits determined by relation counts". The entire open seal content as a concrete counting condition — the sharpest *provable* form of the `s(C)` conjecture (`base(G)` banked by 2.1, layer reduction by 2.2, counting engine here). Whether the hypothesis holds for all primitive small schemes is the GI-adjacent open core. Axiom-clean. | — |
| `reachesRigidOrCameron_viaAffineFormScheme` | 2031-2068 | **(Stage A — the seal's node-4 forms-graph wiring; route §9.9.18c, `chain-descent-formsgraph-wldim-plan.md`)** The conditional capstone for the seal's remaining schurian node-4 residue (the Skresanov-isolated affine forms-graphs `{VO^ε / alternating / half-spin / Suzuki–Tits}`). Carries exactly two pieces: `hbase : IsBase … T` (the **free group base** `T={0,e₁,…,e_d}`, `(G^(2))_T={1}`, discharged outright on `affineScheme G₀`) and `hFormCert : RelCountsDetermineOrbit … T` (the **only open content** — the probe-validated separation certificate the crux lemma "count profile recovers form coords `B(v,e_i)`" discharges per family, Stage B). Wiring: `cellsAreOrbits_of_relCountsDetermineOrbit` → `twinsRealizedByResidualAut_iff_cellsAreOrbits` → `separatesAtBoundedBase_of_twinsRealized` → `reachesRigidOrCameron_viaSpielman`. **Carries NO `hSmallAutThin`** — node 4 is *discharged* for this residue, not assumed. Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `affineScheme_interNum_eq_one_of_unique` | 2547-2584 | §S-stage3 **The affine forced-triangle criterion (δ′ Stage-3 substrate).** For `affineScheme G₀`, the dominator intersection number `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` exactly when `γ` is the **unique** point `u` sharing `γ`'s `G₀`-orbit-of-difference both to `α` (`u−α ∼ γ−α`) and from `β` (`β−u ∼ β−γ`). Proof: the forced-triangle filter is exhibited as the singleton `{γ}` (membership unfolds via `affineScheme_rel_iff` + `orbMk_affine_eq_iff`; uniqueness collapses it). Translates the abstract `DominatorReachable.step` premise into `G₀`-orbit uniqueness on differences — the form the family combinatorics reason in. Axiom-clean. | — |
| `dominatorReachable_affine_step` | 2586-2601 | §S-stage3 **The affine `DominatorReachable` step builder.** From two dominator-reachable points `α, β` and the affine forced-triangle uniqueness pinning `γ`, `γ` is dominator-reachable. With `DominatorReachable.base` (`t ∈ T`) the complete toolkit for constructing `DominatorReachable (affineScheme G₀ hneg) T` derivations from pure `G₀`-orbit-of-difference uniqueness — the lone open content `∀ v, DominatorReachable … v` of the δ′ seal capstone is built from these. Axiom-clean. | — |
| `polar_eq_of_sub` | 2627-2634 | **(Stage B.0 forms-graph slice)** Polar recovery arithmetic: `polar Q v e = Q v + Q e - Q (v - e)`. Axiom-clean. | — |
| `coords_determine` | 2636-2653 | **(Stage B.0 — the crux's reusable back-half: form coordinates determine the vector)** If `Q`'s polar form is nondegenerate and `Q v`, `Q (v − e_i)` agree with `v'` on the standard basis `e_i = Pi.single i 1`, then `v = v'` (same `Q`-values ⟹ same polar coords `polar Q v e_i` ⟹ by nondegeneracy `v = v'`). Shared with Stage B.1's count back-half. Axiom-clean. | — |
| `isometryGroup` | 2655-2671 | **(Stage B.0)** The orthogonal/isometry group `O(Q) = {g : V ≃ₗ V | ∀ x, Q (g x) = Q x}` as a `Subgroup` of `V ≃ₗ[ZMod p] V`. | Definition |
| `mem_isometryGroup` | 2673-2675 | Membership unfolding for `isometryGroup`: `g ∈ isometryGroup Q ↔ ∀ x, Q (g x) = Q x`. | — |
| `neg_mem_isometryGroup` | 2677-2681 | `-1` is an isometry of any quadratic form (the `hneg` input for `affineScheme`). Axiom-clean. | — |
| `frameBase` | 2683-2686 | **(Stage B.0)** The basis-frame base set `{0, e₁,…,e_d}` (origin + standard basis) transported to `Fin (p^d)`. | Definition, `noncomputable` |
| `frameBase_card_le` | 2688-2694 | `frameBase.card ≤ d + 1` (the `O(1)` base size). Axiom-clean. | — |
| `reachesRigidOrCameron_viaOrthogonalForm` | 2696-2733 | **(Stage B.0 — THE SEAL VIA THE ORTHOGONAL FORM; route §9.9.18c, `chain-descent-formsgraph-wldim-plan.md` §3)** For any quadratic form `Q` on `F_p^d` with nondegenerate polar form, the affine scheme of the isometry group `O(Q)` individualizes to discrete at the basis-frame `{0,e₁,…,e_d}` (size `d+1`) and seals, via **depth-1** separation: the orbit-of-difference determines `Q(v−t)`, which recovers the form coordinates (`coords_determine`) ⟹ discrete ⟹ `reachesRigidOrCameron_viaSpielman`. **Carries NO `hSmallAutThin`.** Honest scope: `O(Q)` is the *finer* orthogonal scheme, **not yet** the rank-3 SRG `VO^ε` (= similitude `ΓO(Q)`, Stage B.1); lands the shared quadratic-form infrastructure + Witt-free recovery. Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `similitudeGroup` | 2745-2763 | **(Stage B.1)** The orthogonal **similitude** group `GO(Q) = {g : V ≃ₗ V | ∃ μ ∈ F_p^×, ∀ x, Q (g x) = μ • Q x}` as a `Subgroup` of `V ≃ₗ[ZMod p] V`. The genuine node-4 rank-3 SRG `VO^ε` is its affine scheme (nonzero `Q`-values fuse ⟹ rel = isotropy class). | Definition |
| `neg_mem_similitudeGroup` | 2765-2768 | `-1` is a similitude (factor `1`) — the `hneg` input for `affineScheme`. Axiom-clean. | — |
| `isometry_le_similitude` | 2770-2773 | `O(Q) ≤ GO(Q)`: every isometry is a similitude (factor `1`). Axiom-clean. | — |
| `SimilitudeFrameSeparates` | 2775-2800 | **⚠ SUPERSEDED (2026-06-18 — frame-locked, FALSE for `VO^-`; live target = `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` at a symmetry-broken base).** **(Stage B.1c — THE GENUINE NODE-4 COUNT CRUX, as a named predicate)** The two-round difference-count separation certificate for the similitude scheme at the basis frame (= the hypothesis `discrete_affineScheme_of_twoRoundDiffSeparates` consumes, `T := frameBase`). Under `GO(Q)` the relation is only the isotropy class, so this is the genuine two-round count obligation. **OPEN** — discharge = the affine-quadric point-count (count recovers `B(v,e_i)`; back-half = `coords_determine`), blocked on Mathlib Witt + Gauss-sum infrastructure. | Definition |
| `reachesRigidOrCameron_viaSimilitudeForm` | 2802-2820 | **⚠ SUPERSEDED (2026-06-18 — frame-locked, FALSE for `VO^-`; live target = `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` at a symmetry-broken base).** **(Stage B.1 — THE SEAL VIA THE SIMILITUDE FORM; the node-4 rank-3 SRG `VO^ε`, conditional capstone)** For any `Q` on `F_p^d`, the affine scheme of the similitude group `GO(Q)` — the genuine rank-3 forms-graph residue — seals once the two-round count certificate `SimilitudeFrameSeparates Q` holds (`discrete_affineScheme_of_twoRoundDiffSeparates` at `frameBase` → `reachesRigidOrCameron_viaSpielman`). The certificate is the **only open content** (Stage B.1c). **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `FrameCountsAgree` | 2831-2845 | **(Stage B.1c checkpoint)** The two-round difference-count agreement of `u,u'` at the basis frame — the antecedent of `SimilitudeFrameSeparates`, named for reuse (defeq to it). | Definition |
| `CountsDetermineFrameQ` | 2847-2854 | **⚠ SUPERSEDED (2026-06-18 — frame-locked, FALSE for `VO^-`; live target = `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` at a symmetry-broken base).** **(Stage B.1c front-half — the Witt+Gauss deliverable, as a named predicate)** Agreeing two-round counts ⟹ same `Q`-value profile at the frame (`Q ū = Q ū'`, `Q(ū−e_i)=Q(ū'−e_i)`). Exactly what Witt (orbit = isotropy class) + quadratic Gauss-sum affine-quadric point counts deliver. **OPEN.** | Definition |
| `similitudeFrameSeparates_of_countsDetermineFrameQ` | 2856-2867 | **(CHECKPOINT — the count crux factors through the landed back-half)** `CountsDetermineFrameQ Q` discharges the certificate `SimilitudeFrameSeparates Q` via the landed `coords_determine` (B.0). Confirms front-half (counts recover `Q`-profile) + back-half (nondegenerate ⟹ profile determines vector) compose. Axiom-clean. | — |
| `reachesRigidOrCameron_viaCountsDetermineFrameQ` | 2869-2884 | **⚠ SUPERSEDED (2026-06-18 — frame-locked, FALSE for `VO^-`; live target = `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` at a symmetry-broken base).** **(THE CONFIRMED RESEARCH-CORE CHECKPOINT — seal via the Witt+Gauss deliverable)** End-to-end: `CountsDetermineFrameQ` (= Witt + Gauss) → `SimilitudeFrameSeparates` (via `coords_determine`) → seal for the rank-3 SRG `VO^ε` residue. Confirms the heavy-but-known machinery, once built, closes the seal; open content isolated to the single front-half predicate `CountsDetermineFrameQ`. **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `isoClass` | 2895-2897 | **(Stage B.1c)** The isotropy class of a vector: `0` (zero), `1` (nonzero isotropic), `2` (anisotropic). | Definition, `noncomputable` |
| `isoClass_eq_zero_iff` | 2907-2914 | **(isotropy dictionary)** Class `0` ⟺ `w = 0` (the zero vector). | — |
| `isoClass_eq_two_iff` | 2916-2923 | **(isotropy dictionary)** Class `2` ⟺ anisotropic `Q w ≠ 0` — a *pure* `Q`-value condition (no origin correction), the bridge to `Q`-value-set counts. | — |
| `isoClass_eq_one_iff` | 2925-2932 | **(isotropy dictionary)** Class `1` ⟺ nonzero isotropic `w ≠ 0 ∧ Q w = 0` (the one class refined by the origin). | — |
| `isoClass_ne_two_iff` | 2934-2938 | **(isotropy dictionary)** The coarse isotropic/anisotropic SRG split: `isoClass ≠ 2 ⟺ Q w = 0` — a *pure* `Q`-value condition with the origin folded in. | — |
| `OrbitIsIsotropyClass` | 2940-2951 | **(Stage B.1c-i — the Witt deliverable, as a named predicate)** The `GO(Q)`-orbit of a difference (= the relation `relOfPair (affineE 0) (affineE w)`) is determined by its isotropy class, via an injection `Fin 3 ↪ relations`. "Function of isoClass" = Witt transitivity (orbit fusion); injectivity = `Q`-invariance. **OPEN** (Witt; ABSENT in Mathlib). | Definition |
| `IsotropyFrameCountsAgree` | 2952-2962 | The isotropy-class count agreement of `u,u'` at the frame (`FrameCountsAgree`'s relation conditions rewritten as isotropy-class conditions). | Definition, `noncomputable` |
| `IsotropyCountsRecoverFrameQ` | 2964-2977 | **⚠ SUPERSEDED (2026-06-18 — frame-locked, FALSE for `VO^-`; live target = `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` at a symmetry-broken base).** **(Stage B.1c-ii — the Gauss deliverable, as a named predicate)** Isotropy-class counts recover the frame `Q`-profile (`Q ū=Q ū'`, `Q(ū−e_i)=Q(ū'−e_i)`). The pure affine-quadric point-count statement (Gauss sums), NO opaque relations. **OPEN.** | Definition |
| `isotropyFrameCountsAgree_of_frameCountsAgree` | 2978-3006 | **(plumbing)** Via `OrbitIsIsotropyClass`, relation-count agreement `FrameCountsAgree` ⟹ isotropy-count agreement `IsotropyFrameCountsAgree` (each isotropy filter = relation filter at `ρ = relOfIso ∘ σ`, `b = relOfIso c`). Axiom-clean. | — |
| `countsDetermineFrameQ_of_orbitIsIsotropyClass` | 3008-3014 | **(CHECKPOINT — Witt ∘ Gauss ⟹ the front-half)** `OrbitIsIsotropyClass` (Witt) + `IsotropyCountsRecoverFrameQ` (Gauss) discharge `CountsDetermineFrameQ`. Confirms the isotropy-count predicate is B.1c-ii's exact target and B.1c-i's output plugs in — before building Witt. Axiom-clean. | — |
| `reachesRigidOrCameron_viaIsotropyCounts` | 3016-3032 | Gauss boundary: `OrbitIsIsotropyClass` (Witt) + `IsotropyCountsRecoverFrameQ` (Gauss) → `CountsDetermineFrameQ` → `SimilitudeFrameSeparates` (via `coords_determine`) → seal. Confirms B.1c's two builds compose to close. **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `SeparatesAtBase` | 3058-3077 | **(Stage B.1c CORRECTED — the live separation predicate)** One-round difference-relation count-injectivity at an *arbitrary* base `T` (= the antecedent of `discrete_affineScheme_of_twoRoundDiffSeparates` with `T` free). `SimilitudeFrameSeparates` is the mis-shaped `T := frameBase` instance; the live target discharges this at a symmetry-broken `T` (`≈ d+2`). | Definition |
| `reachesRigidOrCameron_viaSymmetryBrokenBase` | 3079-3097 | **(THE CORRECTED NODE-4 CAPSTONE — seal via a symmetry-broken base)** Any bounded base `T` (`|T|≤bound`) with `SeparatesAtBase Q T` discretizes the rank-3 SRG `VO^ε` residue and seals — dropping `coords_determine`/`Q`-profile recovery (wrong for minus-type). Generalizes `…viaSimilitudeForm` off the symmetric frame. **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `IsotropySeparatesAtBase` | 3098-3112 | **(Stage B.1c-ii — THE GAUSS ENDPOINT)** Pure isotropy-class count-injectivity at an arbitrary base `T`, NO opaque scheme relations — the affine-quadric point-count target the Gauss toolkit (`GaussCount.lean`) discharges for a symmetry-broken `T`. Lifted to `SeparatesAtBase` by `separatesAtBase_of_isotropySeparates` (Witt). **OPEN.** | Definition, `noncomputable` |
| `separatesAtBase_of_isotropySeparates` | 3114-3145 | **(the Witt bridge, arbitrary base)** Given `OrbitIsIsotropyClass` (relation = injective image of isotropy class), `IsotropySeparatesAtBase Q T` ⟹ `SeparatesAtBase Q T` (each isotropy filter = relation filter at `ρ = relOfIso ∘ σ`). Arbitrary-`T` analogue of `isotropyFrameCountsAgree_of_frameCountsAgree`, separation form. Axiom-clean. | — |
| `reachesRigidOrCameron_viaIsotropySeparates` | 3147-3163 | **(THE CORRECTED GAUSS-BOUNDARY CAPSTONE — replaces `…viaIsotropyCounts`)** End-to-end on the arbitrary-`T` target: `OrbitIsIsotropyClass` (Witt, B.1c-i) + a concrete `IsotropySeparatesAtBase Q T` for a bounded symmetry-broken `T` (Gauss, B.1c-ii) → seal. **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `RelationRefinesIsotropy` | 3175-3182 | **(the Witt-FREE easy half of `OrbitIsIsotropyClass`)** The scheme relation *refines* the isotropy class: `∃ g, isoClass Q w = g (relOfPair (affineE 0) (affineE w))`. Implied by `OrbitIsIsotropyClass` (the full bijection) but — unlike it — dischargeable Witt-free (`relationRefinesIsotropy_similitude`). | Definition |
| `relationRefinesIsotropy_of_orbitIsIsotropyClass` | 3184-3196 | The full Witt deliverable `OrbitIsIsotropyClass` ⟹ the easy half `RelationRefinesIsotropy` (confirms the latter is a genuine weakening). Axiom-clean. | — |
| `separatesAtBase_of_isotropySeparates_weak` | 3197-3273 | **(the Witt-FREE separation bridge)** `RelationRefinesIsotropy` (easy half only) + `IsotropySeparatesAtBase Q T` ⟹ `SeparatesAtBase Q T`, via a fiberwise partition (the consistency test `g ∘ ρ = σ` is pivot-independent ⟹ each fiber's relation-count agrees). Witt-free analogue of `separatesAtBase_of_isotropySeparates`. Axiom-clean. | — |
| `isoClass_similitude_invariant` | 3275-3290 | A similitude (`Q (g₀ x) = μ · Q x`, `μ` a **unit** in `similitudeGroup`) preserves `isoClass` — zero/nonzero `LinearEquiv`-invariant, `Q = 0` preserved since `μ` is a unit. The invariance behind the Witt-free discharge. Axiom-clean. | — |
| `relationRefinesIsotropy_similitude` | 3291-3311 | **(discharges `RelationRefinesIsotropy` Witt-FREE, no hypothesis, for any `Q`)** The scheme relation determines `isoClass` by similitude-invariance (`affineScheme_relOfPair_eq_iff` + `orbMk_affine_eq_iff` give the orbit equation; `isoClass_similitude_invariant` finishes). Removes `OrbitIsIsotropyClass` from the capstone. Axiom-clean. | — |
| `reachesRigidOrCameron_viaIsotropySeparates_wittFree` | 3312-3328 | **(THE WITT-FREE SEAL CAPSTONE — supersedes `…viaIsotropySeparates`)** The seal for the rank-3 SRG `VO^ε` residue from a bounded symmetry-broken base + isotropy-count injectivity, carrying **NO Witt input** (`OrbitIsIsotropyClass` discharged Witt-free). The ONLY open input is the Gauss target `IsotropySeparatesAtBase Q T` (plus cited `G3`). **Carries NO `hSmallAutThin`.** Axiom-clean `[propext, Classical.choice, Quot.sound]`. | — |
| `fieldOf` | 3710-3714 | §S-stage3-δ **The field coordinate of a point** — `Fin (p^d) → F_p^d → F_q` (`(efield).symm ∘ affineE.symm`), the bijection carrying the affine point set into `F_q`, in which the cyclotomic orbit-of-difference is a multiplicative `⟨g⟩`-orbit. | Definition, `noncomputable` |
| `fieldOf_injective` | 3716-3721 | §S-stage3-δ **`fieldOf` is injective** (composite of two injective `Equiv.symm` maps) — the distinctness transport: distinct affine points have distinct field coordinates. Axiom-clean. | — |
| `G0pow_orbit_iff` | 3723-3741 | §S-stage3-δ **The cyclotomic orbit reduction (incr 4b core).** A `G0pow g`-orbit relation between coordinate vectors `v,w` is exactly multiplication by a power of `g` through the field iso: `∃ g₀ ∈ G0pow g, g₀ v = w ↔ ∃ k:ℤ, g^k · efield.symm v = efield.symm w`. From `sigmaPow_zpow_apply` + injectivity of `efield`. The brick converting the cyclic affine action into pure `F_q` multiplication. Axiom-clean. | — |
| `dominatorReachable_G0pow_step` | 3743-3769 | §S-stage3-δ **The cyclotomic `DominatorReachable` step builder (`F_q`-power form, incr 4b).** The forced-triangle step for `affineScheme (G0pow g)` with pinning stated in pure `F_q` powers: from reachable `α,β`, if the only `u` with `g^k·(fieldOf u−fieldOf α)=fieldOf γ−fieldOf α` and `g^k·(fieldOf β−fieldOf u)=fieldOf β−fieldOf γ` is `γ`, then `γ` reachable. From `dominatorReachable_affine_step` via `G0pow_orbit_iff` (orbit⟹power on each hypothesis, `efield.symm` linear over the difference). The toolkit the cyclotomic single-base closure builds derivations with. Axiom-clean. | — |
| `dominatorReachable_G0pow_ratio_step` | 3771-3822 | §S-stage3-δ **The cyclotomic ratio-form step builder (incr 4c — the `s(C)` arithmetic boundary).** The forced-triangle step with the field-difference equations divided through: for distinct field coords (`c≠a`, `b≠c`), `γ` is pinned by `α,β` once the only `h` with `h ∈ ⟨g⟩` **and** `1 + r·(1−h) ∈ ⟨g⟩` (cross-ratio `r=(c−a)/(b−c)`) is `h=1`. From `dominatorReachable_G0pow_step` by `h=(x−a)/(c−a)`, computing `(b−x)/(b−c)=1+r(1−h)`; `h=1 ⟺ x=c ⟺ u=γ` (`fieldOf` injective). The `(r+1−r·h)∈⟨g⟩→h=1` reduction of §5 — closest Lean form to the open cyclotomic `s(C)` arithmetic; exposes the char-2-midpoint obstruction (`r=1 ⟹ 2−h=h` in char 2, nothing pins). Axiom-clean. | — |
| `dominatorReachable_G0pow_neg` | 3837-3894 | §S-stage3-δ **The `H={±1}` cyclotomic family closes from any 2-base (odd char) — the FIRST end-to-end discharge of the δ′ seal's closure hypothesis on a real `affineScheme` family.** For `g=-1` (`⟨g⟩={1,-1}`), `p≠2`, every point is dominator-reachable from any 2-base `{α,β}` (`α≠β`): each `γ∉{α,β}` is forced-triangle-pinned by `α,β` in one round. Arithmetic (via `dominatorReachable_G0pow_ratio_step`): the cross-ratio `r=(c−a)/(b−c)` of distinct points has `r∉{0,-1}`, so for `h=-1∈⟨g⟩`, `1+2r∉{1,-1}` (uses `2≠0`), the antecedent fails, only `h=1` survives. Proves the seal's `hclo` for the whole family; char≠2 is the char-2-midpoint obstruction. Axiom-clean. | — |
| `reachesRigidOrCameron_viaG0powNeg` | 3896-3926 | §S-stage3-δ **The seal on the `H={±1}` family, with the δ′ closure DISCHARGED (not assumed).** `reachesRigidOrCameron_viaDominatorClosure` at `affineScheme (G0pow (-1))` (odd char), feeding `hclo` from `dominatorReachable_G0pow_neg`. The seal holds carrying only the standard {G3 `hClassify` + `hne` + `hrank` + `hImprim`} — **the open `hclo` is gone, proved rather than carried.** The first family on which the δ′ route discharges the seal's open content outright. Axiom-clean. | — |
| `dominatorReachable_G0pow_subfield_step` | 3976-4005 | §S-stage3-δ **The subfield pinning step (`r∉K ⟹ pinned`) — the genuine multi-round content.** For `affineScheme (G0pow g)` with `⟨g⟩=K^×` (carried `hHK`, `K` a subfield), if the cross-ratio `r=(c−a)/(b−c)∉K` then `γ` is forced-triangle-pinned by `α,β`. Arithmetic: `h∈K^×`, `h≠1` ⟹ `1−h∈K^×` ⟹ `r=(r(1−h))/(1−h)∈K`, contra `r∉K`. Size-free (any `|K|≥2`), unlike one-round `H={±1}`. Axiom-clean. | — |
| `dominatorReachable_G0pow_subfield` | 4007-4048 | §S-stage3-δ **The 2-round closure for the subfield family `H=K^×` — a genuine multi-round cyclotomic closure.** For `⟨g⟩=K^×` (`K⊊F_q`), a base of two distinct `K`-points closes all of `F_q` in two rounds — the first `|H|>2` closure (vs the one-round `H={±1}`). **NOTE: the `K^×` family is IMPRIMITIVE** (the hImprim/G2-A case, not the primitive G2-B residue); validates the multi-round engine, primitive case still open. Axiom-clean. | — |
| `affinePermFin_eq_one_of_span` | 4385-4409 | **Module-adjoin kill lemma.** An `F_p`-linear automorphism whose affine perm (zero translation) fixes a base `T` pointwise, with `affineE.symm '' T` spanning `F_p^d`, is the identity perm — kills the whole `ΓL₁` separability gap by a spanning (`O(log n)`) base. The linear generalization of the Frobenius-only `frobPerm_pow_eq_one_of_adjoin`. | — |
| `TwinsAreSemilinear` | 4422-4434 | The cited `s(C)`-half of the affine slice: every depth-2 profile-twin from base `T` is realised by an `F_p`-linear automorphism fixing `T`. The operational form of cyclotomic 2-separability (Ponomarenko arXiv:2006.13592 Thm 1.1), carried as a theorem-statement hypothesis. | Definition |
| `powAffineSeparates_of_twinsAreSemilinear` | 4436-4452 | **The reduction.** `TwinsAreSemilinear` on a spanning base ⟹ `PowAffineSeparates`: a twin's realiser fixes the spanning base, so `affinePermFin_eq_one_of_span` forces it trivial. Replaces the open counting crux with the cited 2-separability. | — |
| `reachesRigidOrCameron_viaTwinsAreSemilinear` | 4454-4481 | The seal on `affineScheme (G0pow β)` from the cited `TwinsAreSemilinear` + a spanning base — composes the reduction into `reachesRigidOrCameron_viaPowSeparation`. | — |
| `exists_spanning_base` | 4483-4505 | A bounded spanning base exists: the standard basis `Pi.basisFun` transported through `affineE` gives `∃ T`, `card ≤ d`, with `affineE.symm '' T` spanning `F_p^d`. Discharges the spanning/`card` hypotheses for any `bound ≥ d`. | — |
| `reachesRigidOrCameron_affineSlice` | 4507-4532 | **The fully-reduced affine cyclotomic seal slice.** The seal on `affineScheme (G0pow β)` whose only affine-specific input is `hcite : ∀ T, TwinsAreSemilinear` (= cited cyclotomic 2-separability) plus `d ≤ bound`; the spanning base is picked internally. No counting crux, no spanning-base hypothesis carried. | — |
| `clebschScheme` | 4577-4581 | The Clebsch index-3 affine scheme on `F₁₆` (`affineScheme (G0pow (fqGen³)) …`) — the concrete primitive (rank-≥3), small, non-abelian-residual instance (`clebschWitness_irreducible`); the test fixture for the general P3 converse. | Definition, `noncomputable` |
| `reachesRigidOrCameron_clebsch_viaPersistentTwinBlock` | 4583-4599 | **(Reroute demonstration.)** `reachesRigidOrCameron_viaPersistentTwinBlock` instantiated *verbatim* at `clebschScheme` — no affine/Frobenius machinery. Shows the mechanism-agnostic crux subsumes the affine-cyclic slice the retracted `PowAffineSeparates` targeted (probe evidence: primitive ⟹ flat depth-4 recovery). Conditional (carries the open `hCrux`). Axiom-clean. | — |
## ChainDescent/Separability.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme.valency` | 44-45 | **§S.1.** Valency `n_i = c^0_{i,i}` of relation `R_i` (the constant out-degree). The S-ring/Ponomarenko–Vasil'ev Thm-3.1 parameter substrate. | Definition |
| `AssociationScheme.valency_eq_card` | 47-58 | `n_i` equals the literal out-degree `|{w : (v,w)∈R_i}|` from any vertex `v` (homogeneity). | — |
| `AssociationScheme.valency_zero` | 60-68 | The diagonal `R_0` has valency `1`. | — |
| `AssociationScheme.maxValency` | 70-71 | **§S.1.** The maximum valency `k(X) = max_i n_i`. | Definition |
| `AssociationScheme.valency_le_maxValency` | 73-75 | Every valency is `≤ k(X)`. | — |
| `AssociationScheme.indistinguishingNumberOf` | 85-87 | **§S.2.** `c(r) = Σ_s c^r_{s,s*}` — the indistinguishing number of relation `R_r`. | Definition |
| `AssociationScheme.indistinguishingNumber` | 89-92 | **§S.2.** The indistinguishing number `c(X) = max_{r≠0} c(r)`. | Definition |
| `AssociationScheme.indistinguishingNumberOf_le` | 94-97 | `c(r) ≤ c(X)` for every non-diagonal `R_r`. | — |
| `AssociationScheme.indistinguishingNumberOf_eq_card` | 99-133 | **PV eq. (7).** For `(α,β)∈R_r`, `c(r) = |{γ : r(γ,α)=r(γ,β)}|` — the count of vertices failing to distinguish `α` from `β`. The geometric form the (19) estimate consumes. | — |
| `AssociationScheme.SparseSeparable` | 142-145 | **§S.3.** The PV Theorem-3.1 sparsity hypothesis `2c(k−1) < n` (the sparse end where `b(X)≤2 ∧ s(C)≤2`). | Definition |
| `AssociationScheme.Smax` | 156-157 | **§S.4.** The basis relations of maximum valency `k`. | Definition |
| `AssociationScheme.InSmax` | 159-160 | Membership predicate for `Smax` (`valency s = k`). | Definition |
| `AssociationScheme.mem_Smax_iff` | 162-163 | `s ∈ Smax ↔ InSmax s`. | — |
| `AssociationScheme.card_relNeighbors_of_inSmax` | 165-168 | A maximum-valency relation has out-degree exactly `k` from any vertex. | — |
| `AssociationScheme.smaxAdj` | 170-171 | **§S.4.** The `smax`-graph adjacency: some maximum-valency relation joins the two points. | Definition |
| `AssociationScheme.smaxAdj_symm` | 173-176 | `smax` is symmetric. | — |
| `AssociationScheme.SmaxConnected` | 178-179 | Connectedness of the `smax` graph (`ReflTransGen smaxAdj` total). | Definition |
| `AssociationScheme.saAdj` | 181-185 | **§S.4.** The local-rigidity relation `sα` on `αsmax`: the colored triangle `{α,β,γ}` is forced (`c^{r(α,γ)}_{r(α,β),r(β,γ)}=1`). | Definition |
| `AssociationScheme.SaConnected` | 187-192 | Connectedness of `sα` on `αsmax` (`ReflTransGen (saAdj α)` total on smax-neighbours). | Definition |
| `AssociationScheme.pu` | 194-199 | **§S.4.** The pair-count `pᵤ(δ)` = ordered distinct `(β,γ)∈αu×αu` with `r(β,δ)=r(γ,δ)` (the §3 counting workhorse). | Definition, `noncomputable` |
| `AssociationScheme.sum_intersectionNumber_eq_valency` | 207-223 | **§S.5.** The homogeneous summation identity `Σ_w c^v_{uw} = n_u`. | — |
| `AssociationScheme.pu_eq` | 234-245 | Reformulates `pᵤ(δ)` over `Finset.offDiag` of the neighbour set `αu`. | — |
| `AssociationScheme.sum_pu_le` | 252-292 | **PV (19) / §S.6.** `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c` (double-count swap + per-pair `c(r)≤c(X)` bound). The workhorse upper bound for Lemma 3.6. | — |
| `AssociationScheme.pu_eq_sum` | 301-337 | **PV (20) / §S.7.** `pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)` (`v=r(α,δ)`) — the bridge from the pair-count to intersection numbers. | — |
| `AssociationScheme.valency_mul_intersectionNumber` | 346-424 | **PV eq. (4) / §S.8.** The homogeneous triangle identity `n_k·c^k_{ij} = n_i·c^i_{kj}` (apex double-count, no `n`-cancellation). | — |
| `AssociationScheme.saAdj_symm` | 426-457 | §S.8 The local-rigidity relation `sα` is symmetric (via the triangle identity), so its components are a genuine equivalence. | — |
| `AssociationScheme.valency_le_pu_of_forall_ne_one` | 467-484 | **Lemma 3.5(1) core.** `(∀w, c^v_{uw}≠1) ⟹ pᵤ(δ) ≥ n_u`. Both halves of 3.5(1) supply `≠1` into this. | — |
| `AssociationScheme.intersectionNumber_ne_one_of_valency_lt` | 486-506 | `n_v < n_u ⟹ c^v_{uw} ≠ 1` (a `1` would force `n_u ≤ n_v` via the triangle identity). | — |
| `AssociationScheme.valency_le_pu_of_valency_lt` | 508-513 | **Lemma 3.5(1), `n_u>n_v` half:** `n_v<n_u ⟹ pᵤ(δ) ≥ n_u`. Powers Lemma 3.6's *smax* branch. | — |
| `AssociationScheme.exists_small_closed_of_not_connected` | 523-556 | **§S.10 (generic).** A `ReflTransGen`-disconnected symmetric relation has a nonempty adjacency-closed vertex set of size `≤ n/2`. Reused for the `smax` and `sα` graphs. | — |
| `AssociationScheme.exists_inSmax` | 558-562 | `Smax` is nonempty (the `k(X)` sup is attained). | — |
| `AssociationScheme.smaxConnected_of_sparseSeparable` | 564-615 | **Lemma 3.6, *smax* half:** `SparseSeparable ∧ k≥2 ⟹ SmaxConnected`. Small-closed-set extraction + the `n_u>n_v` bound + the (19) estimate. | — |
| `AssociationScheme.exists_saAdj_of_intersectionNumber_eq_one` | 624-639 | **§S.11 — the graph↔counting bridge.** `c^v_{uw}=1` (with `u,v∈Smax`) ⟹ some `αu`-vertex is `sα`-adjacent to `δ`. The link between `saAdj` and intersection numbers underpinning the `sα`-component analysis. | — |
| `AssociationScheme.valency_le_pu_of_no_saAdj` | 641-650 | **Lemma 3.5(1), `n_u=n_v` half:** if `u,v∈Smax` and no `αu`-vertex is `sα`-adjacent to `δ`, then `pᵤ(δ) ≥ n_u`. | — |
| `AssociationScheme.reflTransGen_saAdj_symm` | 661-665 | §S.12 The `sα`-component relation `ReflTransGen (saAdj α)` is symmetric — an equivalence. | — |
| `AssociationScheme.saComp` | 667-672 | §S.12 The `sα`-component of `β` within `αsmax`, as a `Finset` — the `ReflTransGen (saAdj α)`-class. | Definition, `noncomputable` |
| `AssociationScheme.mem_saComp` | 674-677 | §S.12 Membership: `γ ∈ saComp α β ↔ ReflTransGen (saAdj α) β γ`. | — |
| `AssociationScheme.self_mem_saComp` | 679-680 | §S.12 `β ∈ saComp α β`. | — |
| `AssociationScheme.saComp_eq_of_mem` | 682-688 | §S.12 Two vertices in the same `sα`-component have equal component `Finset`s. | — |
| `AssociationScheme.compsOf` | 690-692 | §S.12 The component set `C(u)` — the `sα`-components meeting `αu` (the `u`-neighbours of `α`). | Definition, `noncomputable` |
| `AssociationScheme.saComp_mem_compsOf` | 694-696 | §S.12 For `β ∈ αu`, `saComp α β ∈ C(u)`. | — |
| `AssociationScheme.sum_card_fiber_saComp` | 698-706 | §S.12 The `αu`-partition by component: `|αu| = Σ_{c∈C(u)} |{β∈αu : saComp α β = c}|` — foundation of the minimum-component bound. | — |
| `AssociationScheme.transport_step` | 718-752 | §S.13 The transport step: an `sα`-edge `b→c` carries any `γ''` matching `b`'s relation to `α` to a `γ'` matching `c`'s, along an `sα`-edge (forward determinacy from the same `c=1` via the triangle identity). | — |
| `AssociationScheme.transport` | 754-764 | §S.13 The path transport: a reference `sα`-path transports any `β'` of matching `r(α,·)` to a matching endpoint, along an `sα`-path. | — |
| `AssociationScheme.compsOf_subset_of_path` | 766-784 | §S.13 Lemma 3.4 (subset): an `sα`-path from `αu` to `αv` ⟹ every component meeting `αu` also meets `αv`. | — |
| `AssociationScheme.compsOf_eq_of_inter_nonempty` | 786-800 | §S.13 **Lemma 3.4 (set-equality).** `C(u) ∩ C(v) ≠ ∅ ⟹ C(u) = C(v)`. | — |
| `AssociationScheme.saAdj_of_mem_of_intersectionNumber_eq_one` | 811-818 | §S.14 The bridge refinement: for `β ∈ αu`, `c^v_{u,r(β,δ)} = 1` is exactly the `saAdj α β δ` condition. | — |
| `AssociationScheme.pu_ge_card_notComp` | 820-871 | §S.14 **Lemma 3.5(2) core.** `|{β∈αu : saComp α β ≠ saComp α δ}| ≤ pu(δ)` — each such `β` (not `sα`-adjacent to `δ`) pairs with a `pu`-partner. | — |
| `AssociationScheme.pu_eq_of_relOfPair_eq` | 873-876 | §S.14 `pu α u δ` depends on `δ` only through `relOfPair α δ`. | — |
| `AssociationScheme.exists_minComp_card` | 878-907 | §S.14 The minimum-component bound: `|C(u)|≥2` ⟹ a component `C₀` with `2·|αu∩C₀| ≤ |αu|`. | — |
| `AssociationScheme.lemma35_2` | 909-939 | §S.14 **Lemma 3.5(2).** `nu=nv ∧ C(u)=C(v) ∧ |C(u)|>1 ⟹ nu ≤ 2·pu(δ)` for `δ∈αv`. | — |
| `AssociationScheme.valency_le_two_pu_of_card_compsOf` | 948-973 | §S.15 The `≥k/2` per-point bound (Lemma 3.5(1)+(2) combined): `u∈Smax ∧ |C(u)|≥2 ⟹ nu ≤ 2·pu(δ)` for every `δ`. | — |
| `AssociationScheme.card_compsOf_eq_one` | 975-1006 | §S.15 **PV claim (23).** Under sparsity and `k≥2`, every `u∈Smax` has `|C(u)|=1` — `αu` lies in a single `sα`-component. | — |
| `AssociationScheme.saComp_closed` | 1016-1020 | §S.16 `sα`-components are closed under `saAdj`. | — |
| `AssociationScheme.mem_saComp_of_card_one` | 1022-1029 | §S.16 With `|C(u)|=1`, all of `αu` lies in the component of any `w∈αu`. | — |
| `AssociationScheme.valency_le_pu_of_closed_notMem` | 1031-1045 | §S.16 For `u∈Smax` and a closed `C ⊇ αu`, any `δ∉C` has `pu(δ) ≥ nu` (Lemma 3.5(1)). | — |
| `AssociationScheme.false_of_closed_subset` | 1047-1082 | §S.16 The contradiction engine: a closed `C ⊇ αu` with `2|C|≤n` is impossible under sparsity. | — |
| `AssociationScheme.saConnected_of_sparseSeparable` | 1084-1111 | §S.16 **Lemma 3.6 (sα half).** `SparseSeparable ∧ k≥2 ⟹ ∀α, SaConnected α` — the last open hypothesis of the PV-Thm-3.1 bridge. | — |
| `AssociationScheme.AlgIso` | 1135-1145 | §S.17 An **algebraic isomorphism** `X→Y`: a relation bijection preserving the identity relation and all intersection numbers (P–V §2.5 eq. (14)) — the morphism of the separability theory. | Structure |
| `AssociationScheme.AlgIso.InducedBy` | 1147-1150 | §S.17 An algebraic isomorphism is **induced** by a vertex permutation carrying each `R_r` onto `R'_{φr}` — an honest isomorphism realising `φ`. | Definition |
| `AssociationScheme.Separable` | 1152-1155 | §S.17 **Separability (`s(X)=1`).** Every algebraic isomorphism out of `X` is induced by an isomorphism — the conclusion of Ponomarenko Thm 4.1 and the Thm-4.1-program target. | Definition |
| `AssociationScheme.idAlgIso` | 1157-1161 | §S.17 The identity algebraic isomorphism (sanity inhabitant of `AlgIso`). | Definition |
| `AssociationScheme.idAlgIso_inducedBy_refl` | 1163-1164 | §S.17 `idAlgIso` is induced by the identity permutation. | — |
| `AssociationScheme.SeparableParam` | 1166-1170 | §S.17 **Theorem 5.1's hypothesis** — the parameter inequality `3c(k−1)k < n` (stricter than `SparseSeparable`) guaranteeing `Separable X`. | Definition |
## ChainDescent/CoherentConfig.lean

The **general (multi-fiber) coherent-configuration substrate** — Stage 0/1 of the general-CC
separability build (`docs/chain-descent-general-cc-separability.md`; Stage-0 decision + increment log
in its §8). Lands the `CoherentConfig` type (colour-function presentation, fibers *derived*), the
homogeneous coercion, the general-CC `AlgIso`/`Separable` (the §S.17 widening the Stage-1.3 soundness
gate demanded), the probe-validated Thm 4.1 hypothesis predicates (`Theorem41ConditionsProbe.cs`),
the cited `Theorem41Statement` (the staging-fallback carry), and the point extension as a universal
property — **plus its §CC.8 construction (Stage 1.2, 2026-06-12)**: the coherent closure
`pointExtension X T` via a pair-refinement saturation (setoid `pairStep`, representative-indexed
counts, `n²`-round pigeonhole), discharging `IsPointExtension` constructively
(`isPointExtension_pointExtension` / `exists_isPointExtension` / `isPointExtension_unique`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CoherentConfig` | 48-74 | **The general (multi-fiber) coherent configuration** on `Fin n`, by its colour function `relOf : Fin n → Fin n → Fin rank` + four axioms (classes nonempty, transpose well-defined, reflexive classes purely diagonal, intersection numbers constant). The central missing object the live build creates; the point extension `X_T` (non-homogeneous) is why it exists. | Structure |
| `CoherentConfig.repPair` | 82-84 | A chosen representative pair of the class `t` (from `relOf_surj`). | Definition, `noncomputable` |
| `CoherentConfig.relOf_repPair` | 86-88 | The representative lies in its class: `relOf (repPair t).1 (repPair t).2 = t`. | — |
| `CoherentConfig.interNum` | 90-94 | The **intersection number** `c^t_{a,b}` of a general CC, computed at the chosen representative. | Definition, `noncomputable` |
| `CoherentConfig.interNum_eq` | 96-101 | The defining property: *any* pair of class `t` computes `interNum a b t` (via `inter_card_eq`). | — |
| `CoherentConfig.transposeRel` | 103-105 | The **transpose class** `t*` (class of the reversed pairs). | Definition, `noncomputable` |
| `CoherentConfig.relOf_swap_eq` | 107-110 | Reversing any pair of `t` lands in `t*`: `relOf u v = t → relOf v u = transposeRel t`. | — |
| `CoherentConfig.transposeRel_transposeRel` | 112-118 | Transposition is an involution on classes: `t** = t`. | `@[simp]` |
| `CoherentConfig.relOf_diag_left_eq` | 127-143 | **Fibers are coherent (derived, not axiomatized).** Same class ⟹ same source fiber: a class determines the reflexive class of its sources, from `diag_eq` + `inter_card_eq` alone. Makes the `IsPointExtension` universal property complete (`T`-singleton fibers ⟹ refines the `T`-individualized start). | — |
| `CoherentConfig.relOf_diag_right_eq` | 145-148 | Same class ⟹ same target fiber (via `transpose_eq`). | — |
| `CoherentConfig._root_.ChainDescent.AssociationScheme.toCoherentConfig` | 156-187 | **The homogeneous coercion** `AssociationScheme → CoherentConfig` (colour function = `relOfPair`), conditional on the seal's existing "every relation occurs" antecedent `hne` (the scheme axioms don't force nonempty relations; `relOf_surj` does). Reconciles the two substrates. | Definition, `noncomputable` |
| `CoherentConfig.AlgIso` | 197-206 | **Algebraic isomorphism of general CCs** — a relation bijection preserving all intersection numbers (Ponomarenko arXiv:2006.13592 §2.5 eq. (8), stated bare as in the paper). The general-CC widening of §S.17's `AlgIso`. | Structure |
| `CoherentConfig.AlgIso.InducedBy` | 208-212 | `φ` is **induced** by the vertex permutation `f`: `Y.relOf (f u) (f v) = φ (X.relOf u v)` — an honest isomorphism realising `φ`. | Definition |
| `CoherentConfig.idAlgIso` | 214-217 | The identity algebraic isomorphism (sanity inhabitant). | Definition |
| `CoherentConfig.idAlgIso_inducedBy_refl` | 219-220 | `idAlgIso` is induced by the identity permutation. | — |
| `CoherentConfig.Separable` | 222-225 | **Separability (`s(X)=1`), general-CC form**: every algebraic isomorphism out of `X` is induced. Partner `Y` quantifies over **all** `CoherentConfig n` (multi-fiber included) — the deliberate widening of §S.17's homogeneous `Separable`, resolving the Stage-1.3 soundness gate (the transport (B) consumes extension alg-isos, which are multi-fiber). | Definition |
| `CoherentConfig.SeparablePointed` | 227-234 | **Pointed separability at `μ`** — Thm 4.1's actual (stronger) conclusion: the inducing `f` is steerable onto any prescribed `μ'` with matching reflexive class. What the transport (B) wants (build doc Stage 2.2(b)). | Definition |
| `CoherentConfig.InComplexProduct` | 244-245 | Membership in the complex product `a·b`: `interNum a b w ≠ 0`. | Definition |
| `CoherentConfig.Dominates` | 247-251 | **Point domination `δ ← λ`** w.r.t. `μ` (paper (9)/(11)): `c^{r(μ,λ)}_{r(μ,δ),r(δ,λ)} = 1` — `λ` pins `δ` uniquely. Exactly the probe's check. | Definition |
| `CoherentConfig.DominationCondition` | 253-255 | **Thm 4.1 condition (i)**: every `Δ` with `|Δ| ≤ 4` is dominated by some `λ`. Probe-validated: holds on the residue's one-point extension, fails on the residue itself. | Definition |
| `CoherentConfig.IsCoupleExtension` | 257-272 | The triangle `(x̄,ȳ,z̄)` is an **`m`-extension of the couple** `Qμ(α,β,γ)` (paper §3 (16)/(17)): product membership + the three product-intersection uniqueness clauses. First-order in intersection numbers — **no `Ωᵐ` substrate needed to state Thm 4.1**. | Definition |
| `CoherentConfig.CoupleExtensionCondition` | 274-279 | **Thm 4.1 condition (ii)**: every couple `Qμ(α,β,γ)` has an `m`-extension with `μm ≠ ∅`. The probe found the witness always *geometric* on the residue's extension (Lemma 5.3's λ-triangle shape) — a future discharge can construct it. | Definition |
| `CoherentConfig.Theorem41Hypotheses` | 281-283 | Conditions (i) + (ii) bundled — the hypotheses of the cited Thm 4.1, as probed. | Definition |
| `Theorem41Statement` | 287-293 | **The cited Theorem 4.1** (Ponomarenko arXiv:2006.13592 §4) as a theorem-statement `Prop` — the staging-fallback carry, per the G3 pattern (cited results are hypotheses, never fresh `axiom`s): hypotheses ⟹ `SeparablePointed`. A future increment proves it (Stage 3, Route α/β) or carries it into the seal capstone. | Definition |
| `CoherentConfig.Refines` | 308-310 | `Y` refines `X`: `Y`'s pair partition is finer. The fission order the point extension minimizes over. | Definition |
| `CoherentConfig.Refines.refl` | 312 | Refinement is reflexive. | — |
| `CoherentConfig.Refines.trans` | 314-316 | Refinement is transitive. | — |
| `CoherentConfig.SingletonFiber` | 318-320 | `t` is a singleton fiber of `Y` (no other point shares its reflexive class). | Definition |
| `CoherentConfig.IsPointExtension` | 322-327 | **The point extension `X_T` as a universal property**: a coherent fission of `X` with `T`-singleton fibers, coarsest among all such. Complete by `relOf_diag_left_eq` (fiber coherence ⟹ such a fission automatically respects the `T`-flags). The closure's *construction* (pair-refinement saturation) is a later increment; consumers key on this predicate. | Definition |
| `CoherentConfig.ExtensionSeparable` | 329-334 | **The staging-fallback target predicate**: every point extension of `X` at `T` is separable — the separability-level hypothesis the transport (B) consumes (build doc Stage 2.2), supplied for schurian residues by Thm 4.1 (cited or proved) per the probe's verdict. | Definition |
| `CoherentConfig.discreteCC` | 338-358 | The **discrete** CC (every ordered pair its own class, via `finProdFinEquiv`) — the finest CC; inhabitant witness. | Definition |
| `CoherentConfig.discreteCC_refines` | 360-365 | The discrete CC refines every CC — with `discreteCC_singletonFiber`, the family `IsPointExtension` minimizes over is nonempty for every `(X,T)`. | — |
| `CoherentConfig.discreteCC_singletonFiber` | 367-372 | Every point is a singleton fiber of the discrete CC. | — |
| `CoherentConfig.extFlag` | 396-398 | §CC.8 The `T`-individualization flag: `t ∈ T` carries the unique flag `t.val + 1`, everything else `0` — the `individualizedColouring` pattern on the closure's start, so distinct `T`-points get distinct classes. | Definition |
| `CoherentConfig.extFlag_eq_of_mem` | 400-407 | Flag injectivity at `T`-points: a vertex sharing `t`'s flag (`t ∈ T`) is `t` — the source of the closure's `T`-singleton-fiber property. | — |
| `CoherentConfig.extInitSetoid` | 409-415 | §CC.8 The initial pair partition of the closure: `X`'s classes split by the endpoint flags — the `T`-individualized starting colouring, on ordered pairs. | Definition |
| `CoherentConfig.pairCount` | 417-422 | §CC.8 The intersection count of `(u, v)` against the classes of the reference pairs `x`, `y` under a pair partition `s`. Representative-indexed (reference *pairs* name their classes), so the iteration never materializes a quotient or an encoding. | Definition, `noncomputable` |
| `CoherentConfig.pairStep` | 424-430 | §CC.8 One pair-refinement round: split each class by all the intersection counts — the WL-on-pairs step, in setoid form. | Definition |
| `CoherentConfig.pairIter` | 432-433 | §CC.8 The saturation chain `pairStep^[k]` from the `T`-individualized start. | Definition |
| `CoherentConfig.pairIter_zero` | 435 | `pairIter 0` is the initial partition (definitional). | — |
| `CoherentConfig.pairIter_succ` | 437-438 | One-step unfolding: `pairIter (k+1) = pairStep (pairIter k)`. | — |
| `CoherentConfig.pairStep_le` | 440-441 | The step refines: `pairStep s ≤ s` (split-only, one round). | — |
| `CoherentConfig.pairIter_le_init` | 443-450 | Every stage refines the start (split-only across the chain) — carries the relOf/flag facts of the initial partition to the fixpoint, where they become `diag_eq` and the `T`-singletons. | — |
| `CoherentConfig.numClasses` | 454-455 | §CC.8 The class count of a pair partition (`Nat.card` of its quotient) — the stabilization monovariant; the pair analogue of `CascadeAffine §S-stab`'s `numCells`. | Definition, `noncomputable` |
| `CoherentConfig.quotMap` | 457-460 | The canonical surjection between quotients of comparable partitions (finer → coarser), via `Quotient.lift`. | Definition |
| `CoherentConfig.quotMap_surjective` | 462-466 | `quotMap` is surjective — every coarse class is hit by a fine one. | — |
| `CoherentConfig.numClasses_le_of_le` | 468-471 | Refining cannot lose classes: `s' ≤ s ⟹ numClasses s ≤ numClasses s'` (the coarser quotient receives the surjection `quotMap`). | — |
| `CoherentConfig.le_of_numClasses_le` | 473-485 | **The rigidity half of the pigeonhole**: a refinement with no more classes is no refinement — `s' ≤ s` with `numClasses s' ≤ numClasses s` forces `s ≤ s'` (a surjection between equal-card finite quotients is injective). The pair analogue of `samePartition_of_refines_of_numCells_le`. | — |
| `CoherentConfig.numClasses_le_sq` | 487-490 | The class count is at most `n²` (quotient of `Fin n × Fin n`). | — |
| `CoherentConfig.numClasses_growth` | 492-512 | **Strict growth before the fixpoint**: `k` non-fixed rounds force at least `k` extra classes — the strictly-increasing monovariant powering the pigeonhole. | — |
| `CoherentConfig.exists_pairIter_fixed` | 514-530 | **The chain reaches a `pairStep` fixpoint within `n²` rounds** — growth (`numClasses_growth`) against the `n²` bound (`numClasses_le_sq`); `n = 0` is vacuously fixed at round 0. | — |
| `CoherentConfig.stableSetoid` | 532-533 | §CC.8 The stable pair partition `pairIter (n²)` — **the coherent closure** of the `T`-individualized start. | Definition |
| `CoherentConfig.pairStep_stableSetoid` | 535-543 | The stable partition is a genuine `pairStep` fixpoint: the fixpoint reached at some `k ≤ n²` propagates to round `n²` by `Function.iterate_fixed`. | — |
| `CoherentConfig.stableSetoid_pairCount` | 545-552 | **The fixpoint property, extracted**: same stable class ⟹ *all* intersection counts agree — this IS the coherence axiom of the closure, read off the fixed point. | — |
| `CoherentConfig.pairCount_swap` | 556-575 | Counts of the swapped pair under a swap-stable partition are a pure reindexing: `pairCount s v u x y = pairCount s u v y.swap x.swap` — the combinatorial core of the closure's transpose axiom. | — |
| `CoherentConfig.pairIter_swap` | 577-596 | **Every stage is swap-stable** (the transpose invariant): the initial partition respects `Prod.swap` (`X.transpose_eq` + flag swap), and `pairCount_swap` carries it through each round — yields the closure's `transpose_eq`. | — |
| `CoherentConfig.pairCount_eq_of_zrel` | 600-716 | **The counting heart of the universal property.** A coherent fission `Z` whose classes refine the pair partition `s` has `s`-counts constant on `Z`-classes: decompose fiberwise over `Z`'s class pairs (`card_eq_sum_card_fiberwise`), the `s`-conditions are constant on each fiber (transport along `hle`), and `Z.inter_card_eq` equates the fibers. The §CC.2 fiber-coherence argument generalized, exactly as the build doc's Stage-1.2 plan predicted. | — |
| `CoherentConfig.zrel_le_pairIter` | 718-748 | **A coherent fission of `X` with `T`-singleton fibers refines every stage of the chain** — base case from `Refines Z X` + derived fiber coherence (`relOf_diag_left_eq` reads the flags off `Z`'s classes via the singleton hypothesis); inductive step = `pairCount_eq_of_zrel`. The closure-is-minimum induction. | — |
| `CoherentConfig.stableEquiv` | 752-755 | The class indexing of the stable partition (`Finite.equivFin` on its quotient). | Definition, `noncomputable` |
| `CoherentConfig.stableEquiv_eq_iff` | 757-761 | Index equality ⟺ stable-setoid relation — the unfolding bridge between `pointExtension.relOf` and `stableSetoid`. | — |
| `CoherentConfig.pointExtension` | 763-816 | **The point extension, CONSTRUCTED (Stage 1.2(a))**: the stable pair partition as a `CoherentConfig` — surjectivity from the quotient, `transpose_eq` from `pairIter_swap`, `diag_eq` + the flags from `pairIter_le_init`, `inter_card_eq` from the fixpoint counts (`stableSetoid_pairCount`). | Definition, `noncomputable` |
| `CoherentConfig.pointExtension_relOf_eq_iff` | 818-821 | `pointExtension`'s colour function realizes exactly the stable partition. | — |
| `CoherentConfig.isPointExtension_pointExtension` | 823-838 | **Stage 1.2(a) headline: the construction satisfies the universal property** — `pointExtension X T` refines `X`, makes every `t ∈ T` a singleton fiber, and is coarsest among coherent fissions doing so (`zrel_le_pairIter`). `IsPointExtension` is discharged constructively. | — |
| `CoherentConfig.exists_isPointExtension` | 840-842 | The fission family `IsPointExtension X T` quantifies over is inhabited for **every** `(X, T)` — so `ExtensionSeparable` is never vacuous. | — |
| `CoherentConfig.isPointExtension_unique` | 844-848 | Stage 1.2(b): any two point extensions mutually refine (same pair partition) — uniqueness up to relabelling, straight from the universal property. | — |
| `CoherentConfig.SeparablePointed.exists_aut_of_fiber_eq` | 866-872 | §CC.9 **The pointed conclusion at the identity algebraic isomorphism**: pointed separability of `Y` at `u` realizes every same-fiber `u'` by a class-preserving vertex automorphism with `f u = u'`. The citation-free heart of the Stage-2 transport. | — |
| `CoherentConfig.IsPointExtension.aut_fixes` | 874-878 | An automorphism of a point extension fixes every individualized point (its fiber is a singleton, and automorphisms preserve fibers). | — |
| `CoherentConfig.Refines.aut_descends` | 880-884 | An automorphism of a fission is an automorphism of the base configuration (coarser classes are unions of finer ones). | — |
| `CoherentConfig.fiberTwin_realized_of_separablePointed` | 886-894 | §CC.9 **THE STAGE-2 TRANSPORT CORE (citation-free).** Pointed separability of a point extension realizes every same-fiber pair `(u,u')` by a `T`-fixing automorphism of the BASE configuration carrying `u ↦ u'` — `exists_aut_of_fiber_eq` + `aut_fixes` + `aut_descends` composed. What the seal's sink consumes, at the fiber keying. | — |
| `CoherentConfig.extension_complete_of_separablePointed` | 896-916 | §CC.9 At a rigid base (only the identity `T`-fixing automorphism), pointed separability of the extension at every non-singleton fiber forces the extension **complete** (all fibers singleton) — the fiber-level `b(X) ≤ b(G)` collapse. Singleton fibers (e.g. the `T`-points, exactly where the probe saw the Thm-4.1 conditions fail) are exempt by construction. | — |
| `CoherentConfig.interNum_eq_one_of_forcedUnique` | 934-945 | §CC.10 **The forced-triangle criterion on a general CC (forward).** `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` when `γ` is the unique `u` sharing `γ`'s relation-profile to both `α` and `β`. Pure counting (`inter_card_eq`); the `CoherentConfig` mirror of `CascadeAffine`'s scheme-level lemma, so the δ′ closure runs on the point extension `X_T` (where the `c=1` triangles the n≥25 residue needs reappear). Axiom-clean. | — |
| `CoherentConfig.forcedUnique_of_interNum_eq_one` | 947-963 | §CC.10 **The forced-triangle criterion, reverse.** `c = 1 ⟹` the profile-uniqueness pinning `γ` (the only `u` with `γ`'s profile to `α,β`). The half the singleton-fiber propagation consumes. Axiom-clean. | — |
| `CoherentConfig.DominatorReachable` | 965-971 | §CC.10 **The forced-triangle dominator closure of `T` on a general CC** — the δ′ `DominatorReachable` lifted from `AssociationScheme` to `CoherentConfig`, so it runs on `X_T = pointExtension X T` (probe finding: scheme-level forced triangles vanish at n≥25; the extension's finer colours carry them). `base`: `t∈T`; `step`: `γ` pinned by a `c=1` triangle against two reachable points. | Inductive |
| `CoherentConfig.dominatorReachable_step_of_unique` | 973-978 | §CC.10 The CC `DominatorReachable` step builder from the profile-uniqueness pinning. Axiom-clean. | — |
| `CoherentConfig.dominatorReachable_of_rank` | 980-996 | §CC.10 **The single-base closure from a pinning rank, on a general CC** (mirror of the scheme engine): a well-founded `rk` with rank-0 in `T` and every positive-rank `γ` profile-pinned by two strictly-lower-rank points ⟹ `∀ v, DominatorReachable X T v`. Axiom-clean. | — |
| `CoherentConfig.Sharp` | 998-1004 | §CC.10 **`Sharp`** — the coherent-closure refinement property: a singleton fiber sees the whole fiber structure (same-fiber points have the same relation to any singleton fiber). FALSE for a general CC, TRUE for the point extension `X_T`; carried as the named hypothesis the discreteness payoff needs (the isolated next discharge: `Sharp (pointExtension X T)`). | Definition |
| `CoherentConfig.singletonFiber_of_dominatorReachable` | 1006-1024 | §CC.10 **Forced-triangle reachability propagates the singleton-fiber property** (modulo `Sharp`): a point reachable from a set of singleton fibers is itself a singleton fiber — `Sharp` makes a same-fiber twin share `γ`'s relations to the pinning `α,β`, and `c=1` uniqueness forces them equal. Induction over `DominatorReachable`. Axiom-clean. | — |
| `CoherentConfig.allSingletonFiber_of_dominatorClosure` | 1026-1035 | §CC.10 **The δ′ engine on the extension: closure ⟹ all fibers singleton.** Every point reachable from `T` + `T`-points singleton fibers + `Sharp` ⟹ `X` discrete (the point extension is complete = `T` a base). The general-CC analogue of `discrete_of_dominatorClosure`; the citation-free path the n≥25 residue needs (closure on `X_T`, not the bare scheme), carrying only `Sharp`. Axiom-clean. | — |
| `CoherentConfig.sharp_pointExtension` | 1037-1082 | §CC.10 **`Sharp` holds for the point extension — the lone carried δ′-engine hypothesis, discharged.** A singleton fiber of `pointExtension X T` sees the whole fiber structure (same-fiber `u,u'` have equal relation to it). False for a general CC, true here because the construction is a `pairStep` fixpoint: the `a`-isolating count `#{w : r(u,w)=r(u,a) ∧ r(w,u)=r(a,u)}` is `1` (`relOf_diag_right_eq` + singleton ⟹ only `w=a`), and `stableSetoid_pairCount` transports `=1` to `u'`, pinning `r(a,u')=r(a,u)`. Axiom-clean. | — |
| `CoherentConfig.allSingletonFiber_of_dominatorClosure_pointExtension` | 1084-1095 | §CC.10 **The δ′ closure is complete on the extension, unconditionally.** Every point `DominatorReachable` from `T` in `pointExtension X T` ⟹ the extension is discrete (all singleton fibers) = `T` a base. Both auxiliary hypotheses of `allSingletonFiber_of_dominatorClosure` discharged for `X_T`: `Sharp` by `sharp_pointExtension`, the `T`-singleton-fibers by `isPointExtension_pointExtension`. Sole remaining input is the closure `hclo` itself (the open `c(X_T)` content). Axiom-clean. | — |
| `CoherentConfig.indistinguishingNumberOf` | 1108-1111 | §CC.11 (A1) **Indistinguishing number of a class `r` on a general CC**: `c(r) = Σ_b c^r_{b*,b}` (`b* = transposeRel b` — the non-symmetric CC form of `Separability.indistinguishingNumberOf`). | Definition, `noncomputable` |
| `CoherentConfig.indistinguishingNumberOf_eq_card` | 1113-1137 | §CC.11 (A1) **PV eq. (7), CC form.** For `(α,β)∈r`, `c(r) = |{γ : relOf γ α = relOf γ β}|` — the count of `γ` failing to distinguish `α` from `β`; the geometric shape the §S.16 connectivity argument consumes. Partition by `b=relOf γ α`, each fiber `= c^r_{b*,b}` via `relOf_swap_eq`. Axiom-clean. | — |
| `CoherentConfig.IsReflexive` | 1139-1143 | §CC.11 (A1) a class is reflexive/diagonal iff some loop lies in it (`∃u, relOf u u = r`); `c(X)` maxes over non-reflexive classes. | Definition |
| `CoherentConfig.indistinguishingNumber` | 1145-1147 | §CC.11 (A1) **The indistinguishing number `c(X)`** of a general CC — `max_{r non-reflexive} c(r)`. The `c` of the sparse bound `2c(k−1)<n` applied to the extension `X_T`. | Definition, `noncomputable` |
| `CoherentConfig.indistinguishingNumberOf_le` | 1149-1152 | §CC.11 (A1) `c(r) ≤ c(X)` for every non-reflexive class `r`. Axiom-clean. | — |
| `CoherentConfig.sourceFiber` | 1154-1158 | §CC.11 (A1) the reflexive class `relOf u u` a class `r` emanates from (well-defined by `relOf_diag_left_eq`); `R₀` on a homogeneous scheme, the source fiber on a multi-fiber CC. | Definition, `noncomputable` |
| `CoherentConfig.valency` | 1160-1164 | §CC.11 (A1) **Valency `n_r`** of a class on a general CC — its out-degree, `interNum r r* (sourceFiber r)` (the `relOf w u = r*` leg is free given `relOf u w = r`). | Definition, `noncomputable` |
| `CoherentConfig.valency_eq_card` | 1166-1177 | §CC.11 (A1) **Valency is the out-degree**: for `(u,v)∈r`, `valency r = |{w : relOf u w = r}|` (constant on the source fiber, by coherence). The CC form of `Separability.valency_eq_card`. Axiom-clean. | — |
| `CoherentConfig.maxValency` | 1179-1181 | §CC.11 (A1) **Max valency `k(X)`** of a general CC — the largest out-degree over non-reflexive classes. The `k` of the sparse bound `2c(k−1)<n` on the extension. | Definition, `noncomputable` |
| `CoherentConfig.valency_le_maxValency` | 1183-1186 | §CC.11 (A1) `n_r ≤ k(X)` for every non-reflexive class `r`. Axiom-clean. | — |
| `CoherentConfig.SparseSeparable` | 1188-1191 | §CC.11 (A1) **The PV-Thm-3.1 sparsity hypothesis `2c(k−1)<n` on a general CC** — satisfied on `X_T` (M1: `c,k=O(1)`), the citation-free `c(X_T)` route's input predicate. | Definition |
| `CoherentConfig.relOf_right_eq_iff_left` | 1204-1214 | §CC.12 (A1) **The transpose bridge** — `relOf a δ = relOf b δ ↔ relOf δ a = relOf δ b`. The non-symmetric CC's substitute for `AssociationScheme.relOfPair_symm`, letting the (19)-estimate pair-count meet `indistinguishingNumberOf_eq_card`'s left-argument form. Via `relOf_swap_eq`. Axiom-clean. | — |
| `CoherentConfig.not_isReflexive_relOf_of_ne` | 1216-1221 | §CC.12 (A1) A non-diagonal pair lies in a non-reflexive class: `a ≠ b → ¬ IsReflexive (relOf a b)` (a reflexive class is purely diagonal, `diag_eq`). Supplies the `c(r) ≤ c(X)` step of the (19) estimate. Axiom-clean. | — |
| `CoherentConfig.card_relNeighbors_le_maxValency` | 1223-1239 | §CC.12 (A1) The `u`-out-neighbour set of `α` has `≤ k(X)` elements for non-reflexive `u` — the CC replacement for homogeneity's exact `card = k` (empty when `α` is outside `u`'s source fiber, else `valency u ≤ maxValency`). Bounds `A.card` in the (19) estimate. Axiom-clean. | — |
| `CoherentConfig.pu` | 1241-1247 | §CC.12 (A1) **The pair-count `pᵤ(δ)`** (CC form) — ordered distinct `(β,γ)` both `u`-out-neighbours of `α` that `δ` fails to distinguish (`relOf β δ = relOf γ δ`). The §3 counting workhorse on a general CC; the CC port of `Separability.pu`. | Definition, `noncomputable` |
| `CoherentConfig.pu_eq` | 1249-1260 | §CC.12 (A1) Reformulation of `pᵤ(δ)` over the off-diagonal of the `u`-neighbour set `αu`. Axiom-clean. | — |
| `CoherentConfig.sum_pu_le` | 1267-1311 | §CC.12 (A1) **The global estimate (19), CC form** — `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c` for a non-reflexive class `u` and any `Δ`. Double-count swap (`sum_comm`), per-pair bound by `c(relOf β γ) ≤ c(X)` through `relOf_right_eq_iff_left` into `indistinguishingNumberOf_eq_card`, and `≤ k(k−1)` off-diagonal neighbour pairs (`card_relNeighbors_le_maxValency`). The CC port of `Separability.sum_pu_le`; the §S.16 connectivity workhorse. Axiom-clean. | — |
| `CoherentConfig.pu_eq_sum` | 1323-1353 | §CC.13 (A1) **Identity (20), CC form** — `pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)` (`v = relOf α δ`). Fiber `pᵤ(δ)` by the common class `w = relOf β δ`; each fiber is the off-diagonal of the `interNum u w v`-element set `{β : relOf α β = u ∧ relOf β δ = w}`. The bridge from the pair-count to intersection numbers (the input both Lemma-3.5 halves consume); the CC port of `Separability.pu_eq_sum`, with the fiber-card step direct from the colour-function `interNum_eq` (no transpose subtlety here). Axiom-clean. | — |
| `CoherentConfig.outDeg_mul_interNum` | 1366-1440 | §CC.14 (A1) **The triangle double-count (out-degree form, unconditional)** — `(deg_k x)·c^k_{i,j} = (deg_i x)·c^i_{k,j*}` (`deg_r x = #{w : relOf x w = r}`, `j* = transposeRel j`). Counting triangles `x →ᵢ y →ⱼ z`, `x →ₖ z` by the `z`-leg vs the `y`-leg. The `j*` on the right is the non-symmetric CC's correction to the homogeneous `valency_mul_intersectionNumber` (where scheme symmetry flipped the `j`-leg for free). Axiom-clean. | — |
| `CoherentConfig.valency_mul_interNum` | 1442-1450 | §CC.14 (A1) **The triangle identity (valency form), transpose-aware** — `n_k·c^k_{i,j} = n_i·c^i_{k,j*}`, given an apex `x` realizing both source fibers (`relOf x y₀ = i`, `relOf x z₀ = k`). The CC analogue of `Separability.valency_mul_intersectionNumber`; consumed by the §S.9 `≠1` argument and (next increment) `saAdj_symm`. Axiom-clean. | — |
| `CoherentConfig.InSmax` | 1465-1466 | §CC.15 (A1) A class is **max-valency** (`InSmax r := valency r = k(X)`) — the CC `Smax`-membership predicate. | Definition |
| `CoherentConfig.smaxAdj` | 1468-1470 | §CC.15 (A1) The **`smax` graph** adjacency (out-going): `relOf a b` is max-valency. *Not* symmetric on a general CC (`n_s ≠ n_{s*}` across fibers; symmetric only within a fiber) — connectivity treatment is the next increment. | Definition |
| `CoherentConfig.SmaxConnected` | 1472-1473 | §CC.15 (A1) Connectedness of the `smax` graph (`ReflTransGen smaxAdj` total). | Definition |
| `CoherentConfig.saAdj` | 1475-1479 | §CC.15 (A1) The **local-rigidity relation `sα`** on `αsmax`: for max-valency neighbours `β,γ` of `α`, the coloured triangle is forced (`c^{r(α,γ)}_{r(α,β),r(β,γ)} = 1`). The CC port of `Separability.saAdj`. | Definition |
| `CoherentConfig.SaConnected` | 1481-1483 | §CC.15 (A1) Connectedness of `sα` on `αsmax` (`ReflTransGen (saAdj α)` total on `α`'s max-valency neighbours). | Definition |
| `CoherentConfig.saAdj_symm` | 1485-1500 | §CC.15 (A1) **`sα` is symmetric** (CC port of `Separability.saAdj_symm`, via the transpose-aware triangle identity §CC.14): both legs have valency `k`, so `valency_mul_interNum` turns `c^t_{r,s}=1` into `c^r_{t,s*}=1`, and `s* = relOf γ β` makes that the reflected triangle. Does *not* need a symmetric `smaxAdj` (legs are both out-going from `α`). Makes the `sα`-components an equivalence. Axiom-clean. | — |
| `CoherentConfig.sum_interNum_eq_outDeg` | 1511-1520 | §CC.16 (A1) **The summation identity (§S.5), out-degree form** — `Σ_w c^v_{uw} = #{z : relOf α z = u}` for any `(α,δ) ∈ v`. Equals `valency u` when `α` is a source of `u`; stated hypothesis-free. CC port of `Separability.sum_intersectionNumber_eq_valency`. Axiom-clean. | — |
| `CoherentConfig.valency_le_pu_of_forall_ne_one` | 1522-1537 | §CC.16 (A1) **Core of Lemma 3.5(1) (§S.9)** — if every middle class `w` has `c^v_{uw} ≠ 1` (`v = relOf α δ`) then `n_u ≤ pᵤ(δ)`, via `pu_eq_sum` (20) + the §S.5 summation identity. Carries the source witness `relOf α β₀ = u`. Axiom-clean. | — |
| `CoherentConfig.interNum_ne_one_of_valency_lt` | 1539-1559 | §CC.16 (A1) `n_v < n_u ⟹ c^v_{uw} ≠ 1` (`v = relOf α δ`) — a `1` would force `n_u ≤ n_v` via the triangle identity §CC.14 (the transpose `w*` it introduces is harmless: only `0`-vs-`≥1` is used). Carries the source witness `relOf α β₀ = u`. Axiom-clean. | — |
| `CoherentConfig.valency_le_pu_of_valency_lt` | 1561-1567 | §CC.16 (A1) **Lemma 3.5(1), the `n_u > n_v` half** — `n_v < n_u ⟹ n_u ≤ pᵤ(δ)` (`v = relOf α δ`); the `≠1` core fed by the triangle identity. Carries the source witness `relOf α β₀ = u`; powers Lemma 3.6's `smax` branch (§S.10, next). Axiom-clean. | — |
| `CoherentConfig.fiberSet` | 1581-1582 | §CC.17 (A1) The fiber of a reflexive class `f` as a vertex set — `{u : relOf u u = f}`. The vertex-side carrier of the fiber-size double-count. | Definition |
| `CoherentConfig.outDeg_eq_interNum` | 1584-1595 | §CC.17 (A1) **The out-degree depends only on the source fiber** — `#{w : relOf u w = r} = c^{relOf u u}_{r,r*}` for any point `u` (the `relOf w u = r*` leg is free by `relOf_swap_eq`). Generalises `valency_eq_card` (its `relOf u u = sourceFiber r` case); the reusable brick of the fiber-size identity. Axiom-clean. | — |
| `CoherentConfig.fiberSize_mul_valency` | 1597-1630 | §CC.17 (A1) **The fiber-size identity** — `|F_src(r)|·n_r = |F_tgt(r)|·n_{r*}` (`F_src(r) = fiberSet (sourceFiber r)`). Double-counts the class `{(u,v) : relOf u v = r}` by source (`outDeg_eq_interNum` + `relOf_diag_left_eq`: each source contributes `n_r` on `F_src`, `0` off it) vs. target (Fubini + `relOf_swap_eq`). Trivial under homogeneity (`F = Ω`); the genuinely-new multi-fiber lemma. Axiom-clean. | — |
| `CoherentConfig.smaxAdj_symm_of_sameFiber` | 1632-1653 | §CC.17 (A1) **`smaxAdj` is symmetric within a fiber** — `relOf a a = relOf b b ∧ smaxAdj a b → smaxAdj b a`. Same fiber ⟹ `sourceFiber (relOf a b) = sourceFiber (relOf b a)`, so the fiber-size identity cancels `|F| > 0` to give `n_{relOf a b} = n_{relOf b a}`. **The only `smaxAdj` symmetry available on a multi-fiber CC** — global `SmaxConnected` is unavailable (the §6.1 cross-fiber wall, now proven); smax connectivity localizes to a single fiber. Axiom-clean. | — |
| `CoherentConfig.dominatorReachable_of_basePinsAll` | 1668-1692 | §CC.18 (A1) **One-round closure from base pinning (CC form)** — every non-base `γ` forced-triangle-pinned by two base points `α,β ∈ T` ⟹ `∀v, DominatorReachable T v`. The `rank∈{0,1}` instance of `dominatorReachable_of_rank`; CC mirror of `CascadeAffine.dominatorReachable_of_basePinsAll`. Axiom-clean. | — |
| `CoherentConfig.basePinsAll_of_card_gt` | 1694-1766 | §CC.18 (A1) **The abundance estimate** — `(k(X)−1)·c(X) < |T| ⟹` every `γ∉T` is pinned (profile uniqueness) by some `α,β∈T`. For fixed `α∈T`, the base points failing to separate `γ` number `≤ (k−1)·c` (union bound over `≤ k−1` other `α`-neighbours, each confusion set an indistinguishing-number count `≤ c` via `indistinguishingNumberOf_eq_card` + `relOf_right_eq_iff_left`); `|T| > (k−1)c` leaves a good `β`. Axiom-clean. | — |
| `CoherentConfig.dominatorReachable_of_card_gt` | 1768-1776 | §CC.18 (A1) **A1's direct discharge** — `(k(X)−1)·c(X) < |T| ⟹ ∀v, DominatorReachable T v` (`basePinsAll_of_card_gt` ∘ `dominatorReachable_of_basePinsAll`). The citation-free "sparse ⟹ pinning rank", **skipping §S.10–§S.16**: a crude base `b(X) ≤ (k−1)c+1` (not PV's sharp `b≤2`) suffices for the δ′ engine. Axiom-clean. | — |
| `CoherentConfig.allSingletonFiber_of_card_gt` | 1778-1789 | §CC.18 (A1 capstone) **A base above the extension's threshold makes `X_T` complete** — `(k(X_T)−1)·c(X_T) < |T| ⟹` every point of `pointExtension X T` is a singleton fiber (`T` a base of `X`). Composes `dominatorReachable_of_card_gt` on `X_T` with `allSingletonFiber_of_dominatorClosure_pointExtension` (`Sharp` + `T`-singletons discharged in §CC.10). **All of A1 reduced to one `O(1)` threshold on `X_T`'s parameters — the crisp interface A2 meets.** Axiom-clean. | — |
| `CoherentConfig.indistinguishingNumber_mono` | 1800-1825 | §CC.19 (A2 interface) **`c` monotone under refinement** — `Refines Y Z ⟹ c(Y) ≤ c(Z)`. A finer config distinguishes more pairs, so each `{γ : relOf γ α = relOf γ β}` shrinks. Axiom-clean. | — |
| `CoherentConfig.maxValency_mono` | 1827-1850 | §CC.19 (A2 interface) **`k` monotone under refinement** — `Refines Y Z ⟹ k(Y) ≤ k(Z)`. A finer class has a smaller out-neighbour set. Axiom-clean. | — |
| `CoherentConfig.refines_pointExtension_of_subset` | 1852-1859 | §CC.19 (A2 interface) **Extending the base refines the extension** — `T₀ ⊆ T ⟹ pointExtension X T` refines `pointExtension X T₀`. Immediate from the universal-property minimality (`isPointExtension_pointExtension`). Axiom-clean. | — |
| `CoherentConfig.allSingletonFiber_of_card_gt_subset` | 1861-1875 | §CC.19 (**the A1+A2 padding capstone**) **A base above the *small* base's threshold makes `X_T` complete** — `T₀ ⊆ T ∧ (k(X_{T₀})−1)·c(X_{T₀}) < |T| ⟹ X_T` complete (`T` a base of `X`). The `X_{T₀}` bounds transport to `X_T` by monotonicity, so `allSingletonFiber_of_card_gt` fires. **The crisp A2 deliverable: bound `c(X_{T₀}), k(X_{T₀}) = O(1)` at one `O(1)` base, then any larger base is a base of `X`** — citation-free, no smax/sα. Axiom-clean. | — |
| `CoherentConfig.dominatorReachable_of_card_gt_subset` | 1877-1888 | §CC.19 (A2 interface) **The padded `DominatorReachable` closure — feeds the seal's `hclo` directly.** `T₀ ⊆ T ∧ (k(X_{T₀})−1)·c(X_{T₀}) < |T| ⟹ ∀v, (pointExtension X T).DominatorReachable T v` (monotone transport of the `X_{T₀}` bounds + `dominatorReachable_of_card_gt`). The brick wiring §CC.18/§CC.19 to `reachesRigidOrCameron_viaBoundedExtensionParams`. Axiom-clean. | — |
| `CoherentConfig.card_foldl_insert_le` | 1899-1907 | §CC.20 (A2 potential route) Folding `insert` over a list grows a `Finset` by at most the list length (`(bs.foldl insert s).card ≤ s.card + bs.length`). Local copy (build places this module before `CascadeAffine`'s namesake); bounds the descent base size by the iteration length. Axiom-clean. | — |
| `CoherentConfig.exists_potential_descent` | 1909-1939 | §CC.20 (A2 potential route) **Abstract potential-descent engine** — a `Nat` potential `Φ` with a per-step *halving* (from any `T` with `Φ T > B`, some insertion at least halves `Φ`) reaches `Φ ≤ B` after `≤ log₂(max 1 (Φ S))` insertions (`2^len ≤ max 1 (Φ S)`). The `Φ`-analogue of the greedy-base `exists_greedy_base_aux`; pure `Finset`/`Nat` strong induction, no CC content. Axiom-clean `[propext, Quot.sound]`. | — |
| `CoherentConfig.potential` | 1941-1944 | §CC.20 (A2 potential route) **The A2 potential** `Φ(T) = (k(X_T)−1)·c(X_T)` on the point extension — the exact threshold quantity of `allSingletonFiber_of_card_gt_subset` (a base `T ⊇ T₀` with `|T| > Φ(T₀)` is a base of `X`). | Definition, `noncomputable` |
| `CoherentConfig.PotentialDrops` | 1946-1952 | §CC.20 (A2 potential route) **The per-step drop hypothesis — the genuine open core of A2.** From any base `T` with `Φ T > B`, some individualization at least halves `Φ`. The "shattering" the probe found holds on the non-geometric residue and fails (climbs to 1) only on geometric/Cameron-carved families; proving it via the Neumaier/CGGP dichotomy closes A2. Carried, never an `axiom`. | Definition |
| `CoherentConfig.exists_small_base_of_potentialDrops` | 1954-1967 | §CC.20 (A2 potential route) **A2's small-base deliverable (the iteration half, LANDED).** `PotentialDrops B` (`B ≥ 1`) ⟹ a base `T₀` with `(k(X_{T₀})−1)·c(X_{T₀}) ≤ B` and the log certificate `2^|T₀| ≤ max 1 (Φ ∅)` (so `|T₀| = O(log n)`). Feeds `allSingletonFiber_of_card_gt_subset` (pad to `|T| > B`); the whole open content is now `PotentialDrops`. Axiom-clean. | — |
| `CoherentConfig.IndistinguishingHalves` | 1969-1981 | §CC.20 (A2 Stage 1b) **The "shattering" hypothesis — the open core, sharpened.** From any base `T` with `Φ T > B`, some individualization at least HALVES the indistinguishing number `c(X_T)` alone (not the product). The max valency `k` is not controlled directly — it rides free by `maxValency_mono` (build doc §1B: `k` free, `c` the crux). A `c`-class resisting halving under every `v` is a partial-geometry line system (probe `Probe_SmallestEigenvalueAxis`: the drop-obstruction is the line/grid geometry, not the smallest-eigenvalue magnitude). Carried, never an `axiom`. | Definition |
| `CoherentConfig.potentialDrops_of_indistinguishingHalves` | 1983-2004 | §CC.20 (A2 Stage 1b) **The drop-lemma reduction — `c`-halving ⟹ `PotentialDrops`.** Halving `c(X_T)` suffices for the potential `(k−1)c` to halve: individualizing `v` refines `X_T` (`refines_pointExtension_of_subset`) so `k` is monotone non-increasing (`maxValency_mono`) and `2·(k'−1)·c' = (k'−1)·(2c') ≤ (k−1)·c` from `2c'≤c`. Reduces A2's open content from "the product halves" to "`c` halves" — the §1B split made rigorous. Axiom-clean. | — |
| `CoherentConfig.exists_potential_descent_bounded` | 2016-2049 | §CC.20b (route §9.8 part 1) **Abstract potential-descent engine, bounded-cardinality steps** — the cascade-rate generalization of `exists_potential_descent`: each step individualizes a *set* `S` of size `≤ M` that halves `Φ`, reaching `Φ ≤ B` at a base `T₀ ⊇ S₀` of size `≤ S₀.card + M·r` with `2^r ≤ max 1 (Φ S₀)` (i.e. `O(M·log)` insertions). `M = 1` (singleton `S`) recovers `exists_potential_descent`. Pure `Finset`/`Nat` strong induction. Axiom-clean. | — |
| `CoherentConfig.BoundedConfusionMultiplicity` | 2051-2060 | §CC.20b (route §9.8 part 1) **The bounded-cleanup confusion hypothesis — the cascade-rate form of `IndistinguishingHalves`.** From any over-`B` base, individualizing a *bounded set* `S` (`|S| ≤ M`) halves the indistinguishing number `c(X_T)`. The `M=1` case is implied by `IndistinguishingHalves`; the bounded form is what the multiplicity reframe (route §9.6) and the probe's `minMult` measure (pin the least-covered vertex, clean up the `≤ M` confusion sets it lies in). Carried as a hypothesis, never an `axiom`. | Definition |
| `CoherentConfig.potentialCleanup_of_boundedConfusionMultiplicity` | 2062-2081 | §CC.20b **The cascade-rate reduction — bounded `c`-cleanup ⟹ bounded potential-cleanup.** As `potentialDrops_of_indistinguishingHalves` but for a set `S`: `k(X_{T∪S})` rides free (`maxValency_mono` under `T ⊆ T∪S`), so halving `c` halves the potential `(k−1)c`. Axiom-clean. | — |
| `CoherentConfig.exists_small_base_of_boundedConfusionMultiplicity` | 2083-2096 | §CC.20b (route §9.8 part 1) **A2's small-base deliverable from the cascade-rate hypothesis — "residue cascades ⟹ polynomial".** If `c` halves per round via `≤ M` individualizations, there is a base `T₀` with `(k(X_{T₀})−1)·c(X_{T₀}) ≤ B` and `T₀.card ≤ M·r`, `2^r ≤ max 1 (Φ ∅)` (so `|T₀| ≤ M·log₂(Φ ∅) = O(M·log n)`). `M = O(1)`/`O(log n)` ⟹ polynomial base; feeds `allSingletonFiber_of_card_gt_subset`. **Collapses A2's open content to "the residue has bounded confusion multiplicity `M`".** Generalizes `exists_small_base_of_potentialDrops` (`M=1`). Axiom-clean. | — |
| `CoherentConfig.confusionSet` | 2111-2114 | §CC.21 (A2 Stage 1b) **The confusion set** `C(α,β) = {γ : relOf γ α = relOf γ β}` — the vertices failing to distinguish `α` from `β`; its card is the geometric form of `indistinguishingNumberOf (relOf α β)` (PV eq. (7)). The object `c(X_T)` maximizes. | Definition |
| `CoherentConfig.BalancedSplits` | 2116-2121 | §CC.21 (A2 Stage 1b) **`v` balance-splits the `(α,β)`-confusion** — every relation-`j` fiber of `C(α,β)` under `γ ↦ relOf γ v` has `≤ |C|/2` vertices. The relation-profile precondition the closure mechanics (route doc §4 G-mech) upgrades to an actual halving of `c` in `X_{T∪v}`. | Definition |
| `CoherentConfig.MajorityRelation` | 2123-2128 | §CC.21 (A2 Stage 1b) **`v` sees a majority of the `(α,β)`-confusion in one relation** (`> |C|/2`) — the negation of a balanced split; the local "monochromatic view" whose universality over all `v` is the geometric line-system obstruction. | Definition |
| `CoherentConfig.balancedSplits_or_majority` | 2130-2139 | §CC.21 (A2 Stage 1b) **The balanced/majority dichotomy** — every external point either balance-splits the confusion class or sees a majority of it in one relation. Pure case-split. Axiom-clean. | — |
| `CoherentConfig.majority_fibers_inter` | 2141-2160 | §CC.21 (A2 Stage 1b) **The intersecting-majority pigeonhole — the near-pencil structure (the combinatorial heart).** Majority fibers for two external points (each `> |C|/2`) necessarily overlap. So a class no point can balance-split has all its monochromatic views sharing witnesses — a pencil of lines = the partial-geometry obstruction the cited Neumaier/Cameron dichotomy attaches to. Via `card_union_add_card_inter`. Axiom-clean. | — |
| `CoherentConfig.GeometricObstruction` | 2162-2167 | §CC.21 (A2 Stage 1b) **The geometric (line-system) obstruction at scale `B`** — a confusion class `> B` that *every* external point sees monochromatically (no individualization balance-splits it). By `majority_fibers_inter` a near-pencil; the CC-intrinsic partial-geometry line system `¬IndistinguishingHalves` produces, routed to `Cameron ∨ finite` by the cited dichotomy. | Definition |
| `CoherentConfig.exists_balancedSplits_of_not_forall_majority` | 2169-2178 | §CC.21 (A2 Stage 1b) **No obstruction on a class ⟹ a balanced splitter exists** — if some point fails to see the confusion monochromatically, it balance-splits it (dichotomy). The bridge from "no geometric obstruction" to the splitter the closure mechanics consumes. Axiom-clean. | — |
| `CoherentConfig.relOf_v_eq_of_confused` | 2190-2219 | §CC.22 (A2 Stage 1b, G-mech kill-lemma core) On a CC with `v` a **singleton fiber**, any `γ` failing to distinguish `α,β` (`relOf γ α = relOf γ β`) forces `v` not to distinguish them either (`relOf v α = relOf v β`). The singleton fiber isolates the triangle count through `v` to `z=v` (`relOf_diag_right_eq`+`SingletonFiber`), so `interNum (relOf γ v) b (relOf γ α) = [b = relOf v α]`; the same count against `β` (same class) is `[b = relOf v β]`, forcing equality. Pure `interNum` coherence — no construction internals/tower. Axiom-clean. | — |
| `CoherentConfig.confusionSet_eq_empty_of_relOf_v_ne` | 2221-2229 | §CC.22 (A2 Stage 1b) **THE KILL LEMMA.** `v` a singleton fiber that *distinguishes* `α,β` (`relOf v α ≠ relOf v β`) ⟹ the confusion set `C(α,β)` is **empty** — individualizing `v` destroys that pair's indistinguishing class outright. The closure mechanism behind A2's per-step `c`-drop (route doc §4c): `c(X_{T∪v})` is bounded by the largest confusion among pairs `v` does *not* distinguish, so a `v` outside all over-half confusion sets halves `c`. Contrapositive of `relOf_v_eq_of_confused`. Axiom-clean. | — |
| `CoherentConfig.indistinguishingNumber_pointExtension_insert_le` | 2231-2273 | ≤ M`, then `c(pointExtension X (insert v T)) ≤ M`. Per non-reflexive `W`-class (rep pair `α≠β`): the kill lemma (`v` a singleton fiber of `W`) empties the confusion of every pair `v` *distinguishes`; each survivor is `⊆ C_{X_T}` (monotone via `Refines W X_T`) with `v` undistinguishing in `X_T` too, so `≤ M`. Dissolves the G-sim gap (one covering hypothesis replaces a per-class splitter). Step 3 consumes with `M = c(X_T)/2`. Axiom-clean. | — |
| `CoherentConfig.indistinguishingHalves_of_exists_avoiding_v` | 2275-2300 | §CC.22 (A2 Stage 1b, G-mech **the halving wiring** — route doc §4c step 3) **`IndistinguishingHalves` from an avoiding `v` per over-`B` base.** If every base `T` with `Φ T > B` admits a `v` avoiding all big confusion sets (every `v`-undistinguished pair `(α,β)`, `α≠β`, has `2·|C_{X_T}(α,β)| ≤ c(X_T)`), then `X.IndistinguishingHalves B`. Pure arithmetic on the step-2 bound at `M = c(X_T)/2`: gives `c(X_{T∪v}) ≤ c(X_T)/2`, hence `2·c(X_{T∪v}) ≤ c(X_T)`. Open content left = existence of the avoiding `v` (its negation = the `BigConfusionCover` obstruction, step 4). Axiom-clean. | — |
| `CoherentConfig.BigConfusionCover` | 2313-2321 | §CC.22 (A2 Stage 1b, route doc §4c step 4) **The big-confusion-set covering obstruction.** The size-`>c(X)/2` confusion sets (`c(X) < 2·|C(α,β)|`, `α≠β`) **cover `Fin n`**: every vertex fails to distinguish some pair with an over-half confusion class. Exact negation of "an avoiding `v` exists" (step 3's hypothesis). A cover forces `n ≤ (#big sets)·c(X)` ⟹ `≥ n/c` near-maximal confusion sets = a partial-geometry / near-pencil line system, routed to `Cameron ∨ finite` by the cited Neumaier + primitive-CC dichotomy (G-cite, step 5); the residue, being neither, has no cover. | Definition |
| `CoherentConfig.exists_avoiding_of_not_cover` | 2323-2338 | §CC.22 (A2 Stage 1b, route doc §4c step 4) **No cover ⟹ an avoiding `v` exists.** `¬ BigConfusionCover ⟹ ∃ v` outside all big confusion sets, i.e. every pair `(α,β)` (`α≠β`) with `relOf v α = relOf v β` has `2·|C(α,β)| ≤ c(X)` — exactly the avoiding-`v` hypothesis of `indistinguishingHalves_of_exists_avoiding_v`. Via `not_forall` + `not_le`. Axiom-clean. | — |
| `CoherentConfig.indistinguishingHalves_of_not_bigConfusionCover` | 2340-2350 | §CC.22 (A2 Stage 1b, route doc §4c step 4) **`IndistinguishingHalves` from no cover at every over-`B` base — the capstone-facing wiring.** `(∀ T, Φ T > B → ¬ BigConfusionCover (X_T)) ⟹ X.IndistinguishingHalves B`, composing `exists_avoiding_of_not_cover` per base with the step-3 wiring. **Packages the entire open content of A2 as one predicate on the extension:** G-cite (step 5) discharges `¬ BigConfusionCover (X_T)` for the residue. Axiom-clean. | — |
| `CoherentConfig.bigClasses` | 2352-2359 | §CC.22 (A2 Stage 1b, route doc §4c step 5 G-cite non-vacuity) **The distinct big confusion classes** — the confusion sets `C(α,β)` (`α≠β`) of size `> c(X)/2`, as a `Finset (Finset (Fin n))` (image of the big pairs under `C`). The geometric object the cited Neumaier/primitive-CC dichotomy attaches to; a cover by these is a near-pencil / partial-geometry line system. | Definition, `noncomputable` |
| `CoherentConfig.card_bigClasses_mul_ge_of_cover` | 2361-2392 | §CC.22 (A2 Stage 1b, route doc §4c step 5 G-cite **non-vacuity**) **A big-confusion cover forces `≥n/c` near-maximal confusion classes.** `BigConfusionCover X ⟹ n ≤ (bigClasses X).card · c(X)` — so a cover is a genuine geometric condition (`≥n/c` confusion classes each of size in `(c/2,c]`), the near-pencil line system the cited dichotomy attaches to and the witness that `BigConfusionCover` is **not** the conclusion in disguise. Each big class `≤ c` (non-reflexive) and they cover `Fin n`; via `card_biUnion_le` + `sum_le_card_nsmul`. Axiom-clean. | — |
| `CoherentConfig.confusionSet_eq_empty_of_allSingletonFiber` | 2394-2406 | §CC.22 (Stage 1b, route-doc §8.5 — citation-side bridge) **A complete extension has no surviving confusion class.** Every point a singleton fiber (`X` discrete) ⟹ any `α≠β` has an empty `confusionSet`: a `γ` confusing `α,β` forces them into one reflexive class (`relOf_diag_right_eq`), forbidden by a singleton fiber. Pure fiber coherence; the combinatorial half of the faithful `hNeumaier` ("discretizes ⟹ no confusion cover"). Axiom-clean. | — |
| `CoherentConfig.not_bigConfusionCover_of_allSingletonFiber` | 2408-2422 | §CC.22 (Stage 1b, route-doc §8.5 — **the citation-side bridge `cover ⟹ ¬complete`**) **Completeness rules out a `BigConfusionCover`.** All points singleton fibers ⟹ the big confusion sets are empty (`confusionSet_eq_empty_of_allSingletonFiber`), covering nothing. Contrapositive (*a cover forces `X_T` non-discrete, `T` not a base*) is the provable, citation-free heart of factoring `hNeumaier` into {Babai's `¬IsLarge ⟹ bounded complete base` (cited) + this bridge}; the honest replacement for the CGGP-false "cover ⟹ large Aut". Needs `n≥1`. Axiom-clean. | — |
| `CoherentConfig.indistinguishingNumber_pointExtension_biUnion_le` | 2433-2475 | §CC.22b (route §9.6 — the `(1+L)`-cleanup, SET form) **The kill-lemma bound for a set of individualizations.** The set generalization of `indistinguishingNumber_pointExtension_insert_le`: if every pair `(α,β)`, `α≠β`, that *no* `s∈S` distinguishes in `X_T` has `|C_{X_T}(α,β)| ≤ M`, then `c(X_{T∪S}) ≤ M`. Per non-reflexive `W=X_{T∪S}`-class: some distinguishing `s∈S` (a singleton fiber of `W`) empties its `W`-confusion (kill lemma), else `C_W ⊆ C_{X_T}` (monotone) with the pair landing in `hM`. The `S={v}` case is the insert bound. Axiom-clean. | — |
| `CoherentConfig.BoundedConfusionLoad` | 2477-2489 | §CC.22b (route §9.6) **The confusion-cover load predicate — the `(1+L)`-cleanup target.** From any over-`B` base `T`, a bounded set `S` (`|S|≤M`) distinguishes every big confusion pair: every `(α,β)`, `α≠β`, that no `s∈S` distinguishes has `2·|C_{X_T}(α,β)| ≤ c(X_T)` (i.e. `S` hits every `>c/2` confusion set). The §9.6 multiplicity reframe in Lean (`M` = `1+L`, `L` = avg load); the cascade-rate, set-lifted form of `BigConfusionCover`'s negation. Carried, never an `axiom`. | Definition |
| `CoherentConfig.boundedConfusionMultiplicity_of_boundedConfusionLoad` | 2491-2510 | §CC.22b (route §9.6 — **THE LOAD-BRIDGE**) **Bounded confusion load ⟹ bounded confusion multiplicity.** A size-`≤M` set distinguishing every big pair cleans `c(X_T)` to `≤c/2` (the set-form kill bound `indistinguishingNumber_pointExtension_biUnion_le` at `M'=c/2`), so `2·c(X_{T∪S}) ≤ c(X_T)`. The cascade-rate engine then runs off the **computable confusion-cover load** `L` (the probe's `minMult`) rather than the abstract "a set halves `c`" — A2's open content becomes "the residue's load is `O(1)`/`O(log n)`". Generalizes the `M=1` reduction `indistinguishingHalves_of_not_bigConfusionCover`. Axiom-clean. | — |
| `CoherentConfig.indistinguishingNumber_eq_zero_of_allSingletonFiber` | 2512-2530 | §CC.22b **A complete CC has `c(X)=0`.** Every point a singleton fiber ⟹ every non-reflexive class's rep `(α,β)`, `α≠β`, has empty confusion (`confusionSet_eq_empty_of_allSingletonFiber`), so the sup is `0`. The brick behind the non-vacuity anchor (`pointExtension X univ` is complete). Axiom-clean. | — |
| `CoherentConfig.boundedConfusionMultiplicity_univ` | 2532-2546 | §CC.22b (non-vacuity anchor, route §9.6) **The cascade hypothesis is satisfiable — the every-graph fallback at `M=n`.** `BoundedConfusionMultiplicity B n` holds for every CC: `S=univ` completes the extension (`c(X_univ)=0`), so `2·0 ≤ c(X_T)`. The route's content is `M=O(log n)`; this exhibits an honest inhabitant guarding the **vacuity trap** (cf. `SchemeReproduced`), mirroring `cascadesAt_univ`/`recoverableByDepth_univ`. Axiom-clean. | — |
| `CoherentConfig.boundedConfusionMultiplicity_of_completeBase` | 2548-2568 | §CC.22e (node-2 rung bridge) **A bounded *discrete* base ⟹ bounded confusion multiplicity.** If a base `T₀` (`|T₀|≤M`) discretizes `X` (the δ′ engine's output), then `BoundedConfusionMultiplicity B M` for every `B` (taking `S:=T₀` halves `c(X_T)` outright). Sharpens the trivial `boundedConfusionMultiplicity_univ` (`M=n`) to `M=|T₀|` — the bridge from a δ′ bounded base to the `…viaBoundedMultiplicity` pipeline. Axiom-clean. | — |
| `CoherentConfig.confusionSet_perm` | 2580-2597 | §CC.22c (route §9.9 step D1) **Confusion sets are equivariant under a CC automorphism.** For a `relOf`-preserving permutation `π` (the `Refines.aut_descends` convention), `C(π α, π β) = π '' C(α,β)`. The structural core of "a persistent big-confusion cover is a rigid `Aut`-invariant line system" (D1) — the object the D2 extraction / D3 dichotomy classify. Axiom-clean. | — |
| `CoherentConfig.card_confusionSet_perm` | 2599-2605 | §CC.22c (D1) **Confusion size is a CC-automorphism invariant.** `|C(π α, π β)| = |C(α,β)|` (`confusionSet_perm` + injectivity). So `c(X)` and the "big" (`>c/2`) threshold are `Aut`-invariant — the load-bearing D1 fact: big-ness travels with the automorphism group. Axiom-clean. | — |
| `CoherentConfig.mem_confusionSet_perm` | 2607-2616 | §CC.22c (D1) **Incidence equivariance.** `π v ∈ C(π α, π β) ↔ v ∈ C(α,β)` — the (vertex, confusion-set) incidence is `Aut`-equivariant, so `π` carries a cover to a cover and preserves each vertex's multiplicity profile. The atom the cover-rigidity / `minMult`-invariance arguments consume. Axiom-clean. | — |
| `CoherentConfig.big_confusion_perm` | 2618-2625 | §CC.22c (D1) **"Big" is a CC-automorphism invariant.** `(α,β)` has an over-half confusion set iff its `π`-image does (`card_confusionSet_perm`), so `π` permutes the big confusion pairs among themselves — the big-class line system is `Aut`-stable, as the D2/D3 classification requires. Axiom-clean. | — |
| `CoherentConfig.confusionMultiplicity` | 2627-2634 | §CC.22c (D1, route §9.6) **The confusion multiplicity (cover-load) of a vertex** — the number of big confusion *pairs* `(α,β)` (`α≠β`, `c(X)<2·|C(α,β)|`) that `v` fails to distinguish (`v∈C(α,β)`). The §9.6 load quantity; its `min` over `v` is `minMult` (the cleanup cost of one halving). Pair form (`≥` the distinct-set `bigClasses` count); bounding it bounds the cleanup `M`. | Definition, `noncomputable` |
| `CoherentConfig.confusionMultiplicity_perm` | 2636-2675 | §CC.22c (D1, the multiplicity punchline) **Confusion multiplicity is a CC-automorphism invariant.** `confusionMultiplicity (π v) = confusionMultiplicity v` for a `relOf`-preserving `π`: the product map `(α,β)↦(πα,πβ)` bijects the big pairs `v` lies in onto those `πv` lies in (`big_confusion_perm`+`mem_confusionSet_perm`+injectivity). So cover-load is **constant on automorphism orbits** — `minMult` is `Aut`-invariant, and on a vertex-transitive scheme it is literally constant `= L = (Σ_{big}|C|)/n` (no min-vs-average slack). The D1 deliverable: the cover's load profile is rigid. Axiom-clean. | — |
| `CoherentConfig.BoundedMinMult` | 2685-2690 | §CC.22d (route §9.6/§9.9) **Bounded minimum multiplicity** — at every over-`B` base, some vertex lies in `≤ M` big confusion pairs (`confusionMultiplicity ≤ M`), i.e. `minMult ≤ M`. The sharpest *computable* form of the §9.6 cover-load hypothesis (the probe's `minMult`); the thin side of the §9.9 dichotomy. Carried, never an `axiom`. | Definition |
| `CoherentConfig.boundedConfusionLoad_of_boundedMinMult` | 2692-2722 | §CC.22d (route §9.6 — **the `(1+L)`-cleanup, formalized**) **Bounded `minMult` ⟹ bounded confusion load.** A least-loaded `v` (in `≤ M` big pairs) builds the hitting set `S = {v} ∪ {α : (α,β) big through v}`, `|S|≤M+1`, distinguishing every big pair: `v` kills the big pairs it avoids, and for a big pair through `v` the endpoint `α∈S` distinguishes it (`relOf α α ≠ relOf α β`). `BoundedMinMult B M ⟹ BoundedConfusionLoad B (M+1)`. The §9.6 cleanup made rigorous. Axiom-clean. | — |
| `CoherentConfig.boundedConfusionMultiplicity_of_boundedMinMult` | 2724-2732 | §CC.22d **Bounded `minMult` ⟹ the cascade-rate hypothesis** — `BoundedMinMult B M ⟹ BoundedConfusionMultiplicity B (M+1)` (cleanup ∘ load-bridge). Reduces the entire cascade open content to **"the residue has bounded `minMult`"** (the probe quantity); feeds `reachesRigidOrCameron_viaBoundedMultiplicity` → the polynomial seal. Axiom-clean. | — |
## ChainDescent/ClebschConcrete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `clebschZ4ColF` | 38-55 | The ℤ₄² Clebsch colour matrix (16×16, rank-4, colours 0..3, 0=diagonal), extracted by `Theorem41ConditionsProbe.Probe_DumpClebschMatrix`. The concrete non-affine residue's relation data. | Definition |
| `clebschZ4Rel` | 57-58 | Relation `i` at `(v,w)` iff `clebschZ4ColF v w == i` (the colour-function `rel` for the concrete scheme). | Definition |
| `clebschZ4Rep` | 60-61 | A representative pair in each colour class `R_k` (`(0,0),(0,2),(0,1),(0,6)`), used to define the intersection numbers. | Definition |
| `clebschZ4IN` | 63-66 | The intersection numbers of the ℤ₄² Clebsch scheme, read off the representative pair per colour. | Definition |
| `clebschZ4Scheme` | 68-83 | **The concrete ℤ₄² amorphic-NLS Clebsch scheme as an `AssociationScheme 16`** (the primitive G2-B bullseye), all four axioms by `decide` (coherence split per-colour for low kernel memory). Distinct from the *affine* F₁₆ `clebschScheme` (CascadeAffine). Axiom-clean. | Definition |
| `clebschZ4_relOfPair` | 85-90 | `relOfPair v w = clebschZ4ColF v w` — the computable bridge letting `decide` evaluate the otherwise-`noncomputable` `relOfPair` in the closure proof. | — |
| `clebschZ4Rank` | 92-93 | The probe-extracted BFS pinning rank for base `{0,1}` (layers `[2,2,6,6]`, depth 3). | Definition |
| `clebschZ4Pin` | 95-100 | The probe-extracted explicit rainbow-triangle pinning pair `(µ,λ)` for each point. | Definition |
| `clebschZ4_closure` | 127-135 | §S-stage3-δ **THE FIRST NON-AFFINE δ′ CLOSURE IN LEAN.** Every point of the ℤ₄² amorphic-NLS Clebsch scheme is forced-triangle dominator-reachable from the 2-base `{0,1}` — the seal's `hclo` content discharged for a real non-affine primitive residue, by `decide` (NOT `native_decide`: axiom-clean). Via a local `interNum`-keyed rank engine (`domReach_of_rank_pin`) + the probe rank/pinners; the rainbow triangles' `c=1` checked by `decide`. Axiom-clean. | — |
| `clebschZ4_discrete` | 137-142 | §S-stage3-δ **The payoff: the ℤ₄² Clebsch scheme is `Discrete` after individualizing `{0,1}`** — `b(X) ≤ 2`, a non-affine `SeparatesAtBoundedBase`-grade recovery fully in Lean. `discrete_of_dominatorClosure` ∘ `clebschZ4_closure`. Axiom-clean. | — |
| `clebschZ4_rainbowRigid` | 144-150 | **The bullseye is rainbow-rigid (non-vacuity of `dominatorReachable_of_rainbowRank`).** `RainbowRigid clebschZ4Scheme` by `decide`: every rainbow triangle of the ℤ₄² Clebsch scheme has `≤ 1` common neighbour — the amorphic `(16,5,0,2)` structure as a checked fact, so the δ′ rainbow family lemma is satisfiable on the genuine non-affine residue (`clebschZ4_closure` is its concrete instance). Axiom-clean (plain `decide`). | — |
| `clebschZ4_closure_viaRainbow` | 152-184 | §S-stage3-δ **The family engine fires on the real residue — non-vacuity for `dominatorReachable_of_rainbowRank` / `reachesRigidOrCameron_viaRainbowRank`.** The ℤ₄² Clebsch closure re-derived through the *family* lemma `dominatorReachable_of_rainbowRank` (vs the bespoke `interNum`-keyed `domReach_of_rank_pin` of `clebschZ4_closure`): every point dominator-reachable from `{0,1}` using only `clebschZ4_rainbowRigid` + a rainbow rank (probe rank `clebschZ4Rank` with the explicit rainbow triangles `clebschZ4Pin`, the colours `≠`-distinct by `decide` after the `relOfPair`→matrix bridge). Witnesses that the rainbow `hbase`/`hstep` data the seal capstone needs is satisfiable on genuine non-affine amorphic-NLS data (the `n=16` instance of the uniform rainbow rank the node-2 rung wants). Gap to a *sealed* instance = the deferred `SchurianScheme` structure on `clebschZ4Scheme`. Axiom-clean (`decide`, not `native_decide`). | — |
## ChainDescent/GaussCount.lean

The finite-field quadratic exponential-sum toolkit for Stage B.1c-ii (the "Gauss build"): the Mathlib-absent
affine-quadric point count and its multi-point / k-fold generalizations. Imports ONLY Mathlib (a cheap leaf in
`namespace ChainDescent`); ported from the former `ScratchGauss.lean` development file. The endpoint it feeds is
`IsotropySeparatesAtBase` in `CascadeAffine.lean`, discharged via the planned `FormsGraph`-side consumer that
imports both this module and `CascadeAffine`. All decls axiom-clean `[propext, Classical.choice, Quot.sound]`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `count_eq_charsum` | 40-52 | **Brick A** — the solution count `#{x | f x = c}` as a double character sum `∑ₓ∑ₜ ψ(t(f x−c))` (additive orthogonality). The entry point for all the point counts. | — |
| `sum_addChar_sq` | 54-82 | **Brick B1** — the 1-D quadratic Gauss sum `∑ₓ ψ(x²) = gaussSum χ ψ` (each `y` hit by `χ(y)+1` roots; the `+1` part vanishes). | — |
| `sum_addChar_smul_sq` | 84-106 | **Brick B2** — the scaled 1-D sum `∑ₓ ψ(a·x²) = χ(a)·gaussSum χ ψ` for a unit `a` (via `gaussSum_mulShift`, `χ(a)²=1`). | — |
| `addChar_sum` | 108-114 | **Helper** — an additive character turns a finite sum into a product: `ψ(∑ᵢ aᵢ) = ∏ᵢ ψ(aᵢ)`. | — |
| `sum_addChar_quadForm` | 116-148 | **Brick B3** — the multivariable quadratic Gauss sum `∑ₓ ψ(Q x) = (∏ᵢ χ(wᵢ))·gaussSum^d` for nondegenerate `Q` (diagonalize via `equivalent_weightedSumSquares`, factor). The multivariable core. | — |
| `sum_quadForm_eval` | 150-186 | **Brick B3′** — basis-explicit `sum_addChar_quadForm` (weights `Q(v i)` for an orthogonal basis `v`; value pinned, no existential). Powers the scaling relation. | — |
| `sum_addChar_quadForm_smul` | 188-225 | **Brick C-scale** — scaling the form by a unit `s` scales the Gauss sum by `χ(s)^d`: `∑ₓ ψ(s·Q x) = χ(s)^d·∑ₓ ψ(Q x)` (change of additive character). For `d` even, scale-invariant. | — |
| `sum_addChar_quadForm_smul_ne_zero` | 227-250 | **(M2 — the cancellable constant)** If `∑_x ψ(Q x) ≠ 0` then `∑_x ψ(s·Q x) ≠ 0` for any unit `s` (factor `χ(s)^d` is a unit). This is the global Gauss value that cancels when comparing two configurations' multi-point sums `S(r) = ψ(Gram-expr)·∑_x ψ(R·Q x)`, yielding `ψ(Gram-expr_u) = ψ(Gram-expr_{u'})`. | — |
| `gaussSum_sq_ne_zero` | 252-268 | **The quadratic Gauss sum squared is nonzero** in a char-zero domain (`gaussSum χ ψ ^ 2 = χ(-1)·card K`, both factors nonzero). First factor of the bridge's carried `hK`. | — |
| `sum_addChar_quadForm_ne_zero` | 270-287 | **The quadratic Gauss sum over `V` is nonzero** given an orthogonal anisotropic basis in char zero — `∑_x ψ(Q x) ≠ 0`. Second factor of the bridge's carried `hK`. | — |
| `card_quadForm_eq` | 289-328 | **Brick C — THE affine-quadric point count (Mathlib-absent).** `#{x:Q x=c}·q = #V + (∑_{t≠0} ψ(−tc)·χ(t)^d)·∑ₓ ψ(Q x)`, from Brick A + the scaling relation. The assembled count formula. | — |
| `sum_addChar_quadForm_linear` | 330-358 | **Brick D1 — complete the square.** `∑_w ψ(r·Q w + polar Q w a') = ψ(−r⁻¹·Q a')·∑_w ψ(r·Q w)` (linear term absorbed by the shift `w ↦ w + r⁻¹a'`). The engine of hyperplane-section / joint counts. | — |
| `count2_eq_charsum` | 360-380 | **Brick A2** — the two-condition count `#{x:f x=c ∧ g x=d}` as a double-indexed character sum (generalizes Brick A). The entry point for the k-fold count assembly (the Gauss endpoint). | — |
| `quad_sub` | 382-390 | **Helper** — the parallelogram identity `Q(a−b) = Q a + Q b − polar Q a b`. | — |
| `polar_sum_right` | 392-400 | **Helper** — `polar Q z ·` is additive over a finite sum in its second argument: `∑ⱼ rⱼ·polar Q z tⱼ = polar Q z (∑ⱼ rⱼ•tⱼ)` (via `polarBilin`). | — |
| `sum_addChar_multiQuad` | 402-440 | **Multi-point quadratic Gauss sum (generalizes D1) — THE inner sum of the k-fold count.** `∑_z ψ(∑ⱼ rⱼ·Q(z−tⱼ)) = ψ(const)·∑_z ψ(R·Q z)` for `R=∑rⱼ≠0` (summand collapses to D1 via `quad_sub`+`polar_sum_right`). The engine for the count at a symmetry-broken base. | — |
| `countk_eq_charsum` | 442-472 | **Brick A_k — the k-fold count as a product-of-sums.** Generalizes `count_eq_charsum`/`count2_eq_charsum` to a `Fintype`-indexed family of conditions: `∑_x ∏_j (∑_{r_j} ψ(r_j(f_j x−c_j))) = #{x:∀j, f_j x=c_j}·q^{#ι}` (product of orthogonality indicators). | — |
| `countk_eq_sum_charsum` | 474-504 | **Brick A_k factored — the k-fold count over dual variables.** `#{x:∀j, f_j x=c_j}·q^{#ι} = ∑_{r:ι→F} ψ(−∑_j r_j c_j)·∑_x ψ(∑_j r_j·f_j x)` (expand via `Fintype.prod_sum`, collapse via `addChar_sum`). With `f_j x = Q(x−t_j)` the inner sum is exactly `sum_addChar_multiQuad` — the closed-form multi-point `Q`-count for the symmetry-broken-base injectivity (the Gauss endpoint). | — |
| `sum_addChar_linearMap` | 505-541 | **The linear-functional character sum (boundary engine).** `∑_x ψ(φ x) = |V|·[φ=0]` for a `K`-linear functional `φ` and primitive `ψ` (translation by `x₀` with `ψ(φ x₀)≠1`, from primitivity). Evaluates the `R=∑r_j=0` boundary of the multi-point count. | — |
| `sum_addChar_multiQuad_zero` | 543-570 | **Multi-point quadratic Gauss sum, the `R=0` boundary** (companion to `sum_addChar_multiQuad`). When `∑_j r_j=0` the `R·Qz` term vanishes and the summand is linear: `∑_z ψ(∑_j r_j·Q(z−t_j)) = ψ(∑_j r_j·Q t_j)·∑_z ψ(polar Q z (−∑_j r_j•t_j))`; the surviving factor evaluates by `sum_addChar_linearMap`. Together with `multiQuad` (R≠0), evaluates the inner sum for ALL `r`. | — |
| `count_pi_setValued` | 572-596 | **The inclusion–exclusion engine — value-SET counts = sum of value-POINT counts.** `#{z : ∀j, h_j z ∈ A_j} = ∑_{c∈∏A_j} #{z : ∀j, h_j z = c_j}` (fiberwise partition additivity). With `h_j z = Q(z−t_j)` it turns isotropy-class counts (each class = a `Q`-value-set: anisotropic ↔ `K∖{0}`, isotropic-or-zero ↔ `{0}`) into the pointwise `Q`-value counts the Gauss toolkit closes. | — |
| `multiCharSum_eq_sum_count` | 598-624 | **(M2 hinge — Fourier inversion)** `∑_x ψ(∑_j r_j·f_j x) = ∑_{c:ι→F} ψ(∑_j r_j·c_j)·#{x:∀j, f_j x=c_j}` (partition `x` by value-tuple). The dual of `countk_eq_sum_charsum`: all pointwise counts agree ⟹ all multi-point Gauss sums `S(r)` agree. With `f_j x=Q(x−t_j)`, `S(r)` carries the Gram (`sum_addChar_multiQuad`), so count-agreement ⟹ Gram-agreement. Elementary (no primitivity/domain). | — |
## ChainDescent/FormsGraphConcrete.lean

The `FormsGraph`-side consumer (imports `CascadeAffine` + `GaussCount`) that discharges `IsotropySeparatesAtBase Q T`
for the rank-3 SRG `VO^ε` residue, combining the Gauss point-count toolkit with the affine substrate + isotropy
dictionary. Build order: (1) count transport `Fin(p^d) ↔ V`; (2) isotropy→value-set conversion; (3) injectivity.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `count_transport` | 26-45 | **Count transport `Fin(p^d) ↔ V` along `affineE`.** A vertex count over the affine point set whose predicate factors through `affineE.symm` equals the count over `V = Fin d → ZMod p`. Moves the `IsotropySeparatesAtBase` counts into the vector space where the Gauss point counts live. | — |
| `qvalue_count_transport` | 46-60 | **`Q`-value-set count on the affine point set → pointwise `Q`-counts in `V` (step 2, value-set part).** Chains `count_transport` (`Fin(p^d)→V`) with `count_pi_setValued` (set→point): `#{z : ∀j, Q(z̄−t_j)∈A_j} = ∑_{c∈∏A_j} #{x : ∀j, Q(x−t_j)=c_j}` — landing on the pointwise counts the Gauss toolkit closes. The isotropy conditions reduce to such `Q`-value-sets via `isoClass_eq_*` (modulo the origin correction). | — |
| `isotropy_count_transport` | 70-94 | **(M1 step 1)** The fine `IsotropySeparatesAtBase` count over `Fin(p^d)` equals the count over `V` (`z≠u ↔ affineE.symm z ≠ affineE.symm u` + `count_transport`) — transports the hypothesis into `V` where the conversion + Gauss closed form live. | — |
| `isoSetOf` | 96-99 | The isotropy-class value-set for a coarse bit: anisotropic (`true`) ↦ `{2}`, isotropic-or-zero (`false`) ↦ `{0,1}`. | Definition |
| `qSetOf` | 101-104 | The matching `Q`-value-set: anisotropic ↦ `{x≠0}`, isotropic-or-zero ↦ `{0}`. | Definition |
| `mem_isoSetOf_iff` | 106-116 | **(M1 dictionary)** `isoClass Q w ∈ isoSetOf b ↔ Q w ∈ qSetOf b` — the coarse split is a pure `Q`-value condition (from `isoClass_ne_two_iff` / `isoClass_eq_two_iff`). | — |
| `coarse_eq_sum_iso` | 117-134 | **(M1 core — fine→coarse)** A coarse `Q`-value-set count `#{x:∀j, Q(x−t_j)∈qSetOf(τ_j)}` = the sum over refining isotropy profiles `σ∈∏isoSetOf(τ_j)` of fine counts `#{x:∀j, isoClass(x−t_j)=σ_j}` (`count_pi_setValued` at the isotropy value-type). So fine-count agreement ⟹ coarse-count agreement, no origin correction (M0). | — |
| `QProfileSeparatesAtBase` | 152-168 | **(M3 crux — the corrected `IsotropyCountsRecoverFrameQ`)** Agreeing fine isotropy-counts at base `T` ⟹ same `Q`-profile over the standard basis frame. At an arbitrary *symmetry-broken* `T` (unlike the superseded frame-locked predicate), where it is probe-validated (`VO^-_4(3)`, `T=frameBase∪{2e₃}`, 81/81). **OPEN** — the genuine uncited joint-incidence content (`Z(S)` over sub-frames; `isoClass` is shell-blind so the M2 pointwise hinge doesn't apply). | Definition, `noncomputable` |
| `isotropySeparates_of_qProfileSeparates` | 170-179 | **(M3 reduction — resolved)** `QProfileSeparatesAtBase Q T` + nondegenerate polar form ⟹ `IsotropySeparatesAtBase Q T`, via the landed `coords_determine` (Q-profile + nondeg ⟹ vector) and `affineE.symm` injective. So the entire remaining Gauss-work content for this residue is the single predicate `QProfileSeparatesAtBase`. | — |
## ChainDescent/RouteCFormAdapters.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RouteC.coords_determine_spanning` | 49-71 | **Key lemma.** The spanning generalization of `coords_determine`: with a nondegenerate polar form, agreeing `Q`-value profiles over a spanning base `S` force `v = v'`. The vertex-determiner Route C needs when the base is an iso-invariantly chosen spanning set rather than the standard frame. | — |
| `RouteC.reachesRigidOrCameron_viaOrthogonalForm_spanning` | 73-128 | **Route C back-half.** The recovered isometry scheme `O(Q)` discretizes at ANY spanning base and seals via `viaSpielman` — spanning generalization of `viaOrthogonalForm`, no standard frame, no `hSmallAutThin`. | — |
| `RouteC.affineScheme_refines_of_le` | 140-157 | **The generic refinement core.** For subgroups `H ≤ G` (both containing `−1`), the affine orbital scheme of `H` is finer than that of `G`. Reusable base of every Route-C refinement brick: recovering a smaller group refines, never fabricates. | — |
| `RouteC.isometryScheme_refines_similitudeScheme` | 159-177 | **A3 brick 1.** `O(Q) ≤ GO(Q)` ⟹ the recovered isometry scheme refines the given similitude graph — the consistency half of the refinement bridge. | — |
| `RouteC.NondegQuadricDeterminesForm` | 199-221 | **The quadric Nullstellensatz predicate — now DISCHARGED.** A nondegenerate quadric determines its form up to a nonzero scalar (`p≠2`, `d≥4`); proved for even `d` by `nondegQuadricDeterminesForm_of_even` (no longer a carried citation). | Definition |
| `RouteC.nondegQuadricDeterminesForm_of_even` | 223-232 | **Citation discharged.** `NondegQuadricDeterminesForm p d` is now a theorem (even `d`): proof = `Nullstellensatz.nondegQuadric_zmod_of_even`; `recoveredForm_colouring_equivariant` no longer carries it as a premise. | — |
| `RouteC.similitude_colouring_equivariant` | 234-245 | **F4 brick 1.** A form similitude `Q' (g v) = μ·Q v` transports the difference colouring by the same scalar: `Q' (g u − g t) = μ·Q (u − t)`. The load-bearing equivariance content of F4. | — |
| `RouteC.similitude_conePreserving` | 247-262 | **F4 brick 1b.** A form similitude carries the `Q`-cone to the `Q'`-cone (`Q' (g v) = 0 ↔ Q v = 0`); the consistency direction complementing `NondegQuadricDeterminesForm`. | — |
| `RouteC.recoveredForm_colouring_equivariant` | 264-285 | **F4 core (`|Aut|`-naming).** A graph iso's linear part carries the `Q`-cone to the `Q'`-cone, so the recovered-`Q` difference colouring transports by one global scalar — the iso-invariance making recovered-form discretization canonical. The Nullstellensatz input is now proved outright (only elementary `Even d` carried). | — |
| `RouteC.vanishingForm_transport_gen` | 303-313 | **F4 discharge — the load-bearing pullback (generic cone).** `g` carries `cone(C)` to `cone(C')` ⟹ pulling a form vanishing on `cone(C')` back by `g` vanishes on `cone(C)` (`F' ∈ W(C') ⟹ F'∘g ∈ W(C)`). Elementary; no dimension count, no citation. Serves single quadric (`C:=Q=0`) and multi-form (`C:=∀k,Qₖ=0`). | — |
| `RouteC.recoveredForm_partition_isoInvariant_gen` | 315-348 | **F4 citation-free payoff (generic).** Two pairs indistinguishable by the whole vanishing space `W(C)` **iff** their `g`-images are indistinguishable by `W(C')` — the iso-invariance of the recovered colour partition, proved by pullback across `g`/`g.symm` with **no `NondegQuadricDeterminesForm`/`JointVarietyDeterminesFamily`**. The elementary vanishing-space route (`chain-descent-citation-discharge.md` §3.2). | — |
| `RouteC.recoveredForm_partition_isoInvariant` | 350-361 | **F4 citation-free — single quadric.** The recovered `W(Q)`-colour partition is iso-invariant under a cone-preserving linear iso (the `C:=Q=0` specialization). Discharges F4 from the Nullstellensatz at `q=p`. | — |
| `RouteC.vanishingColour_refines_form` | 363-372 | **F4 — the `W`-colouring refines the `Q`-colouring** (`Q ∈ W(Q)`), so the citation-free discharge loses no separation: `coords_determine` still fires. | — |
| `RouteC.frobVec` | 390-394 | The coordinate-wise action `x ↦ (σ(xᵢ))` of a field endomorphism `σ` on `V` — the semilinear part of a collineation of `AG(d,q)`. | Definition |
| `RouteC.frobVec_sub` | 395-401 | `σ̂` is additive: `σ̂(u − t) = σ̂ u − σ̂ t`. What makes the semilinear equivariance identity go through. | — |
| `RouteC.semisimilitude_colouring_equivariant` | 402-413 | **F2 brick 1.** A semi-similitude `g = M∘σ̂` transports the difference colouring by scalar `μ` and field automorphism `σ`: `Q'(M σ̂ u − M σ̂ t) = μ·σ(Q(u − t))`. The `q = pᵉ` analog of `similitude_colouring_equivariant`. | — |
| `RouteC.ConePreservingCollineationIsSemiSimilitude` | 415-438 | **Scoped citation (F2), CORRECTED 2026-07-16.** An iso of affine polar graphs (difference-cone-preserving bijection) is a semi-affine semi-similitude — the `q=pᵉ` semilinear seam. The old pointwise-cone antecedent was false as formalized (see docstring). | Definition |
| `RouteC.recoveredForm_colouring_equivariant_semilinear` | 440-459 | **F4 over `𝔽_q`.** The semilinear (`q=pᵉ`) form of F4 — the recovered form is iso-invariant including the Frobenius/ΓL part (translation part cancels in differences). | — |
| `RouteC.FormAdapter` | 476-490 | **The generic Route-C engine interface.** A form family plugs in its linear group `G₀` (∋ −1), a bounded spanning base, and a `separates` certificate. | Structure |
| `RouteC.FormAdapter.reachesRigidOrCameron` | 492-503 | **The shared engine theorem.** Any `FormAdapter` reaches the rigid-or-Cameron disjunction — one engine, N family instances. | — |
| `RouteC.affinePolarAdapter` | 505-531 | **Instance 1** — affine-polar `VO^ε` as a `FormAdapter` (validates the interface). | Definition, `noncomputable` |
| `RouteC.coords_determine_multi` | 547-567 | **Multi-form `coords_determine` (the alternating family's `separates` core).** A family of quadratic forms whose polar forms jointly separate (trivial common radical) determines the vertex from the joint value-profile at the standard frame. The `ι = Unit` case is `coords_determine`. | — |
| `RouteC.coords_determine_multi_spanning` | 569-588 | **Multi-form `coords_determine` at a spanning base** — `coords_determine_multi` with the value-profile taken over any spanning set, combining the joint-radical and spanning arguments for Route C's iso-invariant base. | — |
| `RouteC.multiFormAdapter` | 590-623 | **The multi-quadric engine.** A family of quadratic forms whose joint cone is the connection set plugs into one adapter — basis for the non-quadratic families. | Definition, `noncomputable` |
| `RouteC.jointConeStab` | 646-666 | **The cone stabilizer — the graph-intrinsic linear group of a multi-quadric forms graph.** The setwise stabilizer of the joint isotropic cone (= the connection set): definable from the graph alone, so its affine scheme is the multi-form refinement target (analog of `similitudeGroup`). | Definition |
| `RouteC.neg_mem_jointConeStab` | 668-675 | `−1 ∈ jointConeStab Qs` — the `hneg` input for the cone-stabilizer scheme (`Q_k(−v) = Q_k v` leaves the cone condition unchanged). | — |
| `RouteC.iInf_isometryGroup_le_jointConeStab` | 677-688 | The joint isometry group is contained in the cone stabilizer (`⨅ₖ O(Q_k) ≤ jointConeStab Qs`) — what lets `affineScheme_refines_of_le` fire for the multi-form refinement brick. | — |
| `RouteC.multiIsometryScheme_refines_coneScheme` | 690-705 | **brick-1-multi.** The recovered joint-isometry scheme `⨅ₖ O(Q_k)` refines the graph-intrinsic cone-stabilizer scheme. | — |
| `RouteC.multiSimilitude_colouring_equivariant` | 707-719 | **F4-multi brick.** If a graph iso's linear part transports the value-tuple colouring by a global map `Φ`, it transports the difference colouring by the same `Φ`. Multi-form analog of `similitude_colouring_equivariant` (with `Φ` arbitrary). | — |
| `RouteC.JointVarietyDeterminesFamily` | 721-747 | **CORRECTED 2026-07-16 (was a false-as-formalized citation; now PROVED below).** The joint variety determines its quadric family up to an invertible recombination, GIVEN the span/independence antecedents (= the projective-normality content). The F4-multi sibling of `NondegQuadricDeterminesForm`. | Definition |
| `RouteC.jointVarietyDeterminesFamily_holds` | 749-839 | **The corrected fact is a theorem — no citation at this layer.** Expand each pulled-back form over the other family (`hspan`/`hspan'`), compose the coefficient matrices, and linear independence forces `D·C = 1` ⟹ `Φ := C·` injective. Carried content moves to the per-family span facts at instantiation. | — |
| `RouteC.recoveredFamily_colouring_equivariant` | 841-866 | **F4-multi (`|Aut|`-naming).** Given a joint-cone-preserving graph iso and the per-family span/independence facts (projective normality — the faithful citation shape, replacing the old blanket `hcite` 2026-07-16), the recovered value-tuple difference colouring transports by a single global injective `Φ` — the multi-quadric completion of F4. | — |
| `RouteC.recoveredFamily_partition_isoInvariant` | 868-885 | **F4-multi payoff (`|Aut|`-naming).** The recovered value-tuple colour partition is iso-invariant (a graph iso transports it by a global injective Φ). Derived from the injective-`Φ` equivariance (span/independence facts upstream). | — |
| `RouteC.recoveredFamily_partition_isoInvariant_vanishing` | 887-904 | **F4-multi citation-free.** The recovered joint-`W` colour partition is iso-invariant with **no `JointVarietyDeterminesFamily`** — the `C:=∀k,Qₖ=0` specialization of `recoveredForm_partition_isoInvariant_gen` (vanishing-space transport, §3.2). Discharges F4-multi from projective normality at `q=p`. | — |
| `RouteC.polar_linMulLin` | 915-920 | **Reusable primitive.** `polar (linMulLin f g) x y = f x·g y + f y·g x` — the building block for the polar of any Clifford-term-sum quadric (Plücker sub-Pfaffians, D₅ spinor quadrics). | — |
| `RouteC.Plucker.pc` | 925-926 | The `i`-th Plücker coordinate projection on `𝔽_p^10`. | Definition, `noncomputable` |
| `RouteC.Plucker.Pf0` | 928-930 | Sub-Pfaffian deleting index 0 (`x₄x₉ − x₅x₈ + x₆x₇`); one of the 5 Plücker quadrics. | Definition, `noncomputable` |
| `RouteC.Plucker.Pf1` | 931-933 | Sub-Pfaffian deleting index 1 (`x₁x₉ − x₂x₈ + x₃x₇`). | Definition, `noncomputable` |
| `RouteC.Plucker.Pf2` | 934-936 | Sub-Pfaffian deleting index 2 (`x₀x₉ − x₂x₆ + x₃x₅`). | Definition, `noncomputable` |
| `RouteC.Plucker.Pf3` | 937-939 | Sub-Pfaffian deleting index 3 (`x₀x₈ − x₁x₆ + x₃x₄`). | Definition, `noncomputable` |
| `RouteC.Plucker.Pf4` | 940-942 | Sub-Pfaffian deleting index 4 (`x₀x₇ − x₁x₅ + x₂x₄`). | Definition, `noncomputable` |
| `RouteC.Plucker.pluckerForms` | 944-946 | The family of 5 Plücker quadrics (`Fin 5`); the `Alt(5,q)` connection set is their joint cone. | Definition, `noncomputable` |
| `RouteC.Plucker.Pf0_polar` | 948-951 | The polar form of `Pf0`, expanded in coordinates. | — |
| `RouteC.Plucker.Pf1_polar` | 952-955 | The polar form of `Pf1`, expanded in coordinates. | — |
| `RouteC.Plucker.Pf2_polar` | 956-959 | The polar form of `Pf2`, expanded in coordinates. | — |
| `RouteC.Plucker.plucker_hjoint` | 961-1000 | **The Plücker quadrics are jointly nondegenerate** (trivial common polar radical) — the sole geometric input the alternating adapter needs (`Pf₀` isolates coords 4..9, `Pf₁` isolates 1,2,3, `Pf₂` isolates 0). | — |
| `RouteC.Plucker.alternatingAdapter` | 1002-1005 | **`Alt(5,q)` as a sealed `FormAdapter`** — the Plücker quadrics assembled via `multiFormAdapter`; `G₀ = ⨅ₖ O(Pf_k)`. The first concrete non-quadratic Route-C family. | Definition, `noncomputable` |
| `RouteC.Plucker.reachesRigidOrCameron_alternating` | 1007-1020 | **Instance 2 sealed** — the alternating `Alt(5,q)` family via 5 Plücker quadrics; the first non-quadratic Route-C seal. | — |
| `RouteC.Plucker.alternating_refines_coneScheme` | 1022-1034 | **`Alt(5,q)` brick-1 (concrete).** The recovered joint-isometry scheme refines the graph-intrinsic cone-stabilizer scheme of the Plücker family — the refinement leg for alternating. | — |
| `RouteC.HalfSpin.halfSpin_reduction` | 1056-1073 | **Half-spin reduction (instance 3 target).** Committing the D₅ dimensions: any 10 quadratic forms on `𝔽_p^16` with joint nondegeneracy are sealed via `multiFormAdapter`, reducing all remaining half-spin work to constructing the spinor quadrics and their `hjoint`. | — |
| `RouteC.HalfSpin.sc` | 1090-1091 | The `i`-th half-spin coordinate projection on `𝔽_p^16`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S0` | 1093-1095 | D₅ spinor quadric — the quadruple form for `1234` (`x_∅x_{1234} = Pf`). | Definition, `noncomputable` |
| `RouteC.HalfSpin.S1` | 1096-1098 | D₅ spinor quadric — the quadruple form for `1235`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S2` | 1099-1101 | D₅ spinor quadric — the quadruple form for `1245`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S3` | 1102-1104 | D₅ spinor quadric — the quadruple form for `1345`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S4` | 1105-1107 | D₅ spinor quadric — the quadruple form for `2345`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S5` | 1108-1110 | D₅ spinor quadric — pair×quadruple form 5. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S6` | 1111-1113 | D₅ spinor quadric — pair×quadruple form 6. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S7` | 1114-1116 | D₅ spinor quadric — pair×quadruple form 7. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S8` | 1117-1119 | D₅ spinor quadric — pair×quadruple form 8. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S9` | 1120-1122 | D₅ spinor quadric — pair×quadruple form 9. | Definition, `noncomputable` |
| `RouteC.HalfSpin.spinorForms` | 1124-1127 | The family of 10 D₅ spinor quadrics (`Fin 10`); their joint cone is the pure-spinor cone = the half-spin connection set. | Definition, `noncomputable` |
| `RouteC.HalfSpin.S0_polar` | 1129-1132 | The polar form of `S0`, expanded in coordinates. | — |
| `RouteC.HalfSpin.S1_polar` | 1133-1136 | The polar form of `S1`, expanded in coordinates. | — |
| `RouteC.HalfSpin.S2_polar` | 1137-1140 | The polar form of `S2`, expanded in coordinates. | — |
| `RouteC.HalfSpin.S3_polar` | 1141-1144 | The polar form of `S3`, expanded in coordinates. | — |
| `RouteC.HalfSpin.S4_polar` | 1145-1148 | The polar form of `S4`, expanded in coordinates. | — |
| `RouteC.HalfSpin.spinor_hjoint` | 1150-1209 | **The 10 spinor quadrics are jointly nondegenerate** (trivial common polar radical) — the `hjoint` the half-spin adapter needs, provable from the 5 quadruple forms `S0..S4` alone. | — |
| `RouteC.HalfSpin.spinAdapter` | 1211-1214 | **The D₅ half-spin family as a sealed `FormAdapter`** — the 10 spinor quadrics assembled via `multiFormAdapter`; `G₀ = ⨅ₖ O(S_k)`. | Definition, `noncomputable` |
| `RouteC.HalfSpin.reachesRigidOrCameron_halfSpin` | 1216-1230 | **Instance 3 sealed** — the half-spin family via the 10 D₅ spinor quadrics. | — |
| `RouteC.HalfSpin.halfSpin_refines_coneScheme` | 1232-1242 | **Half-spin brick-1 (concrete).** The recovered joint-isometry scheme refines the graph-intrinsic cone-stabilizer scheme of the D₅ spinor family — the refinement leg for half-spin. | — |
| `RouteC.Suzuki.ovoidC` | 1269-1270 | The 4th Tits-ovoid coordinate `c = a·b + σa·a² + σb` (affine chart `x₀ = 1`). | Definition |
| `RouteC.Suzuki.SF0` | 1272-1274 | Suzuki σ-twisted form 0 (the single derived form `x₃x₀^{σ+1}+x₁x₂x₀^σ+x₁^{σ+2}+x₂^σx₀²`). | Definition |
| `RouteC.Suzuki.SF1` | 1275-1277 | Suzuki σ-twisted form 1. | Definition |
| `RouteC.Suzuki.SF2` | 1278-1280 | Suzuki σ-twisted form 2. | Definition |
| `RouteC.Suzuki.SF3` | 1281-1283 | Suzuki σ-twisted form 3. | Definition |
| `RouteC.Suzuki.SF4` | 1284-1286 | Suzuki σ-twisted form 4. | Definition |
| `RouteC.Suzuki.suzukiForms` | 1288-1291 | The 5 σ-twisted Suzuki forms packaged as a family over `Fin 5`, for the joint-value adapter. | Definition |
| `RouteC.Suzuki.four_eq_zero` | 1293-1296 | `(4 : K) = 0` in char 2 — clears the `·4` coefficients `ring_nf` produces when four equal monomials collect. | — |
| `RouteC.Suzuki.SF0_ovoid` | 1298-1302 | `SF0` vanishes on the affine ovoid `(1, a, b, ovoidC a b)`. | — |
| `RouteC.Suzuki.SF1_ovoid` | 1304-1308 | `SF1` vanishes on the affine ovoid (given `σ∘σ = (·)²`). | — |
| `RouteC.Suzuki.SF2_ovoid` | 1310-1314 | `SF2` vanishes on the affine ovoid (given `σ∘σ = (·)²`). | — |
| `RouteC.Suzuki.SF3_ovoid` | 1316-1320 | `SF3` vanishes on the affine ovoid (given `σ∘σ = (·)²`). | — |
| `RouteC.Suzuki.SF4_ovoid` | 1322-1326 | `SF4` vanishes on the affine ovoid (given `σ∘σ = (·)²`). | — |
| `RouteC.Suzuki.suzukiForms_ovoid` | 1328-1338 | All 5 σ-twisted forms vanish on the affine ovoid (packaged over `Fin 5`). | — |
| `RouteC.Suzuki.suzukiForms_infty` | 1339-1343 | All 5 forms vanish at the point at infinity `(0,0,0,1)`. | — |
| `RouteC.Suzuki.suzukiForms_homog` | 1344-1350 | **σ-twisted homogeneity** — `SF_k(λ·x) = σλ·λ²·SF_k(x)`, so each `{SF_k = 0}` is a cone; with ovoid + infinity vanishing this gives vanishing on the whole connection set. | — |
| `RouteC.Suzuki.SFv` | 1365-1366 | The Suzuki form family evaluated on a vector `v : Fin 4 → K`. | Definition |
| `RouteC.Suzuki.PreservesForms` | 1368-1371 | A map preserves the σ-twisted Suzuki forms (`F_k(g w) = F_k(w)`) — the joint σ-form isometry condition whose orbit-of-difference relation is the Route-C isometry-scheme colouring. | Definition |
| `RouteC.Suzuki.SF0_recover` | 1387-1393 | Recovery of `x₂` — the 2nd discrete derivative `D₀D₁ SF0` collapses to `x₂` (σ-terms cancel in char 2). | — |
| `RouteC.Suzuki.SF1_recover_x3` | 1395-1401 | Recovery of `x₃` — `D₀D₁ SF1 = x₃`. | — |
| `RouteC.Suzuki.SF1_recover_x0` | 1403-1409 | Recovery of `x₀` — `D₁D₃ SF1 = x₀`. | — |
| `RouteC.Suzuki.SF4_recover_x1` | 1411-1419 | Recovery of `x₁` — `D₂D₃ SF4 = x₁`. | — |
| `RouteC.Suzuki.preservesForms_eq` | 1420-1424 | A form-preserving map that carries `b` to `a` equalizes the form-values (`F_k a = F_k b`) — the σ-twisted "orbit ⟹ equal-values" half. | — |
| `RouteC.Suzuki.recover_x2` | 1426-1431 | `SFv`-level recovery of `x₂` (`D₀D₁ SF0`), lifting `SF0_recover` through coordinate evaluation. | — |
| `RouteC.Suzuki.recover_x3` | 1433-1438 | `SFv`-level recovery of `x₃` (`D₀D₁ SF1`). | — |
| `RouteC.Suzuki.recover_x0` | 1440-1445 | `SFv`-level recovery of `x₀` (`D₁D₃ SF1`). | — |
| `RouteC.Suzuki.recover_x1` | 1447-1452 | `SFv`-level recovery of `x₁` (`D₂D₃ SF4`). | — |
| `RouteC.Suzuki.suzukiForms_determine` | 1454-1481 | **Suzuki citation discharge.** The 5 σ-twisted ovoid forms determine the coordinates on the enlarged base — makes `reachesRigidOrCameron_suzuki` citation-free. | — |
| `RouteC.Suzuki.SFbar` | 1496-1497 | The Suzuki forms in `𝔽₂`-coordinates via the additive iso `Ψ` (`SFbar = SFv ∘ Ψ`). | Definition |
| `RouteC.Suzuki.suzukiG₀` | 1499-1516 | **The transported Suzuki joint-isometry group** — the `𝔽₂`-linear autos of `Fin D → ZMod 2` preserving every `SFbar`, a clean subgroup feeding the char-2 engine. | Definition |
| `RouteC.Suzuki.preservesForms_of_mem_G₀` | 1517-1524 | `g ∈ suzukiG₀` ⟹ its `Ψ`-conjugate preserves the `K`-side forms — the link from the standard-space isometry to the `K`-side determiner. | — |
| `RouteC.Suzuki.neg_mem_suzukiG₀` | 1526-1532 | `−1 ∈ suzukiG₀` — free in char 2 (`Ψ(−w) = Ψw`, so `neg` preserves every `SFbar`). | — |
| `RouteC.Suzuki.suzukiBaseVecs` | 1534-1538 | The 8 base vectors on the `K`-side (`{0, e₀, e₁, e₂, e₃, e₀+e₁, e₁+e₃, e₂+e₃}`) whose pairwise sums power the second-derivative recovery. | Definition |
| `RouteC.Suzuki.suzukiBase` | 1540-1544 | The individualized base — `Ψ`-images of `suzukiBaseVecs` transported to `Fin (2^D)` (`≤ 8` points). | Definition, `noncomputable` |
| `RouteC.Suzuki.suzukiBase_card_le` | 1545-1550 | The Suzuki base has `≤ 8` points. | — |
| `RouteC.Suzuki.base_sfv_eq` | 1551-1560 | **Per-base-vector transport.** A `G₀`-orbit witness at the `Ψ`-image of `b` gives equality of the σ-form values of the two vertices' differences by `b`. | — |
| `RouteC.Suzuki.suzukiAdapter` | 1562-1595 | **The Suzuki family as a `FormAdapter`** (instance 4). `G₀ = suzukiG₀`, base = enlarged frame images (`≤ 8`), `separates` = transport to the proved determiner `suzukiForms_determine` — no citation, no `hσ`, no field-size hypothesis. | Definition, `noncomputable` |
| `RouteC.Suzuki.reachesRigidOrCameron_suzuki` | 1597-1611 | **Instance 4 sealed, citation-free** — Suzuki–Tits via 5 σ-twisted ovoid forms; `separates` proved by second-derivative recovery (no citation, no `hσ`). | — |

## ChainDescent/RouteCSeam.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SealDisj` | 35-40 | The seal disjunction (`reachesRigidOrCameron` conclusion shape) with the free `IsCameronScheme` predicate + depth bound as parameters. | Definition |
| `reachesRigidOrCameron_seamDispatch` | 47-63 | **The generic seam dispatch.** A residue that is Cameron, or realized by some already-sealed scheme `Y`, is itself sealed — one theorem over all forms-graph families + the cyclotomic branch. Carries the generic `htransport`. | — |
| `reachesRigidOrCameron_affineResidue` | 65-78 | **The named combined seam.** `reachesRigidOrCameron_seamDispatch` under the name recording intent — the seam over the *whole* Skresanov-isolated affine residue (the cyclotomic scheme + the four forms-graph families), each supplied as an already-sealed realized `Y`. | — |
| `separatesAtBoundedBase_affinePolar` | 87-98 | **The Cameron-free producer.** `IsotropySeparatesAtBase Q T` (+ bounded `T`) gives a bounded base discretising the affine-polar similitude scheme — extracted before the `Or.inl(Or.inr)` padding. | — |
| `reachesRigidOrCameron_viaSchurianRank3Affine_proved` | 100-118 | **The affine-polar atom-free capstone.** `htransport` DISCHARGED: transports the light `SeparatesAtBoundedBase` (not the 4-way `SealDisj`) and re-derives via `viaSpielman` — no `IsCameronScheme`-invariance premise. | — |
| `cyclotomic_sealDisj` | 120-138 | **The cyclotomic dispatch input.** The 1-dim cyclotomic scheme satisfies `SealDisj` (via `affineSlice`) — the branch the four-case sketch dropped. | — |
| `affineG_le_schemeAutGroup` | 147-160 | **The `≥` half of the 2-closure.** `affineG G₀ ≤ SchemeAutGroup(affineScheme G₀)`: the affine group acts as scheme automorphisms of its own orbital scheme — reusable for both the fine (`isometryGroup`) and coarse (`similitudeGroup`) schemes. | — |
| `schemeAutGroup_affineScheme_mono` | 162-180 | **`hmono`.** A finer affine scheme has a smaller automorphism group (`H ≤ G ⟹ SchemeAutGroup(affineScheme H) ≤ SchemeAutGroup(affineScheme G)`) — the honest sense in which the recovered form only *refines*. | — |
| `isometrySimilitude_schemeAutGroup_mono` | 182-188 | The concrete `hmono` for Route C's fine⟶coarse: the recovered isometry scheme's Aut group is `≤` the given similitude graph's. | — |
| `AffineSchemeTwoClosed` | 190-198 | **Skresanov rank-3 2-closure citation** (one named premise, all four families): the affine scheme of `G₀` has no unexpected automorphisms. | Definition |
| `schemeAutGroup_affineScheme_eq_affineG` | 200-210 | -side content. | — |
| `schemeAutGroup_coarse_eq_affineG` | 212-219 | **Affine-polar instance of the group-pinning.** The given `VO^ε` graph's Aut group is exactly `affineG(similitudeGroup Q) = translations ⋊ AΓO(Q)`, modulo Skresanov — the `G₀ := similitudeGroup Q` case of `schemeAutGroup_affineScheme_eq_affineG`. | — |
| `routeC_polySupport` | 221-240 | **Route C poly-support certificate.** Bundles (coarse Aut = known group) ∧ (fine harvest, genuine) ∧ (fine ≤ coarse) — the structural support for the meta poly-canonization. | — |

## ChainDescent/RouteCTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SchemeRealizes` | 30-34 | A permutation realizes a scheme iso `S ≅ X` (preserves `schemeAdj`) — the combinatorial iso the cited classification supplies. | Definition |
| `warmRefine_congr_samePartition` | 38-45 | **Partition-congruence of warm refinement.** Refining two same-partition seed colourings yields same-partition results — the engine that lets the base-transport pass through `warmRefine`. | — |
| `mem_image_transport` | 47-53 | Membership transport under a permutation: `g i ∈ T.image g ↔ i ∈ T` (injectivity of `g`). | — |
| `indiv_samePartition_image` | 55-70 | **Seed transport.** The `T`-individualized colouring and the `g`-pullback of the `g(T)`-individualized colouring induce the same partition — index labels differ, the partition does not. | — |
| `signature_transport_iso` | 77-100 | **The cross-graph transport root.** A graph iso `g` (`adj₂∘g = adj₁`) carries `adj₁`'s 1-WL signature at `v` onto `adj₂`'s at `g v` — the two-adjacency generalization of `signature_transport`. | — |
| `sigKey_transport_iso` | 102-108 | Cross-graph transport of the refinement key `sigKey` along a graph iso `g`. | — |
| `refineStep_transport_iso` | 110-117 | Cross-graph transport of one 1-WL round `refineStep` along a graph iso `g`. | — |
| `iterate_refineStep_transport_iso` | 119-131 | Cross-graph transport of iterated `refineStep` — the `χ`-hypothesis re-establishes itself each round, so the induction carries it. | — |
| `warmRefine_transport_iso` | 133-142 | **The cross-graph WL-transport deliverable.** The whole `warmRefine` fixpoint transports along a graph iso `g` (`adj₂∘g = adj₁`) — the two-adjacency generalization of `warmRefine_transport`. | — |
| `separatesAtBoundedBase_transport` | 148-189 | **The L1 payoff.** `SeparatesAtBoundedBase` is invariant along a scheme iso (`SchemeRealizes f`) — transports the single light predicate, no `schemeEquiv`/`StabilizerAt`. | — |

## ChainDescent/RouteCNode4.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `reachesRigidOrCameron_viaAffineFormScheme_routeC` | 39-84 | **L4 — the affine-polar node-4 discharge via Route C, no `hFormCert`.** The abstract residue reaches the seal (same conclusion as `viaAffineFormScheme`) from the classification (`S ≅` the standard `VO^ε` scheme) + the pair-route scope — the separation is discharged internally (`exists_isotropySeparatesAtBaseK`) and transported (`separatesAtBoundedBase_transport`), so no `RelCountsDetermineOrbit`/`hFormCert` is carried. Supersedes the abstract hook for this family. | — |
| `routeC_polySupport_of_adapter` | 99-122 | **Track B engine.** From any `FormAdapter A` + a coarse over-group `Gc ≥ A.G₀` (mod the Skresanov `AffineSchemeTwoClosed`), the §9.0a poly-support triple: coarse Aut = `affineG Gc` ∧ fine harvest **extracted from the adapter** (no carried hypothesis) ∧ fine ≤ coarse. One engine, all four families. | — |
| `routeC_polySupport_alternating` | 123-143 | **Track B — alternating.** `routeC_polySupport_of_adapter` at the Plücker family (`alternatingAdapter` + `jointConeStab pluckerForms`); retires the island status of `reachesRigidOrCameron_alternating` at the meta level. | — |
| `routeC_polySupport_halfSpin` | 144-161 | **Track B — half-spin.** `routeC_polySupport_of_adapter` at the D₅ spinor family (`spinAdapter` + `jointConeStab spinorForms`). | — |
| `formConeStab` | 170-186 | **The cone stabilizer of an arbitrary (non-quadratic) form family** — setwise stabilizer of the joint zero locus; the graph-intrinsic coarse group for any forms graph. `jointConeStab` is the `QuadraticForm` case; `formConeStab (SFbar)` the Suzuki (cubic) case. | Definition |
| `suzukiG₀_le_formConeStab` | 193-203 | **Suzuki fine ⟶ coarse bridge** — a σ-twisted-form-value preserver preserves the ovoid cone, so `suzukiG₀ ≤ formConeStab (SFbar)`; the cubic analog of `iInf_isometryGroup_le_jointConeStab`. | — |
| `routeC_polySupport_suzuki` | 204-225 | **Track B — Suzuki–Tits.** `routeC_polySupport_of_adapter` at the σ-twisted ovoid family via the cubic `formConeStab (SFbar)`; completes the multi-form set. | — |

## ChainDescent/AffinePolarSeal.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `exists_pow_matching_lt` | 30-47 | Matching-length existence: `F < card W ⟹ ∃ m, (card ι)·Fᵐ < (card W)ᵐ` — supplies `exists_separating_base`'s hypothesis. | — |
| `exists_pow_matching_le` | 49-85 | The matching length with an explicit `Real.log` bound `m ≤ log(card ι)/log(card W/F) + 1` (standalone; the live chain uses the log-free `exists_pow_matching_block`). | — |
| `exists_pow_matching_block` | 87-122 | **Log-free matching-length keystone (REUSABLE).** From the ratio `64·F ≤ 63·(card W)`, a separating base exists of length `m ≤ 64·(Nat.log 2 (card ι) + 1) = O(log (card ι))` (block fact `2·63⁶⁴ ≤ 64⁶⁴`) — the non-vacuity backbone, no `Real.log`. | — |
| `exists_separating_base_of_split` | 124-149 | Matching mechanics: per-good-anchor fail bound `cN` + bad-anchor count `βN` + `cN+βN < card V` ⟹ a base `Fin m → V×V` whose 2-element sub-frames each target avoids. | — |
| `exists_separating_base_of_split_bounded` | 151-180 | The `exists_separating_base_of_split` sibling that also carries the logarithmic length bound `m ≤ 64·(Nat.log 2 (card ι)+1)`, from the ratio hypothesis `64·(cN+βN) ≤ 63·(card V)`. | — |
| `cbar_lt` | 182-202 | The `c̄₀<1` arithmetic: `16cN≤15N ∧ q·βN≤(2d+4)N+2q ∧ q≥32(2d+4) ∧ N>64 ⟹ cN+βN<N` (superseded in the live chain by the ratio bound; retained). | — |
| `jointIsoCountK_ne_of_sep` | 203-229 | Bridge wiring used by increment 5: the separation event (χ(I_u)≠χ(I_v) ∧ I_u,I_v≠0 ∧ Q(t₀-u),Q(t₀-v)≠0) discharges `jointIsoCountK_ne_of_chiSep_pair`'s hypotheses and fires the count inequality. | — |
| `exists_zProfileSeparatesK` | 230-380 | **The family assembly.** Running the matching trick over good/bad anchors produces a finite base `T` separating every distinct pivot pair in the joint isotropic counts (`ZProfileSeparatesK Q T`), with `T.card = O(d log q)`. | — |
| `exists_isotropySeparatesAtBaseK` | 381-402 | **The seal-ready deliverable.** A nondegenerate `Q` on `Fin d → K` (even `d≥2`, `q≳32d`) admits a finite base `T` with `IsotropySeparatesAtBaseK Q T` and `T.card ≤ 128·(Nat.log 2 (card V)²+1)` — exactly the input the Witt-free seal capstone consumes. | — |
| `reachesRigidOrCameron_affinePolar` | 403-439 | **The q=p affine-polar seal.** For an odd prime `p` and a nondegenerate quadratic form `Q` on `Fin d → ZMod p` (even `d≥2`, `p≥256`, `p≳32d`), the affine-polar VO^ε residue reaches the `reachesRigidOrCameron` disjunction modulo {G3} — Witt-free, no `hSmallAutThin` — carrying an explicit base bound… | — |
## ChainDescent/BadAnchorCount.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `fail_count_split` | 24-61 | **Anchor-averaging split — the increment-4 backbone.** For a fail predicate `fail : A → B → Prop` over a product space (`A` = probe, `B` = anchor), if every **good** anchor `b` has `#{a : fail a b} ≤ c` and the bad anchors number `≤ β`, then the total fail count over `A × B` is `≤ c·|B| + |A|·β`.… | — |
| `matching_F_bound` | 63-75 | **The matching-trick `F`, ready for `exists_separating_base`.** A target-indexed fail predicate `fail : ι → A → B → Prop` (`g = (u,v)`, `(a,b) = (t,t₀)`) with uniform per-good-anchor bound `c` and uniform bad-anchor count `β` gives, for *every* target, `#{(t,t₀) : fail g} ≤ c·|B| + |A|·β =: F`.… | — |
| `good_anchor_fail_le` | 77-130 | **Increment 4 — the good-anchor fail bound (input `c`).** For a **good anchor** `t₀` (the `c0_le_threequarters` hypotheses `hnz`/`hgood`/`hPu` + the size thresholds), the probes `t` that the bridge FAILS to use for separation — those where the separation criterion `χ(I_u(t)) ≠ χ(I_v(t)) ∧ I_u(t) ≠…` | — |
| `zeroCountShift_card_le` | 132-175 | **The shifted zero-count bound (the remaining piece of input `c`).** For any *nonzero* quadratic form `P` and shift `u`, `#{t : P(t−u) = 0} · |K| ≤ |V| + (|K|−1)·|V|/√|K|` — so `#{t : P(t−u)=0}/|V| ≤ 1/q + (q−1)/(q√q) = O(1/√q)`. Reindex `t ↦ t−u` to the homogeneous count, then `zeroCount_sq_le`… | — |
| `good_anchor_fail_le_const` | 177-224 | **The good-anchor fail bound (matching input `c`).** On a good anchor, `#{t : ¬separated} ≤ 15/16·(card V)`. | — |
| `mvPoly_zeros_count_le_dim` | 232-253 | **Schwartz–Zippel in `Fin d` — the bad-anchor counting engine.** For a *nonzero* `d`-variable polynomial `p`, the zero set over `K^d` satisfies `#{f : Fin d → K | eval f p = 0} · |K| ≤ p.totalDegree · |K^d|`, i.e. `#{zeros}/|K^d| ≤ totalDegree/|K| = O(1/q)`. | — |
| `mem_polarRad_smul_pairForm` | 258-267 | Every scalar multiple `c • pairForm Q a` has the anchor `a` in its polar-radical (`pairForm_polar_anchor` transports through `polar_smul`). | — |
| `polarRad_smul_pairForm_ne_bot` | 269-274 | A nonzero scalar-multiple-of-`pairForm` form has nontrivial radical (the anchor `a ≠ 0`), hence is degenerate. | — |
| `hPu_of_hgood` | 276-284 | **`hgood ⟹ hPu`.** A nondeg pencil member forces `pairForm Q (t₀−u) ≠ 0`: if it were `0` the pencil would reduce to `z • pairForm Q (t₀−v)`, degenerate (anchor `t₀−v ≠ 0`). | — |
| `hPv_of_hgood` | 286-293 | **`hgood ⟹ hPv`** (symmetric to `hPu_of_hgood`). | — |
| `hnz_of_hgood` | 295-310 | **`hgood ⟹ hnz`.** A nondeg pencil member forbids a zero member on `y,z ≠ 0`: a zero member makes `pairForm Q (t₀−u) ∝ pairForm Q (t₀−v)`, collapsing the *whole* pencil to a scalar multiple of the (degenerate) `pairForm Q (t₀−v)` — so no member could be nondegenerate. | — |
| `bad_anchor_card_le_hgood` | 311-352 | **The bad-anchor reduction (input `β`).** The full good-anchor predicate `hnz ∧ hgood ∧ hPu ∧ hPv` (what `good_anchor_fail_le_const` consumes) fails on at most `#{t₀ : ¬hgood} + 2` anchors — i.e. `β ≤ #{¬hgood} + 2`. | — |
| `bad_anchor_count_le_of_poly` | 360-398 | **Bad-anchor count via a representing polynomial — the rigorous Schwartz–Zippel reduction.** If a bad-anchor predicate `badpred` is contained in the zero set of a *nonzero* polynomial `P` read off the anchor's coordinates (`hrep : badpred t₀ → eval (b.equivFun t₀) P = 0`), then `#{t₀ : badpred} ·…` | — |
| `notHgood_eval_zero_of_repr` | 399-415 | **`hrep` for `¬hgood`, from a representing polynomial.** If `P` represents the pencil-determinant at a fixed witness `(y₀,z₀)` — `eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u + z₀•pairForm_v)))` — then on every `¬hgood` anchor `eval (coords t₀) P = 0` (the witness member is… | — |
## ChainDescent/Coordinatization.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `coordPoly` | 35-37 | The degree-`≤1` polynomial with coefficient function `g` on the coordinate variables. | Definition, `noncomputable` |
| `coordPoly_eval` | 39-41 | Evaluation: `coordPoly` of a linear functional, at the coordinate point `b.equivFun t₀`, recovers the functional's value at `t₀`. | `@[simp]` |
| `linFunc_eq_sum` | 43-49 | A linear functional expanded over the basis: `f t₀ = ∑ₖ f(bₖ)·(coords t₀)ₖ`. | — |
| `coordPoly_eval_linFunc` | 51-55 | **The coordinatization workhorse.** A linear functional `f` is represented by `coordPoly (f ∘ b)`: its evaluation at the coordinates of `t₀` is `f t₀`. | — |
| `polar_t0_t0_sum` | 57-72 | The diagonal bilinear expansion `polar Q t₀ t₀ = ∑_{k,l} polar Q bₖ bₗ · xₗ · xₖ` (`x = coords t₀`), by applying the linear-functional expansion twice (`polarBilin Q` is bilinear). | — |
| `gramQuadPoly` | 74-76 | The polynomial representing `Q(t₀)` (the diagonal Gram quadratic, scaled by `⅟2`). | Definition, `noncomputable` |
| `gramQuadPoly_eval` | 78-91 | Evaluation: `gramQuadPoly b Q` at `b.equivFun t₀` equals `Q t₀` — the quadratic form as a polynomial in the coordinates (needs `Invertible 2`). | — |
| `LPoly` | 93-95 | The polynomial representing the affine-linear `polar Q w (t₀ − c)`. | Definition, `noncomputable` |
| `LPoly_eval` | 97-103 | Evaluation: the affine linear polynomial `LPoly` at `b.equivFun t₀` recovers `polar Q w (t₀ - c)`. | — |
| `QPoly` | 105-107 | The polynomial representing the quadratic `Q (t₀ − c)`. | Definition, `noncomputable` |
| `QPoly_eval` | 109-119 | Evaluation: the affine quadratic polynomial `QPoly` at `b.equivFun t₀` recovers `Q (t₀ - c)`. | — |
| `polar_pairForm_apply` | 121-131 | The general polar of `pairForm Q a`: `polar(pairForm Q a) s r = 4 Q(a)·polar Q s r − 2·polar Q s a·polar Q r a` (the `r = a` case is `pairForm_polar_anchor`). | — |
| `entryPoly` | 133-137 | The polynomial representing the Gram entry `polar(pairForm Q (t₀−a))(bᵢ)(bⱼ)`. | Definition, `noncomputable` |
| `entryPoly_eval` | 139-144 | Evaluation: `entryPoly b Q a i j` at `b.equivFun t₀` equals the Gram entry `polar (pairForm Q (t₀-a)) (b i) (b j)`. | — |
| `pencilDetPoly` | 146-150 | **The representing polynomial `P`** for the pencil determinant at witness `(y₀,z₀)`: the determinant of the `d×d` matrix of Gram-entry polynomials. | Definition, `noncomputable` |
| `pencilDetPoly_eval` | 152-163 | **`P` represents the pencil determinant** — `eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u + z₀•pairForm_v)))`. Via `RingHom.map_det` (eval is a ring hom) + the per-entry `entryPoly_eval` + `polar_pencil`. | — |
| `pencilDetPoly_ne_zero` | 165-175 | **`P ≠ 0`** when there is a good anchor `t₀₀` with witness `(y₀,z₀)` (`polarRad = ⊥` there): the determinant is nonzero at `t₀₀`'s coordinates (`polarRad_ne_bot_iff_det_eq_zero`), so the polynomial cannot vanish identically. | — |
| `det_totalDegree_le_gen` | 185-199 | **Per-entry degree bound for a determinant (general `D`).** Generalizes `PencilTBound.det_totalDegree_le` (linear pencil, `D = 1`, `Fin 2` variables) to entries of `totalDegree ≤ D` over any variable type: the determinant of a `d × d` matrix has `totalDegree ≤ D · d`. | — |
| `coordPoly_totalDegree_le` | 201-206 | `coordPoly` (a coordinate linear functional) has total degree ≤ 1. | — |
| `gramQuadPoly_totalDegree_le` | 208-220 | `gramQuadPoly` (the quadratic form as a coordinate polynomial) has total degree ≤ 2. | — |
| `LPoly_totalDegree_le` | 222-227 | The affine linear polynomial `LPoly` has total degree ≤ 1. | — |
| `QPoly_totalDegree_le` | 229-237 | The affine quadratic polynomial `QPoly` has total degree ≤ 2. | — |
| `entryPoly_totalDegree_le` | 239-253 | The Gram-entry polynomial has total degree ≤ 2 (so its `d×d` determinant `pencilDetPoly` has degree ≤ 2d). | — |
| `pencilDetPoly_totalDegree_le` | 255-269 | **`totalDegree (pencilDetPoly) ≤ 2·d`** (B-iii). The determinant of the `d × d` matrix of quadratic Gram-entry polynomials, via `det_totalDegree_le_gen` at `D = 2` (each entry `C y₀·entryPoly_u + C z₀·entryPoly_v` is quadratic). | — |
| `badHgood_count_le` | 270-285 | **`#{¬hgood}` bounded — the bad-anchor Schwartz–Zippel count.** Instantiating `bad_anchor_count_le_of_poly` at the constructed `P = pencilDetPoly` (nonzero by the good-anchor witness, representing by `pencilDetPoly_eval`): `#{t₀ : ¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`, i.e. density `≤…` | — |
| `beta_count_closed` | 286-325 | **B-ii — `β` closed to an explicit `O(d/q)` bound.** Composing `badHgood_count_le` (`#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`) with B-iii (`pencilDetPoly_totalDegree_le`, `totalDegree ≤ 2d`) and the landed `BadAnchorCount.bad_anchor_card_le_hgood` (`β ≤ #{¬hgood} + 2`): the **full**… | — |
| `corr_zero_of_anchor` | 335-337 | A good anchor (`Q(t₀−u) ≠ 0`) kills the bridge's `corr` condition for every probe `t`: `¬(Q(t−u)=0 ∧ Q(t₀−u)=0)`. | — |
| `QPoly_ne_zero` | 339-347 | `QPoly b Q c ≠ 0` whenever the form is nonzero somewhere (`Q w₀ ≠ 0`): its value at `t₀ = w₀ + c` is `Q w₀ ≠ 0`. | — |
| `qZero_count_le` | 348-360 | **The corr-locus count.** `#{t₀ : Q(t₀−c)=0}·|K| ≤ 2·|V|` (a quadric in `t₀`), via the SZ engine on `QPoly` (`QPoly_eval`/`QPoly_totalDegree_le`). | — |
| `beta_full_count_closed` | 361-432 | **The bad-anchor density (matching input `β`).** The non-good anchors satisfy `β·(card K) ≤ (2d+4)·(card V) + 2·(card K) = O(d/q)·(card V)`, via Schwartz–Zippel on the pencil-determinant polynomial. | — |
| `exists_orthoAnisotropic_basis` | 444-455 | **C-basis.** A nondegenerate (`SeparatingLeft`) quadratic form `Q` over a finite-dimensional space (char ≠ 2) has an **orthogonal basis of anisotropic vectors** — exactly the `vb`/`hv`/`hw` the bridge `jointIsoCount_ne_of_chiSep_pair` carries. A `Q`-level fact (no anchor/probe), discharged once… | — |
| `associated_separatingLeft_of_polarRad` | 457-472 | **Bridge to the project-native nondegeneracy.** `polarRad Q = ⊥` (the form used throughout — `hgood`, `degenerate_count_le`, `polarRad_ne_bot_iff_det_eq_zero`) gives `(associated Q).SeparatingLeft`, the hypothesis of `exists_orthoAnisotropic_basis`. Chain: `polarRad = ⊥ ↔ (polarBilin…` | — |
## ChainDescent/FieldGeneric.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `isoClassK` | 32-36 | **Isotropy class** of `w : Fin d → K` under `Q`: `0` (zero vector), `1` (nonzero isotropic), `2` (anisotropic). | Definition, `noncomputable` |
| `isoClassK_eq_zero_iff` | 37-46 | Class `0` ⟺ the zero vector. | — |
| `isoClassK_eq_two_iff` | 47-56 | Class `2` ⟺ anisotropic (`Q w ≠ 0`). A *pure* `Q`-value condition. | — |
| `isoClassK_eq_one_iff` | 57-66 | Class `1` ⟺ nonzero isotropic (`w ≠ 0 ∧ Q w = 0`). | — |
| `isoClassK_ne_two_iff` | 67-70 | The coarse "isotropic-or-zero" split: `isoClassK ≠ 2` ⟺ `Q w = 0`. | — |
| `polar_eq_of_subK` | 75-84 | `polar Q v e = Q v + Q e − Q (v − e)`. | — |
| `coords_determineK` | 85-100 | **The back-half — form coordinates determine the vector.** Same `Q`-profile on the standard basis frame + nondegenerate polar form ⟹ `v = v'`. (V-indexed; the `affineE.symm.injective` step of the original vanishes.) | — |
| `jointIsoCountK` | 105-112 | **The joint isotropic count `Z_u(S)`** over `V = Fin d → K`, indexed directly (no `affineE`). | Definition, `noncomputable` |
| `ZProfileSeparatesK` | 113-121 | **The reduced crux predicate `ZProfileSeparates`** (V-indexed). Agreeing joint isotropic counts over every sub-frame `S ⊆ T` ⟹ the same `Q`-profile over the standard basis frame. | Definition, `noncomputable` |
| `QProfileSeparatesAtBaseK` | 122-135 | **`QProfileSeparatesAtBase`** (V-indexed): agreeing fine isotropy counts at `T` ⟹ the `Q`-profile agrees. | Definition, `noncomputable` |
| `IsotropySeparatesAtBaseK` | 136-147 | **`IsotropySeparatesAtBase`** (V-indexed): the fine isotropy-count profile at `T` separates all vertices. | Definition, `noncomputable` |
| `extProfileK` | 151-156 | Extend a `T`-indexed isotropy profile to a full profile (junk `0` off `T`). | Definition, `noncomputable` |
| `extProfileK_mem` | 157-160 | On `t ∈ T`, the extended isotropy profile `extProfileK σ` agrees with `σ` (abstract-K version). | — |
| `qProfileSeparatesAtBaseK_of_zProfileSeparatesK` | 161-241 | **D1 — `ZProfileSeparatesK` ⟹ `QProfileSeparatesAtBaseK`.** Marginalise the fine profile over base-points ∉ `S` and the pivot class. (Faithful V-indexed copy of `ProfileReduction.qProfileSeparatesAtBase_of_zProfileSeparates`.) | — |
| `isotropySeparatesK_of_qProfileSeparatesK` | 243-250 | **`QProfileSeparatesAtBaseK` ⟹ `IsotropySeparatesAtBaseK`** (V-indexed): the recovered `Q`-profile pins the vector via `coords_determineK` directly (no `affineE.symm.injective`). | — |
| `isotropySeparatesK_of_zProfileSeparatesK` | 252-257 | **End-to-end reduction (abstract K).** `ZProfileSeparatesK Q T` ⟹ `IsotropySeparatesAtBaseK Q T` when `Q.polarBilin` is nondegenerate. | — |
| `jointIsoCountK_eq_restricted` | 262-290 | **D2 (bridge)** — `jointIsoCountK Q u S` as the Lemma-A-ready restricted count over `V`: nonzero `w` on the cone `Q w = 0` whose shift by each config vector `t − u` (`t ∈ S`) stays isotropic. The original's `count_transport` (`Fin (p^d) ↔ V`) step is gone — we are already in `V`. | — |
| `zProfileSeparatesK_of_zSep` | 298-309 | **Soft endpoint.** If every distinct pivot pair is separated by some sub-frame `S ⊆ T` in the joint isotropic counts, then `ZProfileSeparatesK Q T` holds (pure logic on the predicate). | — |
| `isoClassK_eq_isoClass` | 319-329 | The V-indexed `isoClassK` (abstract `K`, here `K = ZMod p`) agrees with the build's `Fin (p^d)`-flavoured `isoClass` on the vector space — both are `if w = 0 then 0 else if Q w = 0 then 1 else 2`. | — |
| `isoCount_transport` | 330-361 | **The relabel.** For a single pivot `w : Fin (p^d)`, the V-indexed isotropy-profile count (at base `T.image affineE.symm`, profile `σV`, pivot class `c`) equals the build's `Fin (p^d)`-indexed count (at base `T`, profile `σV ∘ affineE.symm`, pivot class `c`), via the bijection `affineE`. | — |
| `isotropySeparatesAtBase_of_K` | 363-376 | **The q = p adapter.** `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` (the abstract-K, V-indexed predicate of `FieldGeneric`) ⟹ `IsotropySeparatesAtBase Q T` (the build's `Fin (p^d)`-indexed predicate). Pure relabel: descend to `V` via `affineE.symm.injective`, transport the count agreement… | — |
| `reachesRigidOrCameron_viaIsotropySeparatesK_wittFree` | 378-391 | **The q=p adapter.** The abstract-`K` predicate `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` reaches the in-build `Fin(p^d)`-indexed Witt-free seal capstone (a pure `affineE` relabel). | — |
## ChainDescent/GoodAnchorNonvacuity.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `polar_pencil_apply` | 36-48 | **NV-1 — the pencil polar formula.** The polar of a pencil member `y • pairForm Q a + z • pairForm Q b` is `4c · polar Q s r − 2y · polar(s,a)·polar(r,a) − 2z · polar(s,b)·polar(r,b)` with `c = y·Q(a) + z·Q(b)`. Pure algebra on `polar_pairForm_apply` + bilinearity (`polar` of a sum/scalar-multiple… | — |
| `pencil_radical_key` | 50-71 | **The radical equation (shared by NV-2/NV-3).** For nondegenerate `Q`, `s ∈ polarRad B` forces `(4c)·s = (2y·polar(s,a))·a + (2z·polar(s,b))·b` (`c = y·Q(a)+z·Q(b)`), by inverting the nondegenerate `polar Q` against the NV-1 polar formula. | — |
| `polarRad_pencil_subset_span` | 73-89 | **NV-2 — the radical lands in `⟨a,b⟩`.** For nondegenerate `Q`, if `c = y·Q(a)+z·Q(b) ≠ 0` then every `s ∈ polarRad (y • pairForm Q a + z • pairForm Q b)` lies in `span K {a,b}` (divide `pencil_radical_key` by `4c ≠ 0`). | — |
| `polarRad_pencil_eq_bot` | 91-139 | **NV-3 — the pencil member is nondegenerate.** For nondegenerate `Q` with `y,z ≠ 0`, `c = y·Q(a)+z·Q(b) ≠ 0`, and `pairForm Q a b ≠ 0` (⟺ `⟨a,b⟩` a nondegenerate plane), the member `y • pairForm Q a + z • pairForm Q b` is **nondegenerate** (`polarRad = ⊥`). Evaluating the radical equation at `r =…` | — |
| `pairForm_self_sub` | 148-159 | **The plane-discriminant formula.** `pairForm Q a (a−w) = 4·Q(a)·Q(w) − polar(a,w)²` — the determinant of the Gram of `⟨a, a−w⟩ = ⟨a, w⟩`, a **degree-2** polynomial in `a` (key for the NV-4 counting). | — |
| `exists_ne_zero_polar_eq_zero` | 161-179 | A nonzero vector orthogonal to `w` exists once `finrank V ≥ 2`: the functional `b ↦ polar Q b w` has a kernel of positive dimension (rank-nullity, codomain `K` is `1`-dimensional). | — |
| `exists_pairForm_self_sub_ne_zero` | 181-232 | **NV-4a — the geometric witness.** For nondegenerate `Q`, `w ≠ 0`, `finrank V ≥ 2`, the plane discriminant `pairForm Q a (a−w) = 4 Q a Q w − polar(a,w)²` is **not identically zero** in `a`. Otherwise `Q` would satisfy `4 Q a Q w = polar(a,w)²` for all `a` — a rank-≤1 form (its polar would vanish on… | — |
| `exists_anisotropic` | 234-247 | A nondegenerate `Q` over a nontrivial space is **not the zero form** — `∃ a, Q a ≠ 0` (else `polar Q ≡ 0`, so `polarRad Q = ⊤ ≠ ⊥`). | — |
| `gramQuadPoly_ne_zero` | 253-261 | `gramQuadPoly b Q ≠ 0` when `Q` is nonzero somewhere (`gramQuadPoly_eval = Q t₀`). | — |
| `planeDiscPoly` | 263-267 | The polynomial representing the plane discriminant `pairForm Q a (a−w) = 4·Q(a)·Q(w) − polar(a,w)²`. | Definition, `noncomputable` |
| `planeDiscPoly_eval` | 269-277 | Evaluation: `planeDiscPoly b Q w` at `b.equivFun a` equals `pairForm Q a (a - w)` — the plane discriminant as a coordinate polynomial. | — |
| `planeDiscPoly_totalDegree_le` | 279-291 | Total-degree bound for the plane-discriminant polynomial (feeds Schwartz–Zippel in the non-vacuity count). | — |
| `planeDiscPoly_ne_zero` | 293-299 | The plane-discriminant polynomial is nonzero given a point where `pairForm Q a₀ (a₀-w) ≠ 0` — so Schwartz–Zippel bounds its zero set. | — |
| `exists_good_plane_anchor` | 301-358 | **NV-4 — an anisotropic-generator nondegenerate plane through `w`.** For nondegenerate `Q`, `w ≠ 0`, `finrank V ≥ 2`, `|K| ≥ 7`: there is `a` with `Q a ≠ 0`, `Q (a−w) ≠ 0`, and `pairForm Q a (a−w) ≠ 0`. The three bad loci are quadrics (each `≤ 2·|V|/|K|` by Schwartz–Zippel on… | — |
| `linearIndependent_of_pairForm_ne_zero` | 360-375 | **`pairForm` nonvanishing ⟹ linear independence.** `pairForm Q a b = 4·Q(a)·Q(b) − polar(a,b)²` is the Gram determinant of `{a,b}` under `polar Q`, so it vanishes whenever `a, b` are linearly dependent (if `b = c•a` then `pairForm Q a (c•a) = 4c²Q(a)² − (2cQ(a))² = 0`). Contrapositive: a nonzero… | — |
| `exists_hgood` | 377-411 | **Good-anchor non-vacuity.** For `u≠v`, nondegenerate `Q`, `finrank≥2`, `card K ≥ 7`, a good anchor exists (a witness `t₀` and pencil coefficients with vanishing polar radical); the conclusion also exposes `Q(t₀-u)≠0` and the linear independence of `t₀-u, t₀-v`. | — |
## ChainDescent/IsotropicIncidenceCount.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `isoIncidence_eq_linearConds` | 27-44 | **Lemma A, step A1 — the isotropic-incidence count rewrites with LINEAR conditions.** On the cone `Q w = 0`, the condition `Q (w − a j) = 0` is equivalent to the affine-linear `polar Q w (a j) = Q (a j)` (by the polar identity `polar Q w a = Q w + Q a − Q (w − a)`). So the count is over linear… | — |
| `map_add_of_polar_zero` | 46-53 | **Lemma A, step A4-core — `Q` is additive across a polar-orthogonal pair.** If `polar Q w x = 0` then `Q (w + x) = Q w + Q x`. (This is what makes the affine level-set HOMOGENEOUS once `w₀ ⊥ Uᗮ`.) | — |
| `count_coset` | 55-77 | **Lemma A, step A3 — the linear-condition count is a count over the kernel coset.** Given any `w₀` realizing the affine system (`polar Q w₀ (a j) = Q (a j)`), the solution set of the system is `w₀ + Uᗮ` (`Uᗮ = {x | ∀ j, polar Q x (a j) = 0}`), so the cone-count over the system equals the count… | — |
| `polar_w0_perp` | 79-88 | **Lemma A, step A4-link — `w₀ ∈ span{a j}` is polar-orthogonal to `Uᗮ`.** If `w₀ = ∑ k, c k • a k` and `x` is in `Uᗮ` (`∀ j, polar Q x (a j) = 0`), then `polar Q w₀ x = 0`. (Polar bilinearity, `polar_sum_right`.) | — |
| `reduction_to_levelset` | 90-110 | **Lemma A, steps A1+A3+A4 combined — the count is a HOMOGENEOUS level-set count over `Uᗮ`.** Given a spanning solution `w₀ = ∑ k, c k • a k` of the affine system (`polar Q w₀ (a j) = Q (a j)`), the isotropic-incidence count equals the count, over `Uᗮ = {x | ∀ j, polar Q x (a j) = 0}`, of `x` with… | — |
| `spanning_w0_exists` | 112-131 | **Lemma A, step A-M2 — a spanning `w₀` exists when the config Gram is nondegenerate.** If the Gram matrix `G i j = polar Q (a i) (a j)` is invertible (`IsUnit G.det`), then `c := (Q ∘ a) ᵥ* G⁻¹` realizes the affine system: `w₀ = ∑ k, c k • a k` satisfies `polar Q w₀ (a j) = Q (a j)` for all `j`.… | — |
| `reduction_to_levelset_nondeg` | 133-149 | **Lemma A, A-M1 ∘ A-M2 — the reduction, unconditional on nondegenerate configs.** If the config Gram matrix is invertible, the isotropic-incidence count is the HOMOGENEOUS level-set count `#{x ∈ Uᗮ : Q x = − Q w₀}` for the explicit `w₀ = ∑ k, c k • a k` (`c` from `spanning_w0_exists`). The… | — |
| `levelset_fourier` | 150-198 | **Lemma A, step A-M3 increment 1 — the Fourier expansion of the level-set count over the FULL space `V`** (Route B, §10.10). The level-set count `#{x : (∀ j, polar Q x (a j)=0) ∧ Q x = c}`, scaled by `q^{m+1}`, is a double character sum indexed by `Option (Fin m)`: the `none` slot carries the… | — |
| `levelset_fourier_prod` | 199-219 | **Lemma A, step A-M3 increment 2a — reindex the dual sum into `(s, ρ)` product form.** Splits the `Option (Fin m) → F` dual variable into the quadratic dual `s = r none` and the linear duals `ρ = r ∘ some` (via `Equiv.piOptionEquivProd`), so the inner sum is `∑_x ψ(s·Q x + polar Q x (∑ⱼ ρⱼ•aⱼ))` —… | — |
| `levelset_fourier_split` | 220-251 | **Lemma A, step A-M3 increment 2b — the `s`-split (D1 on the bulk).** Split the quadratic dual `∑_s` at `s = 0`. The `s = 0` boundary leaves the linear sum `∑_ρ ∑_x ψ(polar Q x (∑ⱼ ρⱼ•aⱼ))` (collapsed in 2c via `sum_addChar_linearMap` + config-vector independence, where nondegeneracy enters). | — |
| `s0_boundary_collapse` | 252-304 | **Lemma A, step A-M3 increment 2c — the `s = 0` boundary collapses to `q^d`.** The boundary sum `∑_ρ ∑_x ψ(polar Q x (∑ⱼ ρⱼ•aⱼ))` equals `|V| = q^d`. Pointwise (`sum_addChar_linearMap`, with the linear functional `φ_ρ = (polarBilin Q).flip (∑ⱼ ρⱼ•aⱼ)`), the inner `x`-sum is `|V|·[φ_ρ = 0]`; and… | — |
| `levelset_count_eq` | 305-323 | **Lemma A, step A-M3 ASSEMBLED — the level-set count in closed form up to the two Gauss sums (Route B).** For a nondegenerate config Gram (`IsUnit G.det`), the level-set count satisfies `count·q^{m+1} = |V| + ∑_{s≠0} ψ(−s·c)·(ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))·∑_x ψ(s·Q x)) summed over ρ`. The `|V|` is the `s=0`… | — |
| `configForm` | 327-331 | **The config quadratic form** `QR(ρ) = Q(∑ⱼ ρⱼ•aⱼ)` on `Fin m → ZMod p`, as `Q.comp L` with `L` the linear-combination map. Its associated bilinear (Gram) at the standard basis is the config Gram `G`. | Definition, `noncomputable` |
| `configForm_apply` | 333-336 | Unfolds `configForm Q a` — the quadratic form pulled back along a `Fin m` configuration `a`. | `@[simp]` |
| `linComb_single` | 338-340 | `Fintype.linearCombination a (Pi.single i 1) = a i` (single-index linear combination selects the i-th vector). | — |
| `polar_configForm` | 342-348 | The polar of the config form transports along `L`. | — |
| `polar_configForm_single` | 350-357 | **The config form's Gram = the config Gram `G`** (at the standard basis). | — |
| `configForm_nondegenerate` | 358-394 | **A-M4a gap-2 — the config form's associated bilinear is nondegenerate** (from `IsUnit G.det`). If `∀ y, associated QR x y = 0`, then in particular `polar QR x (eᵢ) = 0 ∀ i`, i.e. | — |
| `configForm_exists_orthoBasis` | 395-415 | **A-M4a gap-3 — an orthogonal *anisotropic* basis of the config form `QR`** (from nondegeneracy, gap-2). The `(v, hv, hw)` triple the Gauss toolkit (`sum_quadForm_eval` / `sum_addChar_quadForm_smul`) consumes. | — |
| `configGaussSum_eval` | 416-439 | **A-M4a gap-4 — the config-form Gauss sum** (composing the two landed toolkit lemmas). For an orthogonal anisotropic basis `v` of `QR = configForm Q a` and a unit scalar `s`, `∑_ρ ψ(s·QR ρ) = χ(s)^n · (∏ᵢ χ(QR vᵢ)) · gaussSum^n` (`n = finrank`, `χ` the quadratic character cast to `R'`). | — |
| `prod_quadChar_eq_det` | 440-488 | **A-M4a gap-5 (THE CRUX) — the discriminant collapse.** The basis-dependent factor `∏ᵢ χ(QR vᵢ)` from gap-4 equals `χ(D)`, where `D = det` of the Gram of `associated QR` at the canonical reference basis `b₀ = finBasis` — a **basis-free config invariant**. Proof: in `v` the Gram is `diagonal (QR∘v)`… | — |
| `configGaussSum_eq_det` | 489-510 | **A-M4a config-side ASSEMBLED — the config Gauss sum, basis-free** (gap-3 ∘ gap-4 ∘ gap-5). Eliminating the existential orthogonal basis, for a nondegenerate config Gram (`IsUnit G.det`) and unit `s`, `∑_ρ ψ(s·QR ρ) = χ(s)^n · χ(D) · gaussSum^n`, where `D = det` of the Gram of `associated QR` at… | — |
## ChainDescent/IsotropicIncidenceCountK.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `isoIncidence_eq_linearCondsK` | 20-37 | **A1 (K)** — isotropic-incidence count rewrites with LINEAR conditions. | — |
| `map_add_of_polar_zeroK` | 38-44 | **A4-core (K)** — `Q` is additive across a polar-orthogonal pair. | — |
| `count_cosetK` | 46-67 | **A3 (K)** — the linear-condition count is a count over the kernel coset. | — |
| `polar_w0_perpK` | 68-76 | **A4-link (K)** — `w₀ ∈ span{a j}` is polar-orthogonal to `Uᗮ`. | — |
| `reduction_to_levelsetK` | 78-95 | **A1+A3+A4 (K)** — the count is a HOMOGENEOUS level-set count over `Uᗮ`. | — |
| `spanning_w0_existsK` | 96-112 | **A-M2 (K)** — a spanning `w₀` exists when the config Gram is nondegenerate. | — |
| `reduction_to_levelset_nondegK` | 114-127 | **A-M1 ∘ A-M2 (K)** — the reduction, unconditional on nondegenerate configs. | — |
| `levelset_fourierK` | 128-169 | **A-M3 inc 1 (K)** — the Fourier expansion of the level-set count over the FULL space `V`. | — |
| `levelset_fourier_prodK` | 170-187 | **A-M3 inc 2a (K)** — reindex the dual sum into `(s, ρ)` product form. | — |
| `levelset_fourier_splitK` | 188-214 | **A-M3 inc 2b (K)** — the `s`-split (D1 on the bulk). | — |
| `s0_boundary_collapseK` | 215-263 | **A-M3 inc 2c (K)** — the `s = 0` boundary collapses to `q^d`. | — |
| `levelset_count_eqK` | 264-276 | **A-M3 ASSEMBLED (K)** — the level-set count in closed form up to the two Gauss sums. | — |
| `configFormK` | 280-285 | **The config quadratic form (K)** `QR(ρ) = Q(∑ⱼ ρⱼ•aⱼ)` on `Fin m → K`. | Definition, `noncomputable` |
| `configFormK_apply` | 286-291 | Unfolds `configFormK Q a` (the abstract-K config form). | `@[simp]` |
| `linComb_singleK` | 292-296 | Abstract-K version of `linComb_single`: `Fintype.linearCombination a (Pi.single i 1) = a i`. | — |
| `polar_configFormK` | 297-305 | The polar of the config form transports along `L`. | — |
| `polar_configFormK_single` | 306-314 | **The config form's Gram = the config Gram `G`** (K). | — |
| `configFormK_nondegenerate` | 315-349 | **A-M4a gap-2 (K)** — the config form's associated bilinear is nondegenerate. | — |
| `configFormK_exists_orthoBasis` | 350-366 | **A-M4a gap-3 (K)** — an orthogonal *anisotropic* basis of the config form `QR`. | — |
| `configGaussSum_evalK` | 367-385 | **A-M4a gap-4 (K)** — the config-form Gauss sum. | — |
| `prod_quadChar_eq_detK` | 386-426 | **A-M4a gap-5 (K, THE CRUX)** — the discriminant collapse. | — |
| `configGaussSum_eq_detK` | 427-444 | **A-M4a config-side ASSEMBLED (K)** — the config Gauss sum, basis-free. | — |
## ChainDescent/Matching.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `exists_separating_base` | 20-63 | **The matching-trick first moment (REUSABLE, general).** If every target's fail-set has at most `F` elements and `(card ι)·Fᵐ < (card W)ᵐ`, then some length-`m` base `Fin m → W` separates every target. Pure cardinality / union bound — no probability. | — |
## ChainDescent/ObservableCountBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `levelset_count_collapse` | 35-128 | **The `|S|`=2, even-d closed form.** For a config-nondegenerate Gram and even `d`, the homogeneous level-set count collapses to `count·q³ = card V + χ(D)·(gaussSum²·∑ψ(Q))·(q·[c=0]−1)`, the config dependence entering only through the pair invariant `χ(D)`. | — |
| `fullcount_eq_jointIsoCount_add_corr` | 129-143 | **B1a wrap (i) — `fullcount = jointIsoCount + (y=0 correction)`.** The Lemma-A fullcount over `V` (`#{y : Q y = 0 ∧ ∀ t∈S, Q(y−(t̄−ū)) = 0}`, the `reduction_to_levelset_nondeg` entry point) equals the observable `jointIsoCount Q u S` (the same count restricted to `y ≠ 0`) plus the correction `[∀…` | — |
| `fullcount_pair_eq_levelset` | 144-179 | **B1a wrap (ii-a) — fullcount over `{t,t₀}` = the homogeneous level-set count.** Index the pair `{t,t₀}` as the `Fin 2` config `a = ![t̄−ū, t̄₀−ū]`; on the config-nondegenerate locus (`hG : IsUnit (config Gram det)`) the Lemma-A fullcount equals the level-set count of `Q|_{Uᗮ}` at level `−Q w₀` for… | — |
| `fullcount_pair_closed` | 180-216 | **B1a wrap (ii-b) — the fullcount closed form over `{t,t₀}`.** Composing wrap (ii-a) with `levelset_count_collapse`: for even `d` and a config-nondegenerate Gram, the Lemma-A fullcount over `{t,t₀}` satisfies `fullcount · q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀ = 0] − 1)`, with `w₀ = ∑ c k • a k`… | — |
| `configPolarDet_eq_pairForm` | 217-233 | The config polar-Gram determinant (the `IsUnit` hypothesis matrix of `fullcount_pair_closed`/`levelset_count_collapse`) is the pair invariant `pairForm`. `det_fin_two` + `polar_self` (`polar Q x x = 2 Q x`) + `polar_comm` + the structural `detG2_eq_pairForm` (`4 Q(a₀) Q(a₁) − B(a₀,a₁)² = pairForm`). | — |
| `chi_configDet_eq_chi_pairForm` | 235-315 | **χ-kills-squares (REUSABLE).** `χ(det config-Gram) = χ(I_w(t))`: the `½·polar` factor-2 and the change-of-basis determinant enter only as squares, so the quadratic character erases them — no identification of the basis with the standard one is needed. | — |
| `chi_eq_one_or_neg_one` | 317-328 | The quadratic character of a nonzero element is `±1` (its square is `1`, a domain has no other roots). | — |
| `chiSep_imp_zSep_field` | 330-356 | **The ℂ-restated B1b (`chiSep_imp_zSep`) over a `CharZero` field.** The four-value distinctness of the closed form `n + c·K·(q·b − 1)` (`c ∈ {±1}`, `b ∈ {0,1}`, `K ≠ 0`, `q > 2`), but stated over a `CharZero` field `F` (= ℂ), so the `R' → ℕ` integrality descent is unnecessary — distinctness holds… | — |
| `pairCount_ne_of_chiSep_field` | 358-371 | **B1b in count form over a `CharZero` field — the per-pair bridge step.** Two pivots whose pair invariants `χ(I)` differ (`hne`) have different joint isotropic counts at a sub-frame, given each point's closed form `Z_w · q³ = n + χ_w·K·(q·b_w − 1)`. The ℂ analogue of… | — |
| `jointIsoCount_pair_closed_corr0` | 372-414 | **B1a final assembly — the observable per-pair closed form (corr = 0).** Combining wrap (i) (`fullcount = jointIsoCount + corr`), wrap (ii) (`fullcount_pair_closed`), and wrap (iii) (`chi_configDet_eq_chi_pairForm`): on the `corr = 0` locus (`hcorr`: not both config-differences isotropic), the… | — |
| `jointIsoCount_ne_of_chiSep_pair` | 415-467 | **The observable↔count bridge, per pair (ZMod p).** Two pivots whose pair invariant `χ(det G₂(u;t,t₀))` differs — both config invariants nonzero, corr term vanishing — have distinct joint isotropic counts `Z_u({t,t₀})`. Turns χ-separation into Z-separation. | — |
## ChainDescent/ObservableCountBridgeK.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `cone_count_zero_splitK` | 30-62 | **The `y=0` split (K)** — `fullcount = restricted (y≠0) + [∀ t∈S', Q(t−w)=0]`. | — |
| `fullcount_eq_jointIsoCountK_add_corr` | 67-74 | **B1a wrap (i) (K)** — `fullcount = jointIsoCountK + (y=0 correction)`. | — |
| `levelset_count_collapseK` | 79-156 | **B1a analytic core (K)** — the `|S|=2`, even-`d` `s`-sum collapse. | — |
| `fullcount_pair_eq_levelsetK` | 161-186 | **B1a wrap (ii-a) (K)** — fullcount over `{t,t₀}` = the homogeneous level-set count. | — |
| `fullcount_pair_closedK` | 187-212 | **B1a wrap (ii-b) (K)** — the fullcount closed form over `{t,t₀}`. | — |
| `configPolarDet_eq_pairFormK` | 217-227 | **The config polar-Gram det is the pair invariant `pairForm` (K).** | — |
| `chi_configDet_eq_chi_pairFormK` | 229-297 | **wrap (iii) (K) — `χ(D) = χ(I_w(t))`.** | — |
| `chi_eq_one_or_neg_oneK` | 299-312 | The quadratic character of a nonzero element is `±1` (K). | — |
| `jointIsoCountK_pair_closed_corr0` | 313-345 | **B1a final assembly (K) — the observable per-pair closed form (corr = 0).** | — |
| `jointIsoCountK_ne_of_chiSep_pair` | 346-381 | The abstract-`K` mirror of `jointIsoCount_ne_of_chiSep_pair`: χ-separation of the pair invariant ⟹ distinct joint isotropic counts `jointIsoCountK`. | — |
## ChainDescent/PairForm.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `quadChar_addChar_sum` | 67-102 | **The multiplicative↔additive Gauss bridge.** For the quadratic character `χ` of `K` composed into a char-zero domain `R'`, and any additive character `ψ : AddChar K R'`, `∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)` for every `a : K` (including `a = 0`, both sides `0`). | — |
| `pairCharSum_factor_gen` | 110-150 | **The "no Weil" core, GENERAL form — a product of two `χ`-of-functions factors into additive Gauss sums.** For ANY two functions `f g : V → K`, applying the bridge twice and reordering, `gaussSum χ ψ ^ 2 · (∑_t χ(f t)·χ(g t)) = ∑_y ∑_z χ(y)χ(z)·(∑_t ψ(y·f t + z·g t))`. The factoring never uses any… | — |
| `pairCharSum_factor` | 152-164 | The original form-specific factoring (the singleton model `S`), now a one-line corollary of the general lemma (`f = Q`, `g = Q(· − c)`). Kept for the singleton/translate instance; the live route uses `…_gen` with the pair invariant `f = det G₂(u; ·, t₀)`, `g = det G₂(u'; ·, t₀)`. | — |
| `pairForm` | 178-182 | **The pair invariant as a quadratic form.** `pairForm Q a` is the form `s ↦ 4·Q(a)·Q(s) − (polar Q s a)²`; its value at the shift `s = t − u` (anchor offset `a = t₀ − u`) is exactly the Gram determinant `det G₂(u; t, t₀)`. | Definition, `noncomputable` |
| `pairForm_apply` | 184-187 | Unfolds `pairForm Q a s = 4·Q a·Q s − polar Q s a · polar Q s a` (the `|S|`=2 config-Gram determinant, a quadratic in `s`). | — |
| `detG2_eq_pairForm` | 189-194 | The Gram determinant `det G₂(u; t, t₀) = 4 Q(t−u) Q(t₀−u) − B(t−u,t₀−u)²` equals `pairForm Q (t₀−u)` evaluated at the shift `t − u` — the structural identity that turns the opaque pair invariant into a quadratic-form-at-a-shift. | — |
| `pairCombine` | 196-215 | **The two-pivot combine.** The inner-sum integrand `y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀)` — two pair invariants at DIFFERENT pivots `u, v` — expressed in the single shift `p = t − u`: a quadratic FORM `y•pairForm_u + z•pairForm_v` applied to `p`, plus a LINEAR term `z·polar pairForm_v (p, u−v)` and… | — |
| `sum_addChar_quadForm_translate` | 217-223 | **Gauss-sum translation invariance.** `∑_t ψ(P (t − a)) = ∑_t ψ(P t)` for any quadratic form `P` (reindex `t ↦ t + a`). The final step of the inner-sum evaluation, recentring each pivot's shift. | — |
| `pairSum_to_shifted` | 225-260 | **The single-shift reduction of `M(y,z)` (increment 2, forward step — UNCONDITIONAL).** The inner sum `M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))` (written via `pairForm`) reduces, by `pairCombine` then recentring `t ↦ t−u`, to a CONSTANT phase times a sum of `ψ` of `F(s) + (linear in s)`… | — |
| `sum_addChar_shifted_eval` | 262-274 | **Complete the square (increment 2, forward step).** Once the linear term `L s` of the shifted sum is represented as `polar F s b` (possible exactly when `F` is nondegenerate — that representability is the separate next piece), the linear part is absorbed by a translate and `∑_s ψ(F s + L s) =…` | — |
| `pairSum_closed_of_repr` | 276-296 | **The `M(y,z)` closed form, modulo the representation `b` (increment 2 — ASSEMBLED).** Chains `pairSum_to_shifted` (reorganise) with `sum_addChar_shifted_eval` (complete the square): given a vector `b` representing the residual linear term against `F = y•pairForm_u + z•pairForm_v` (i.e. `hb`, which… | — |
| `exists_repr_of_nondeg` | 298-309 | **Representability from nondegeneracy (increment 2, piece (i)).** On a finite-dimensional space, if the polar bilinear form of `F` is nondegenerate then every linear functional `ℓ` is `polar F (·, b)` for some `b` — exactly the input `pairSum_closed_of_repr` needs. Via Mathlib's… | — |
| `pairSum_closed_of_nondeg` | 311-332 | **The `M(y,z)` closed form from nondegeneracy alone (increment 2, (i) discharged).** Combining `exists_repr_of_nondeg` with `pairSum_closed_of_repr`: when `F = y•pairForm_u + z•pairForm_v` has nondegenerate polar form, there is a `b` (the canonical representative of the residual linear term) with… | — |
| `pairSum_fully_closed` | 334-359 | **The fully explicit `M(y,z)` closed form (increment 2 — COMPLETE on the nondegenerate locus).** Chaining `pairSum_closed_of_nondeg` (absorb the linear term) with `sum_addChar_quadForm` (evaluate the quadratic Gauss sum) gives, for `F = y•pairForm_u + z•pairForm_v` nondegenerate, `M(y,z) =…` | — |
| `pairForm_polar_anchor` | 371-381 | **Every `pairForm Q a` is degenerate: `a` lies in its polar-radical, and `pairForm Q a (a) = 0`.** This is the structural source of the degenerate locus (it forces degeneracy on the axes `{y=0}∪{z=0}`). Verified by expanding `pairForm_apply` + the polar identities. | — |
| `pairForm_self_anchor` | 383-386 | `pairForm Q a a = 0` — the pair invariant vanishes on the diagonal (the anchor direction lies in its radical). | — |
| `sum_addChar_radical_vanish` | 388-424 | **Radical-vanishing (the degenerate-locus diagonal collapse).** If `r` lies in the polar-radical of `F` (`∀ s, polar F s r = 0`) with `F r = 0`, and the residual linear functional does not annihilate `r` (`L r ≠ 0`), then `∑_s ψ(F s + L s) = 0`. Proof: translating by `c•r` fixes `F` (constant on… | — |
| `norm_addChar_eq_one` | 436-447 | **`AddChar` values into `ℂ` are unit-modulus** (each `ψ c` is a `(card K)`-th root of unity). The phase factors of `M` therefore drop out of its magnitude. | — |
| `norm_gaussSum_sq` | 449-475 | **The quadratic Gauss sum has `|gaussSum| = √q`** (over `ℂ`): `‖gaussSum χ ψ‖² = card K`. Via Mathlib's `gaussSum_mul_gaussSum_pow_orderOf_sub_one` (`gaussSum² = χ(-1)·card` for the order-2 character `χ`) and `|χ(-1)| = 1`. | — |
| `norm_pairSum_le` | 477-498 | **`‖M(y,z)‖ ≤ ‖gaussSum‖^d` on the nondegenerate locus** (so `‖M‖² ≤ (card K)^d = q^d`). From the explicit `pairSum_fully_closed` value: the two `ψ`-phases have norm `1` (`norm_addChar_eq_one`), the `∏ χ(wᵢ)` factor has norm `≤ 1` (each `χ` value is `0, 1`, or `−1`), leaving `‖gaussSum‖^d`. | — |
| `norm_sq_sum_addChar_quadForm` | 507-591 | `‖∑ₓ ψ(Q x)‖² = (card V)·…` — the magnitude of the global quadratic Gauss sum (the `K` Gauss-factor). | — |
| `norm_sq_sum_addChar_quadForm_linear_le` | 593-675 | **The with-linear degenerate magnitude bound (3c — uniform over nondeg AND conic).** For ANY quadratic form `Q` and linear functional `L`, `‖∑_x ψ(Q x + L x)‖² ≤ qᵈ · |radical Q|`. (Exact: `S·conj S = qᵈ·∑_{h∈radical} ψ(−L h)`, bounded by the triangle inequality + `‖ψ‖ = 1`.) This is the magnitude… | — |
| `norm_sq_pairSum_le` | 677-700 | **The uniform `|M(y,z)|²` bound (3c — the magnitude consumed by the increment-3 `c₀` bound).** For the inner sum `M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))`, `‖M‖² ≤ qᵈ · |radical F|`, `F = y•pairForm_u + z•pairForm_v`. On the NONDEG locus `|radical F| = 1 ⟹ ‖M‖² ≤ qᵈ` (matches… | — |
| `zeroCount_sq_le` | 702-775 | **Zero-count bound (3d).** For a quadratic form `P` (possibly degenerate), the number of zeros `z = #{x : P x = 0}` satisfies `(z·q − qᵈ)² ≤ (q−1)²·qᵈ·|radical P|` (`qᵈ = card V`). From `count_eq_charsum` (`z·q = ∑_x ∑_t ψ(t·P x)`), peeling the `t = 0` term (`= qᵈ`), and bounding the rest by the… | — |
| `normT_le` | 777-815 | **The `|T|` bound (3e, step i — the load-bearing analytic step).** The per-pair character sum `T = ∑_t χ(det G₂(u;t,t₀))·χ(det G₂(v;t,t₀))` (over ℂ) satisfies `q·‖T‖ ≤ ∑_{y,z} ‖χ y‖·‖χ z‖·√(qᵈ·|radical F_{y,z}|)`, `F_{y,z} = y•pairForm_u + z•pairForm_v`. From the factoring `gaussSum²·T = ∑_{y,z}…` | — |
## ChainDescent/PencilTBound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `polarRad` | 38-48 | The polar-radical of a quadratic form `F`, bundled as a submodule: `{ h | ∀ x, polar F x h = 0 }`. (Right radical of `F.polarBilin`.) | Definition |
| `mem_polarRad` | 50-51 | Membership criterion for the polar-radical submodule `polarRad Q`. | `@[simp]` |
| `polarRad_card_filter` | 53-64 | The `Finset.filter` cardinality used in `normT_le`'s RHS equals `Nat.card` of `polarRad F`. Routed through `Nat.card`/`Set.ncard` (instance-free) to avoid `Fintype`-on-submodule instance mismatches. | — |
| `polarRad_ne_top_of_ne_zero` | 66-79 | **`F ≠ 0 ⟹ its polar-radical is a PROPER subspace** (char ≠ 2).** If the radical were everything, then `polar F x x = 0` for all `x`, i.e. `2 • F x = 0`, i.e.` | — |
| `radical_card_mul_card_le` | 81-96 | **The corank-uniform proper-subspace bound (the corank ≥ 2 enabler).** For any NONZERO quadratic form `F` on a finite space `V` over a finite field `K` (char ≠ 2), `|radical F| · |K| ≤ |V|` — equivalently `|radical F| ≤ q^{d-1}`, regardless of the corank. | — |
| `mvPoly_zeros_count_le` | 104-123 | **Schwartz–Zippel over a finite field (REUSABLE).** A nonzero two-variable polynomial over `K` has at most `totalDegree·(card K)` common zeros in `K²`. | — |
| `det_totalDegree_le` | 125-140 | **The pencil-discriminant degree bound.** The determinant of a `d × d` matrix whose every entry is a 2-variable polynomial of `totalDegree ≤ 1` (a *linear pencil* `y·A + z·B`) has `totalDegree ≤ d`. This caps the discriminant `disc(y,z) = det(y·G_u + z·G_v)` at degree `d`, the `p.totalDegree` fed… | — |
| `pencilDisc` | 141-147 | The **pencil discriminant** of two matrices `A, B` over `K`: the determinant of the linear-pencil matrix `y·A + z·B` packaged as a 2-variable polynomial `det(X₀·A + X₁·B) : MvPolynomial (Fin 2) K`. | Definition, `noncomputable` |
| `pencilDisc_totalDegree_le` | 148-158 | `pencilDisc A B` has `totalDegree ≤ d` (each entry is linear in `(X₀, X₁)`). | — |
| `pencilDisc_eval` | 159-166 | Evaluating `pencilDisc A B` at `(y, z)` recovers `det(y·A + z·B)`. | — |
| `polar_pencil` | 171-176 | Polar of the pencil form `y•P + z•R` is the linear combination of the polars. | — |
| `polarRad_eq_bot_iff_separatingRight` | 178-188 | The polar-radical is trivial ⟺ the polar bilinear form separates on the right. | — |
| `polarRad_ne_bot_iff_det_eq_zero` | 190-195 | **Degeneracy ⟺ vanishing determinant** (the bridge linchpin). For a basis `b`, the pencil member `G` is degenerate (`polarRad G ≠ ⊥`) iff the determinant of the Gram matrix of its polar form vanishes. | — |
| `toMatrix₂_polarBilin_pencil` | 197-207 | In matrix coordinates, the pencil `y•P + z•R`'s polar bilinear form is `y·(matrix of P.polarBilin) + z·(matrix of R.polarBilin)`. | — |
| `pencilZeros_count_le` | 211-225 | The Schwartz–Zippel count over `K × K` (via the `(y,z) ↦ ![y,z]` bijection). | — |
| `degenerate_count_le` | 227-259 | **The good-anchor degenerate-pencil count.** Given a good anchor, the number of degenerate pencil ratios `(y,z)` is `≤ d·(card K)` (Schwartz–Zippel on the pencil discriminant). | — |
| `sum_two_bucket_le` | 267-286 | **Two-bucket sum bound.** Split `s` by predicate `p`; if `g ≤ Ma` on the `¬p` bucket and `g ≤ Mb` on the `p` bucket, with cardinalities `≤ Ca`, `≤ Cb` respectively (and `Ma, Mb ≥ 0`), then `∑_{i∈s} g i ≤ Ca·Ma + Cb·Mb`. | — |
| `sqrt_mul_le_div` | 288-296 | **Deg-bucket magnitude.** If `r·k ≤ V` (the proper-subspace radical bound), then `√(V·r) ≤ V/√k`. Used with `r = |radical F_{y,z}|`, `k = |K|`, `V = card V`: a degenerate member contributes at most `card V / √|K|`. | — |
| `c0_le` | 298-334 | **The final c₀ bound (3e-iii finish).** From the counting bound `2·NS ≤ 2·z_u + n + T` (`card_agree_le`), the `|T|` bound `T ≤ q·√n + d·n/√q` (`normT_bucket_bound`, ÷q), and the zero-count `z_u·q ≤ n + (q−1)·n/√q` (`zeroCount_sq_le` with the proper-subspace radical bound), under the threshold… | — |
| `norm_quadraticChar` | 342-356 | The quadratic character composed into `ℂ` has norm `0` at `0` and `1` elsewhere. | — |
| `normT_bucket_bound` | 364-450 | **The `‖T‖` magnitude bound.** Bucket-splitting the character sum into nondegenerate and degenerate pencil members gives `(card K)·‖T‖ ≤ q²√n + (d·q)(n/√q)`. | — |
## ChainDescent/PerAnchorBound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|

| `int_char_pointwise` | 25-30 | Per-element χ-value inequality (the heart of the counting identity). For `ca, cb ∈ {-1,0,1}`: `2·[ca=cb] ≤ 2·[ca=0] + 1 + ca·cb`. | — |
| `counting_identity` | 32-56 | **The c₀ counting identity.** `2·#{t : χ(a t) = χ(b t)} ≤ 2·#{t : a t = 0} + |V| + ∑_t χ(a t)·χ(b t)`, for the quadratic character `χ = quadraticChar K`. (`a, b = I_u, I_v`.) | — |
| `charSum_int_le_norm` | 64-76 | The integer character sum is `≤` the norm of the complex character sum (`T_ℤ ≤ |T_ℤ| = ‖T_ℂ‖`). | — |
| `card_agree_le` | 78-94 | **The count controlled by the magnitude.** `2·#{χ(a)=χ(b)} ≤ 2·#{a=0} + |V| + ‖T_ℂ‖` over ℝ, combining `counting_identity` with `charSum_int_le_norm`. | — |
| `c0_le_threequarters` | 102-182 | **The per-anchor non-separation bound (increment 3).** For a good anchor with `q≥q₀`, `d≥3`, the fraction of probes failing to separate a pivot pair is `NS ≤ ¾·(card V) < 1` — assembled from the counting identity, the `‖T‖` magnitude bound, and the radical zero-count. | — |
## ChainDescent/ProfileReduction.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `jointIsoCount` | 27-36 | **The joint isotropic count `Z_u(S)`** = `#{z ≠ u : z isotropic-to-u, and isotropic-to-every t ∈ S}`, where "isotropic" is `isoClass ≠ 2` (the dictionary: `isoClass w = 2 ⟺ Q w ≠ 0`). This is the joint-incidence content the crux reduces to (the `VO⁻₄(3)` `sigF` counts at `|S| = 2`). | Definition, `noncomputable` |
| `ZProfileSeparates` | 37-45 | **The reduced crux predicate.** Agreeing joint isotropic counts `Z(S)` over every sub-frame `S ⊆ T` ⟹ the same `Q`-profile over the standard frame (the `QProfileSeparatesAtBase` conclusion). This is the genuine open content (D3): the joint `Z(S)`-profile separates `u`. | Definition, `noncomputable` |
| `extProfile` | 47-50 | Extend a `T`-indexed isotropy profile to a full profile (junk `0` off `T`). | Definition, `noncomputable` |
| `extProfile_mem` | 52-55 | On `t ∈ T`, the extended isotropy profile `extProfile σ` agrees with `σ`. | — |
| `qProfileSeparatesAtBase_of_zProfileSeparates` | 56-138 | **D1 — the marginalisation reduction.** The `QProfileSeparatesAtBase` fine antecedent ⟹ the `Z(S)` antecedent, so `ZProfileSeparates` (the joint-incidence crux) discharges `QProfileSeparatesAtBase`. Proof: fiber `Z_w(S)` by each point's `(T`-profile`, pivot-class)`; "good" fibers (`c ≠ 2`, profile… | — |
| `isotropySeparates_of_zProfileSeparates` | 140-149 | **The D1 chain, end-to-end.** `ZProfileSeparates` + nondegeneracy ⟹ `IsotropySeparatesAtBase` (the wittFree capstone's target) — composes D1 with the landed `isotropySeparates_of_qProfileSeparates`. So the *entire* open content of the generalization is now the single predicate `ZProfileSeparates Q…` | — |
| `jointIsoCount_eq_restricted` | 150-190 | **D2 (bridge) — `Z_u(S)` as the restricted isotropic count over `V`.** Unfolding the dictionary (`isoClass ≠ 2 ⟺ Q = 0`), transporting `Fin (p^d) ↔ V` (`count_transport`), and shifting `w = x − ū`, the joint isotropic count is the Lemma-A-ready restricted count: nonzero `w` on the cone `Q w = 0`… | — |
| `coarse_incidence_agree` | 200-277 | **B-M1 core — isotropic-incidence agreement from the fine isotropy-count antecedent.** | — |
| `incidence_to_V` | 278-313 | **B-M1, transport+translate — the incidence count moves to `V` in Lemma-A coordinates.** The cone-incidence count over `Fin (p^d)` (basepoint `w`) equals the count over `V` of `y ≠ 0` with `Q y = 0` and `Q (y − aₜ) = 0` for the config differences `aₜ = t̄ − w̄`. One bijection `z ↦ affineE.symm z −…` | — |
| `incidence_agree_V` | 314-337 | **B-M1 capstone — the incidence counts agree in `V` (Lemma-A coordinates).** Composing the fiberwise agreement (`coarse_incidence_agree`) with the transport/translate (`incidence_to_V`): from the fine isotropy-count antecedent, the `V`-side incidence count `#{y ≠ 0 : Q y = 0 ∧ ∀ t∈S', Q (y −…` | — |
| `cone_count_zero_split` | 338-374 | **B-M2 bridge — the `y=0` correction.** Lemma A's full cone-count equals B-M1's `y≠0` (restricted) count plus the `y=0` term, which is present iff all config differences `aₜ = t̄−w̄` are isotropic (`∀ t∈S', Q aₜ = 0`) — a Gram-determined indicator. Connects `incidence_agree_V` (restricted) to the… | — |
| `fullcount_agree_modulo_corr` | 375-399 | **B-M2 bridge capstone — the FULL Lemma-A-shaped counts agree modulo the Gram-determined `y=0` correction.** From the fine isotropy-count antecedent: `fullcount_u(S') + corr_{u'} = fullcount_{u'}(S') + corr_u`, where `fullcount_w(S') = #{y : Q y=0 ∧ ∀t∈S', Q(y−(t̄−w̄))=0}` (Lemma A's count, `aₜ =…` | — |

## ChainDescent/ScratchSimilitudeCap.lean

**Viability spike (2026-06-29), NOT in `build.sh`** — the "similitude cap" closing the last in-architecture-poly lead.
Formalizes that the affine-polar graph determines `Q` only up to scaling (a similitude), so refinement is provably
capped at the **square class**: `χ(det G₂)` is a graph invariant, but the exact form value (and the singleton square
class) is not. Verdict consequence: the `χ(det G₂)` refinement route is provably quasipoly, not poly — the dividing
line for poly is *coloring vs group* (Route C / `CellsAreOrbits`), not square-class vs field-value. Axiom-clean
`[propext, Classical.choice, Quot.sound]`, builds on `PairForm`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|

## ChainDescent/ScratchOrbitBaseCase.lean

**CellsAreOrbits route, increment 1 + 2 (2026-06-29), NOT in `build.sh`.** The base case of the `CellsAreOrbits`
induction (the open core of the forms-graph poly route) + the multiplier-rigidity delimiter + the free-prefix orbit
coarsening. Models affine-polar automorphisms as `Similitude Q` (`g : V ≃ₗ V`, `μ ≠ 0`, `Q∘g = μ·Q`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, pure geometry (no `Fintype`). Builds on `PairForm`. See
`docs/chain-descent-cellsareorbits-route.md`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|

## ChainDescent/ScratchWittCone.lean

**Witt build, stages W0 + W1 (2026-06-29), NOT in `build.sh`.** Discharges the `WittConeTransitive` input of
`ScratchOrbitBaseCase` down to a concrete residual. W0 = the orthogonal-reflection engine; W1 = cone-transitivity
reduced to `IsotropicPairing`. Axiom-clean `[propext, Classical.choice, Quot.sound]`. Imports `ScratchOrbitBaseCase`
(for `Similitude`/`WittConeTransitive`) + `Mathlib.LinearAlgebra.Reflection`. See `docs/chain-descent-cellsareorbits-route.md` §7.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `refl` | 41-43 | The orthogonal reflection `τ_v : y ↦ y − (polar Q y v / Q v) • v` as a linear equiv (via `Module.reflection`). | Definition, `noncomputable` |
| `exists_hyperbolic_partner` | 100-116 | **The partner lemma** — a nonzero isotropic vector has an isotropic partner `f` with `polar Q u f = 1` (from nondegeneracy `hnd`). The key tool for the residual. | — |

## ChainDescent/ScratchNodeCountBridge.lean

**Increment 0 — the node-count bridge + transport seam (2026-06-29), NOT in `build.sh`.** The CellsAreOrbits route's
poly *payoff* mechanism: the single-path disposition delivers the two poly ingredients (bounded node count + every
consumed cell one residual orbit), plus the **transport seam** (representative-choice invariance of the leaf canonical).
Grounding finding — most ingredients were already landed (node-count `≤ n`, prune soundness, per-node firing,
direction-invariance); this module adds prune *completeness*, the depth-1 rep-transport `repTransport`, the general
`baseTransport` (iterate), and the `canonAdj`-lift atom `labelledAdj_rankPerm_transport`. Keyed on the *weaker*
`SelectedCellIsOrbit`, discharged by full `CellsAreOrbits`. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
Imports `ChainDescent.Cascade`. Remaining seam gap = `samePartition`→literal relabel = `canonForm` (§15.7 placeholder).
See `docs/chain-descent-cellsareorbits-route.md` §6.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SelectedCellIsOrbit` | 37-47 | **0a** — `CellsAreOrbits` restricted to `sel`'s targeted cell: same-coloured vertices of the *consumed* cell are `Stab(S)`-orbit-equivalent. Strictly weaker than full `CellsAreOrbits`; matches the scheduler. | Definition |
| `selectedCellIsOrbit_of_cellsAreOrbits` | 59-65 | **0b** — full `CellsAreOrbits S ⟹ SelectedCellIsOrbit`. The §4 forms-graph math (modulo Witt + the wall) discharges the bridge hypothesis for free. | — |
| `selectedCell_single_stabOrbit` | 69-80 | **0c — prune completeness (the missing pillar).** Under `SelectedCellIsOrbit`, two same-cell vertices lie in one `StabilizerAt`-orbit (the consumed cell is *one* orbit ⟹ one sibling-class). The direction prune *soundness* (`covered_sound`) does not give. Via `mem_orbit_stabilizerAt_iff`. | — |
| `selectedCell_prune_sound_complete` | 82-90 | The two reps are *mutually* `OrbitPartition` — dropping either is sound (isomorphic) and complete (no class lost). Turns "fork over reps" into "descend on one". | — |
| `spine_node_count_le` | 94-102 | **Node count `≤ n`** — re-export of the landed `defaultSpineChain_reaches_leaf` (single path reaches a discrete leaf in `≤ n` levels). Step (3) is free — NOT `exists_potential_descent` (that bounds *base size*, the quasipoly engine). | — |
| `SinglePathDisposition` | 106-111 | The bridge-keyed hypothesis: `∀ S, SelectedCellIsOrbit … S` (every consumed cell one orbit). Structural form of the empirical `Phase2Nodes = 0`. Weaker than `∀ S, CellsAreOrbits`. | Definition |
| `singlePathDisposition_of_cellsAreOrbits` | 113-117 | The forms-graph math (full `CellsAreOrbits` at every base) discharges the disposition. | — |
| `CertifiedSinglePath` | 119-131 | The two poly ingredients bundled: `boundedNodes` (`≤ n`) + `cellsCertified` (every consumed cell one residual orbit). The structural object the **meta** poly-argument reads "poly time" off. | Structure |
| `certifiedSinglePath_of_disposition` | 133-145 | **★ The bridge capstone (Increment 0).** `SinglePathDisposition ⟹ CertifiedSinglePath` — both poly ingredients discharged from the disposition. | — |
| `NodeCountBridge.certifiedSinglePath_of_cellsAreOrbits` | 147-157 | **Recovery route angle (b).** Full `CellsAreOrbits` at every base discharges the single-path disposition, hence the certified single path — the composition taken when routing through the forms-graph `CellsAreOrbits` scaffold rather than proving `SelectedCellIsOrbit` directly. | — |
| `warmRefine_congr_samePartition` | 183-190 | `warmRefine` is a `samePartition` congruence in its seed (the `D=∅` case of `warmRefine_agree_off'`). The engine that passes representative-transport through warm refinement. | — |
| `mem_insert_transport` | 187-201 | An `S`-fixing aut `g` with `g v₁=v₂` carries `insert v₁ S` onto `insert v₂ S`: `g i ∈ insert v₂ S ↔ i ∈ insert v₁ S`. | — |
| `indiv_samePartition_transport` | 203-221 | **Seed transport.** The `v₁`-individualized seed and the `g`-pullback of the `v₂`-individualized seed induce the same partition (both singletons-on-pinned-set; `g` matches the pinned sets). Literal index-labels differ, partition does not. | — |
| `repTransport` | 223-240 | **★ The representative-transport core (depth 1).** An orbit aut `g ∈ Stab(S)` carrying rep `v₁ ↦ v₂` makes the `v₂`-individualized descent (pulled back by `g`) `samePartition` the `v₁`-descent — rep-choice invariance, the transport seam's load-bearing equivariance. Via cross-config `warmRefine_transport` + the congruence. | — |
| `repTransport_of_orbitPartition` | 242-252 | `repTransport` with `g` supplied by `OrbitPartition adj P S v₁ v₂` (what `selectedCell_single_stabOrbit` yields). Two reps of a certified single-orbit cell give `g`-relabeled descents. | — |
| `mem_image_transport` | 268-274 | Membership transport, general base: `g i ∈ T.image g ↔ i ∈ T` (injectivity of `g`). | — |
| `indiv_samePartition_image` | 276-290 | Seed transport, general base: the `T`-individualized seed and the `g`-pullback of the `g(T)`-individualized seed induce the same partition. General form of `indiv_samePartition_transport`. | — |
| `baseTransport` | 287-300 | **★ Full-base `g`-equivariance (the "iterate across levels" lemma).** For any aut `g` and base `T`, the descent at `g(T)` (pulled back by `g`) is `samePartition` the descent at `T`. `g` global ⟹ holds at every base incl. a leaf ⟹ subsumes level-by-level iteration in one lemma. | — |
| `repTransport_eq_baseTransport_instance` | 302-314 | `(insert v₁ S).image g = insert v₂ S` for `g` fixing `S` with `g v₁=v₂` — confirms `repTransport` is the `S`-fixing instance of `baseTransport`. | — |
| `labelledAdj_rankPerm_transport` | 332-351 | **The `canonAdj`-lift atom.** Labelled output `labelledAdj (rankPerm π) adj` is invariant under a `g`-relabel of the discrete leaf colouring (`g` an aut), via `rankPerm_comp` + `labelledAdj_eq_of_isAut`. Remaining lift gap = `samePartition`→literal relabel = `canonForm` (§15.7 placeholder). | — |

## ChainDescent/ScratchWallKernel.lean

**Increment 3a — the wall isolated as one predicate (2026-06-29), NOT in `build.sh`.** `CellsAreOrbits` in the
anisotropic regime (the "wall") reduced to a single open predicate `WallKernel` (square-class profile *determines*
exact Gram), with everything else proved. Geometric `Similitude`/orbit setting (extends `ScratchOrbitBaseCase`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`. Imports `ChainDescent.ScratchOrbitBaseCase`. `WallKernel` = the
exact-Gram form of the seal's `ZProfileSeparates`; the character-inversion attack = 3c. See
`docs/chain-descent-cellsareorbits-route.md` §6 Increment 3.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
## ChainDescent/ScratchBoundedBranching.lean

**Phase 1 — the bounded-branching node-count bridge `leaves ≤ Bᴸ` (recovery route T0, 2026-06-30), NOT in `build.sh`.**
Generalizes the single-path `ScratchNodeCountBridge` (`B = 1`) to the C# default mode (branch-but-resolve). §1 is the
pure tree-combinatorics core (`BTree` + `leaves_le_pow : BoundedDeg B t → leaves t ≤ B ^ branchDepth t`, the `D3` math,
forms-graph-free); §2 the disposition (`SelectedCellOrbitsLE`/`BoundedBranchingDisposition`, cell covered by `≤ B` orbits);
§3 the capstone (`CertifiedBoundedTree` + `leafBound : leaves ≤ Bᴸ` + `certifiedBoundedTree_of_disposition`), with the
`B = 1` single-path corner recovered. Carried `degBound`/`depthBound` = the Increment-1 realisation seam (concrete branching
descent ↔ orbit tree, Phase 4). Axiom-clean `[propext, Classical.choice, Quot.sound]`. See
`docs/chain-descent-recovery-route.md` §6/§8.

| Name | Line | Description | Notes |
|------|------|-------------|-------|

## ChainDescent/ScratchBranchingBound.lean

**Phase 2 — the a-priori branching bound `bᵢ ≤ |K|^{|S|+1}` (recovery route T0, forms graph, 2026-07-01), NOT in `build.sh`.**
Discharges the Phase-1 bridge's `degBound` at the **quasipoly** tier: reusing the demoted route's geometric model
(`ScratchOrbitBaseCase`/`ScratchWallKernel`: `Similitude`/`StabOrbit`/`SameExactGram` + soundness + carried Witt), the
branching factor `#{Stab(S)-orbits}` **injects into exact-Gram profiles** (`gramProfile`), giving the unconditional
`stabOrbit_cover_card_le : #{Stab(S)-orbits} ≤ |K|^{|S|+1}` (`card_gramProfiles_le` counts the profiles). So the recovery
bridge re-derives the banked quasipoly unconditionally (mod Witt); the polynomial target is the strictly sharper "the cell
cuts `|K|^{|S|}` profiles to `poly(q)`" (the WL-orbit-defect crux). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
See `docs/chain-descent-recovery-route.md` §6/§8.

| Name | Line | Description | Notes |
|------|------|-------------|-------|

## ChainDescent/ScratchWLVisibility.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `WLVis.product_coord_regular` | 32-48 | **Blindness heart.** Fixing the first coordinate of the product relation `a·y·z = 1` to any `a` leaves exactly `|G|` completing pairs, independent of `a` and of whether `G` is abelian — the perfect-quasigroup property that makes the standard CFI/multipede gadget 1-WL-blind to group structure. | — |
| `WLVis.product_coord_regular_indep` | 50-55 | The fix-one completion count on the product gadget is the same for all fixed values `a, a'` — the interchangeability of segment values that 1-WL blindness literally needs. | — |
| `WLVis.linear_eq_unique` | 75-88 | **Degree-2 blindness kernel.** The solution set of `u·z·w = 1` is a singleton, so every fix-two completion count on the minimal `d=3` product gadget is `1`, independent of the fixed values and of `G` — the `Γ`-blindness a 2-WL pair-refinement sees. | — |
| `WLVis.product_fix_two_indep` | 90-97 | Fix-two completion counts on the minimal `d=3` product gadget agree across all coordinate pairs and fixed values (each `= 1`); the degree-2 analogue of `product_coord_regular_indep`. | — |
| `WLVis.commDeg` | 101-105 | The commuting-degree `|C(g)|` of a group element — the 1-WL degree of `g`'s value-vertex in a commuting-pairs gadget (`noncomputable`). | Definition, `noncomputable` |
| `WLVis.commDeg_const_of_comm` | 107-111 | **Visibility heart (abelian side).** On an abelian group the commuting-degree is constant `= |G|`, so the commuting-pairs gadget is also 1-WL-blind there. | — |
| `WLVis.commDeg_nonconst_of_noncomm` | 113-127 | **Visibility heart (non-abelian side).** On a non-abelian group some element commutes with strictly fewer elements than `1` does, so colour refinement splits the segment by centralizer size — non-abelian structure is 1-WL-visible through a commuting-pairs gadget. | — |
| `WLVis.commDeg_const_iff_comm` | 129-150 | The dichotomy in one statement: the commuting-degree is constant iff the group is abelian — the commuting-pairs gadget is 1-WL-blind exactly on abelian groups and visible exactly on non-abelian ones. | — |

## ChainDescent/WLGeneric.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `WLGeneric.Colouring` | 35-36 | A colouring assigns each vertex a natural-number colour (`V → Nat`). | Definition |
| `WLGeneric.GAdj` | 38-40 | Labelled graph on an arbitrary finite vertex type `V` — the `V`-generic analogue of `AdjMatrix n`'s `adj` field. | `abbrev` |
| `WLGeneric.GPOE` | 42-44 | Partial-order matrix on `V` (`V → V → POE`), the generic analogue of `PMatrix n`; pass the constant `POE.unknown` for a plain graph. | `abbrev` |
| `WLGeneric.signature` | 48-53 | The 1-WL signature of a vertex `v`: the multiset of `(neighbour-colour, adjacency-value, P-relation)` tuples over all `u ≠ v`. This is the object whose `Γ`-(in)dependence drives the rigid-Cameron rungs. | Definition |
| `WLGeneric.sigKey` | 68-71 | The canonical refinement key of `v` — old colour prepended to its sorted encoded signature multiset — so that two vertices share a key iff same old colour and same signature. | Definition |
| `WLGeneric.sigKey_eq_iff` | 73-86 | Equal `sigKey`s ⟺ same old colour and same `signature`; the injectivity backing the refinement key. | — |
| `WLGeneric.refineStep` | 90-93 | One round of 1-WL refinement over `V`: recolour each vertex by the encoded canonical `sigKey`. | Definition |
| `WLGeneric.refineStep_iff` | 95-104 | **The splitting lever.** Two vertices get the same refined colour iff they had the same old colour AND the same `signature` — equal signatures ⟹ no split (hideability), unequal ⟹ split (visibility). | — |
| `WLGeneric.warmRefine` | 106-110 | Warm refinement: iterate `refineStep` `Fintype.card V` times (enough rounds since each non-fixpoint round strictly refines). | Definition |
| `WLGeneric.samePartition` | 114-116 | Two colourings induce the same partition iff their equivalence classes coincide. | Definition |
| `WLGeneric.samePartition.refl` | 122 | `samePartition` is reflexive. | — |
| `WLGeneric.samePartition.symm` | 124-125 | `samePartition` is symmetric. | — |
| `WLGeneric.samePartition.trans` | 127-129 | `samePartition` is transitive. | — |
## ChainDescent/ScratchWLWiring.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
## ChainDescent/Nullstellensatz.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Nullstellensatz.quad_lin_combo` | 73-79 | Two-vector expansion `Q(c•x + d•y) = c²·Qx + d²·Qy + c·d·polar Q x y`; the algebraic identity underlying every line-restriction argument. | — |
| `Nullstellensatz.nullstellensatz_core` | 81-96 | **Line-restriction core (ring-general).** On the line through an isotropic non-tangent point, a form `R` vanishing on the `Q`-cone obeys the local ratio identity — the shared per-line engine of both Nullstellensatz routes. | — |
| `Nullstellensatz.nullstellensatz_pointwise` | 103-113 | Field version of `nullstellensatz_core`: cancels the nonzero factor `polar Q x y` to give the pointwise ratio identity `Q y · polar R x y = R y · polar Q x y`. | — |
| `Nullstellensatz.form_eq_of_polar_eq_smul` | 115-125 | **The char ≠ 2 finish.** `polar R = μ · polar Q ⟹ R = μ · Q` — a quadratic form is determined by its polar form in characteristic ≠ 2. | — |
| `Nullstellensatz.ratio_step` | 127-143 | Ratio-preservation step: one isotropic non-tangent move preserves `R/Q`, straight from `nullstellensatz_core` (no structural input). | — |
| `Nullstellensatz.ratioEdge` | 145-150 | The isotropic-edge relation on anisotropic vectors: `b` is one non-tangent isotropic step from `a` — the walk relation of the connectivity route. | Definition |
| `Nullstellensatz.ratio_step_edge` | 152-158 | One `ratioEdge` step preserves the ratio: `R a · Q b = R b · Q a` (repackages `ratio_step`). | — |
| `Nullstellensatz.ratioEdge_symm` | 160-179 | The isotropic-edge relation is symmetric on anisotropic vectors. | — |
| `Nullstellensatz.ratioEdge_smul` | 181-189 | Edge along an isotropic direction: rescaling an isotropic non-tangent generator by `t ≠ 0` stays one `ratioEdge` step. | — |
| `Nullstellensatz.ratioEdge_line` | 191-204 | Two anisotropic points on a common isotropic line are one `ratioEdge` apart. | — |
| `Nullstellensatz.ratio_const_of_reflTransGen` | 206-217 | Ratio constancy along a walk: the reflexive-transitive closure of `ratioEdge` preserves `R/Q`. | — |
| `Nullstellensatz.reflTransGen_ratioEdge_symm` | 219-229 | Walks reverse — the `ratioEdge` closure is symmetric on anisotropic vertices reachable from an anisotropic start. | — |
| `Nullstellensatz.hconn_of_hub` | 231-237 | Hub reduction: if every anisotropic vector is `ratioEdge`-reachable from a single hub, the connectivity hypothesis `hconn` holds. | — |
| `Nullstellensatz.nullstellensatz_of_connectivity` | 239-266 | **Alternative (spare) route.** Reduces the quadric Nullstellensatz to `hconn` (isotropic-edge connectivity of anisotropic vectors) instead of hspan+hlink — hspan-free but needs the walk hypothesis; the structural route is the one wired into Route C. | — |
| `Nullstellensatz.nullstellensatz_of_structural` | 277-343 | **Key theorem.** Reduces the quadric Nullstellensatz (nondeg `Q` determined up to scalar by its cone) to two purely-geometric facts — `hspan` (punctured cone spans) and `hlink` (anisotropic polar-diameter ≤ 2); field-general, no finiteness. | — |

## ChainDescent/NullstellensatzCount.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Nullstellensatz.radical_card_one` | 70-83 | The radical of a nondegenerate `Q` is trivial (the `zeroCount_sq_le` radical filter has card 1). | — |
| `Nullstellensatz.cone_card_lower` | 85-110 | **Support backbone.** Lower bound on the isotropic-cone size `|V| − (q−1)√|V| ≤ |cone|·q`, from `zeroCount_sq_le` with trivial radical. | — |
| `Nullstellensatz.card_zeros_odd` | 111-152 | **Support backbone.** A nondegenerate quadric in ODD dimension has exactly `|V|/q` zeros (`|{Q=0}|·q = |V|`); the Gauss error term vanishes as `∑_{t≠0} χ(t) = 0`. | — |
| `Nullstellensatz.sec_aniso` | 153-234 | For anisotropic `u`, the tangent section `{x | Q x = 0 ∧ polar Q u x = 0}` has exactly `|V|/q²` points — `u^⊥` is odd-dimensional so `card_zeros_odd` gives the exact count. | — |
| `Nullstellensatz.cone_not_covered` | 235-310 | The isotropic cone is not covered by two ANISOTROPIC hyperplanes `u₁^⊥ ∪ u₂^⊥` (`q ≥ 3`, even `finrank ≥ 4`); exact `q^{d−2}` sections give a tail-free union bound. | — |
| `Nullstellensatz.section_iso_count` | 312-440 | **Counting crux.** Exact isotropic-`u` hyperplane section identity `section·q² + (q−1)·|V| = |cone|·q²` (type-independent, holds at `q=3`) via a two-constraint character sum. | — |
| `Nullstellensatz.cone_not_covered_gen` | 441-509 | The isotropic cone is not covered by `y^⊥ ∪ u^⊥` for anisotropic `y` and ANY nonzero `u` (isotropic case via union bound over `sec_aniso` + `section_iso_count`); the general form `hspan` needs. | — |
| `Nullstellensatz.cone_punctured_span` | 510-537 | `hspan`: for anisotropic `y` the punctured isotropic cone `{x | Q x = 0 ∧ polar Q x y ≠ 0}` spans `V` (its polar-orthogonal complement is `⊥` by `cone_not_covered_gen` + nondegeneracy). | — |

## ChainDescent/NullstellensatzHlink.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Nullstellensatz.cone_card_upper` | 10-31 | Upper mirror of `cone_card_lower`: `|cone|·q ≤ |V| + (q−1)·√|V|` (Gauss error-term bound on the isotropic-cone size). | — |
| `Nullstellensatz.hyperplane_card` | 33-49 | A nonzero linear functional `f : V → K` has kernel of size `|V|/q`: `|{f = 0}|·|K| = |V|`. | — |
| `Nullstellensatz.aniso_polar_diameter_two` | 50-194 | `hlink`: any two anisotropic vectors are polar-joined through one anisotropic `z` (`∃ z, Q z ≠ 0 ∧ polar Q y z ≠ 0 ∧ polar Q z y' ≠ 0`); a `q=3`-tight union-bound count using `cone_card_upper` and the exact section saving. | — |
| `Nullstellensatz.nondegQuadric_determines_of_even` | 195-211 | **Key theorem — Nullstellensatz discharged (general finite field).** For odd char and even `finrank ≥ 4`, a nondegenerate `Q` is determined up to a `Kˣ` scalar by its isotropic cone; feeds `nullstellensatz_of_structural` with `cone_punctured_span` + `aniso_polar_diameter_two`, primitive ℂ-char built internally. | — |
| `Nullstellensatz.nondegQuadric_zmod_of_even` | 213-242 | **Key theorem — the `ZMod p` discharge.** For odd prime `p` and even `4 ≤ d`, proves exactly `NondegQuadricDeterminesForm p d`; removes the last carried Nullstellensatz citation from Route C. | — |

## ChainDescent/NullstellensatzStructural.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Nullstellensatz.binary_represents` | 39-61 | **Support backbone.** Over a finite field of odd order, a nondegenerate binary form `A x² + B y²` represents every target `c` (Cauchy–Davenport / pigeonhole on `q` values). | — |
| `Nullstellensatz.weightedSumSquares_isotropic` | 62-100 | A unit-weighted sum of squares in `dim ≥ 3` over a finite field of odd order is isotropic (has a nontrivial zero); the base case for isotropic existence. | — |
| `Nullstellensatz.separatingLeft_associated_of_polarBilin_nondeg` | 102-116 | Bridge (char ≠ 2): `polarBilin Q` nondegenerate ⟹ the associated symmetric bilinear form is separating-left — connects the project's nondegeneracy to Mathlib's form API. | — |
| `Nullstellensatz.exists_isotropic_of_nondegenerate` | 117-135 | **Bedrock.** A nondegenerate `Q` in `dim ≥ 3` over a finite field of odd order has a nonzero isotropic vector (diagonalize + `weightedSumSquares_isotropic`). | — |
| `Nullstellensatz.exists_hyperbolic_partner` | 137-159 | For a nonzero isotropic `v` under nondegenerate `Q`, there is a hyperbolic partner `f` (`polar Q v f = 1`) — the hyperbolic-pair building block. | — |
| `Nullstellensatz.isotropic_span` | 161-195 | Isotropic vectors span `V` (`dim ≥ 3`, nondegenerate, finite field of odd order), via one hyperbolic pair; the ambient-span fact behind `cone_punctured_span`. | — |
## ChainDescent/CanonForm.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CanonSound.canonForm_isLabelledAdj` | 25-36 | — | — |
| `CanonSound.leafLevel` | 40-45 | — | Definition, `noncomputable` |
| `CanonSound.leafLevel_isLeaf` | 47-52 | — | — |
| `CanonSound.canonForm?` | 54-66 | — | Definition, `noncomputable` |
| `CanonSound.canonForm?_sound` | 68-88 | — | — |
| `CanonSound.defaultP₀` | 98-100 | — | Definition |
| `CanonSound.defaultP₀_antisym` | 102 | — | — |
| `CanonSound.defaultχι₀` | 104-106 | — | Definition |
| `CanonSound.nonDiscreteSel` | 108-115 | — | Definition |
| `CanonSound.nonDiscreteSel_targets` | 117-119 | — | — |
| `CanonSound.nonDiscreteSel_nonempty` | 121-129 | — | — |
| `CanonSound.canonFormOf` | 131-135 | — | Definition, `noncomputable` |
| `CanonSound.canonFormOf_sound` | 137-143 | — | — |
| `CanonSound.canonFormOf_isSome` | 145-147 | — | — |
| `CanonForm.descent` | 166-170 | — | Definition |
| `CanonForm.descentResult` | 172-174 | — | Definition |
| `CanonForm.descentCost` | 176-177 | — | Definition |
| `CanonForm.descentCost_le` | 179-184 | — | — |
| `CanonForm.canonForm?` | 188-194 | — | Definition, `noncomputable` |
| `CanonForm.canonForm?_sound` | 196-205 | — | — |
| `CanonForm.canonForm?_eq_none_iff` | 207-223 | — | — |

## ChainDescent/Confinement.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `NodeCountBridge.indivχ` | 49-55 | — | Definition |
| `NodeCountBridge.warmRefine_congr_samePartition` | 178-185 | — | — |
| `NodeCountBridge.mem_image_transport` | 263-269 | — | — |
| `NodeCountBridge.indiv_samePartition_image` | 271-285 | — | — |
| `ConfinementP1.log_two_le_baseMax` | 367-374 | — | — |
| `ConfinementP1.greedy_base_card_le_baseMax` | 376-388 | — | — |
| `ConfinementP1.not_flagsAt_of_smallAut_spine` | 390-405 | — | — |
| `ConfinementP1.spineResidualCard` | 419-425 | — | Definition, `noncomputable` |
| `ConfinementP1.spineBaseAt` | 427-438 | — | Definition, `noncomputable` |
| `ConfinementP1.spineBaseAt_le_log` | 440-453 | — | — |
| `ConfinementP4.SelectedCellSubsetOrbit` | 467-478 | — | Definition |
| `ConfinementP4.selectedCellIsOrbit_of_subsetOrbit` | 480-490 | — | — |
| `ConfinementP4.selectedCellSubsetOrbit_of_orbit_cover` | 501-516 | — | — |
| `ConfinementP4.selectedCellSubsetOrbit_of_pretransitive` | 518-529 | — | — |
| `ConfinementP4.SelectedCellSubsetOrbitAt` | 538-543 | — | Definition |
| `ConfinementP4.selectedCellSubsetOrbitAt_of_cover` | 545-558 | — | — |
| `ConfinementP4.FrameSelectorTransitive` | 578-587 | — | Definition |
| `ConfinementP4.selectedCellSubsetOrbitAt_of_frameSelectorTransitive` | 589-599 | — | — |
| `Confinement.flag_imp_large` | 625-637 | — | — |
| `Confinement.confinement_selectedCellIsOrbit` | 644-669 | — | — |
| `Confinement.singlePathDisposition_of_confinement` | 678-699 | — | — |
| `Confinement.certifiedSinglePath_of_confinement` | 701-710 | — | — |
| `Confinement.IsoInvariantCanonical` | 730-734 | — | Definition |
| `Confinement.isoInvariantCanonical_of_certifiedSinglePath` | 736-749 | — | — |
| `Confinement.flag_imp_large_spine` | 759-771 | — | — |
| `Confinement.flag_imp_pow_baseMax_lt` | 773-794 | — | — |
| `Confinement.not_flagsAt_of_residualCard_le_pow` | 796-811 | — | — |
| `Confinement.flag_imp_symmetric_spine` | 822-836 | — | — |
| `Confinement.confinement_selectedCellIsOrbit_spine` | 846-868 | — | — |
| `ConfinementP3.ResidueSchemeModel` | 888-899 | — | Structure |
| `ConfinementP3.PrimRank3Classical` | 901-909 | — | Definition |
| `ConfinementP3.residue_primRank3Classical` | 911-928 | — | — |
| `ConfinementP3.confinement_selectedCellIsOrbit_spine_P3` | 938-960 | — | — |
| `ConfinementP3.confinementLargeScheme` | 971-985 | — | Definition |
| `ConfinementP3.largeBridge_confinementLargeScheme` | 987-996 | — | — |
| `ConfinementP3.confinement_selectedCellIsOrbit_spine_P3_discharged` | 998-1016 | — | — |
| `ConfinementWitt.WittCellTransitive` | 1037-1048 | — | Definition |
| `ConfinementWitt.frameSelectorTransitive_of_wittCellTransitive` | 1050-1068 | — | — |
| `ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt` | 1076-1098 | — | — |
| `ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt_classical` | 1115-1136 | — | — |
| `ConfinementSchurianModel.residueModel_of_orbitalGroup` | 1151-1172 | — | Definition, `noncomputable` |

## ChainDescent/CostModel.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CostModel.CostM` | 38-39 | — | `abbrev` |
| `CostModel.CostM.value` | 43-44 | — | Definition |
| `CostModel.CostM.cost` | 45-46 | — | Definition |
| `CostModel.CostM.pure` | 48-49 | — | Definition |
| `CostModel.CostM.tick` | 50-51 | — | Definition |
| `CostModel.CostM.bind` | 52-53 | — | Definition |
| `CostModel.CostM.value_pure` | 55 | — | `@[simp]` |
| `CostModel.CostM.cost_pure` | 56 | — | `@[simp]` |
| `CostModel.CostM.cost_tick` | 57 | — | `@[simp]` |
| `CostModel.CostM.value_bind` | 58 | — | `@[simp]` |
| `CostModel.CostM.cost_bind` | 59-60 | — | `@[simp]` |
| `CostModel.budgetedIterate` | 70-80 | — | Definition |
| `CostModel.cost_budgetedIterate_le` | 82-105 | — | — |
| `CostModel.done_of_budgetedIterate_some` | 107-125 | — | — |
| `CostModel.BudgetedCanonizer` | 132-139 | — | Structure |
| `CostModel.BudgetedCanonizer.run` | 141-143 | — | Definition |
| `CostModel.BudgetedCanonizer.cost_run_le` | 145-149 | — | — |
| `CostModel.WarmRefine.warmRefine_eq_iterate` | 177-180 | — | — |
| `CostModel.WarmRefine.signature_card` | 182-190 | — | — |
| `CostModel.WarmRefine.sigCost` | 197 | — | Definition |
| `CostModel.WarmRefine.roundCost` | 199-200 | — | Definition |
| `CostModel.WarmRefine.warmRefineCost` | 202-204 | — | Definition |
| `CostModel.WarmRefine.warmRefineCost_eq` | 206-210 | — | — |
| `CostModel.WarmRefine.warmRefineCost_le` | 212-214 | — | — |
| `CostModel.PerNode.Phase` | 227-232 | — | Inductive |
| `CostModel.PerNode.capStep` | 234-238 | — | Definition |
| `CostModel.PerNode.value_capStep` | 240-241 | — | `@[simp]` |
| `CostModel.PerNode.cost_capStep_le` | 243-245 | — | — |
| `CostModel.PerNode.cost_budgetedIterate_capped_le` | 247-253 | — | — |
| `CostModel.PerNode.flagsAt` | 255-258 | — | Definition |
| `CostModel.PerNode.flagsAt_iff` | 260-262 | — | — |
| `CostModel.PerNode.capStep_cost_eq_of_not_flags` | 264-269 | — | — |
| `CostModel.PerNode.CappedCanonizer` | 273-281 | — | Structure |
| `CostModel.PerNode.CappedCanonizer.run` | 283-285 | — | Definition |
| `CostModel.PerNode.CappedCanonizer.cost_run_le` | 287-291 | — | — |
| `CostModel.PerNode.CappedCanonizer.done_of_run_some` | 293-296 | — | — |
| `CostModel.CostM.iterate` | 312-316 | — | Definition |
| `CostModel.CostM.value_iterate` | 318-325 | — | — |
| `CostModel.CostM.cost_iterate_const` | 327-337 | — | — |
| `CostModel.CostedWarmRefine.costedRound` | 347-349 | — | Definition |
| `CostModel.CostedWarmRefine.costedWarmRefine` | 351-353 | — | Definition |
| `CostModel.CostedWarmRefine.value_costedWarmRefine` | 355-362 | — | — |
| `CostModel.CostedWarmRefine.cost_costedWarmRefine` | 364-368 | — | — |
| `CostModel.Oracle.oracleCost` | 384-387 | — | Definition |
| `CostModel.Oracle.baseMax` | 389-399 | — | Definition |
| `CostModel.Oracle.oracleBudget` | 401-404 | — | Definition |
| `CostModel.Oracle.oracleCost_le_budget_of_base_le` | 406-410 | — | — |
| `CostModel.Oracle.nodeCost` | 417-418 | — | Definition |
| `CostModel.Oracle.nodeBudget` | 420-421 | — | Definition |
| `CostModel.Oracle.nodeCost_le_budget_of_base_le` | 423-426 | — | — |
| `CostModel.Oracle.not_flagsAt_of_base_le` | 428-438 | — | — |
| `CostModel.SpineInstance.decidableDiscrete` | 456-460 | — | Instance |
| `CostModel.SpineInstance.decidableIsLeaf` | 462-467 | — | Instance |
| `CostModel.SpineInstance.spineCappedCanonizer` | 469-482 | — | Definition |
| `CostModel.SpineInstance.spineCappedCanonizer_step_cost` | 484-490 | — | — |
| `CostModel.SpineInstance.spineCappedCanonizer_cost_le` | 492-503 | — | — |
| `CostModel.SpineInstance.spineCappedCanonizerO` | 516-527 | — | Definition |
| `CostModel.SpineInstance.spineCappedCanonizerO_step_cost` | 529-536 | — | — |
| `CostModel.SpineInstance.spineCappedCanonizerO_cost_le` | 538-550 | — | — |
| `CostModel.SpineInstance.spineCappedCanonizerO_flagsAt_iff` | 552-563 | — | — |
| `CostModel.SpineInstance.not_flagsAt_of_base_le_spine` | 565-575 | — | — |

## ChainDescent/OrbitRecovery.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `OrbitPartition.refl` | 279-282 | — | — |
| `OrbitPartition.symm` | 284-299 | — | — |
| `OrbitPartition.trans` | 301-316 | — | — |

## ChainDescent/Phase2Handoff.lean

The **Phase-1 → Phase-2 seam** (`docs/chain-descent-remaining-work.md` item 6). Both sides of the phase boundary, meeting at `rigidResidue adj = R(G)` (`Cascade`). The `RRU` namespace is the Phase-1 deliverable — "Reaches Rigid Unconditionally", stated as a reduction to two named obligations (`ComputesResidue`, `Poly`), with the recovery obligation `ComputesResidue` discharged on the WL-1-recoverable domain (`computesResidue_phase1Root_of_recoverable`) and — with no recovery citation — on the vertex-transitive class (`phase1Root_eq_rigidResidue_of_pretransitive`). The `Phase2` namespace is the rigid solver's input object + correctness contract (`Sound`/`IsoInvariant`, Algorithm R the future witness). NEXT: the non-transitive (CFI/multipede) remainder of `ComputesResidue` via the cross-branch harvest, or the assume-VT reframe; then factor `canonForm? = phase2 ∘ phase1`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Phase2.trivialP` | 34-36 | The trivial order `P₀` (`fun _ _ => POE.unknown`) the RRU handoff runs at; every permutation preserves it, so the residual group is the full `Aut(adj)`. | `abbrev` |
| `Phase2.handoffBase` | 38-39 | **The Phase-2 handoff base** `R(G)` (`= rigidResidue adj`) handed to the rigid solver. | Definition, `noncomputable` |
| `Phase2.handoff_isRigid` | 41-46 | **The handoff is rigid.** `R(G)` is a base of `Aut^{P₀}(adj)` — the guarantee Phase 2 may assume, for every input. | — |
| `Phase2.orbitPartition_handoff_iff_eq` | 48-55 | **No residual symmetry at the handoff.** At `R(G)` the orbit relation is equality — what makes Phase 2 a rigid search (no symmetry to collapse). | — |
| `Phase2.handoffBase_relabel` | 57-63 | **The handoff is iso-invariant.** Relabelling the graph relabels its handoff base correspondingly — Phase 2's input is a function of the isomorphism class. | — |
| `Phase2.Solver` | 73-74 | **A Phase-2 rigid canonizer**: a canonical labelled adjacency, or an honest flag (`none`). | Definition |
| `Phase2.Sound` | 76-80 | **Phase-2 soundness contract.** Any answer is a genuine relabelling of the input (`Publication` ①a at the residue); Algorithm R is the future witness. | Definition |
| `Phase2.IsoInvariant` | 82-86 | **Phase-2 iso-invariance contract.** Relabelling the input leaves the answer unchanged (`Publication` ①b/①c at the residue); Algorithm R is the future witness. | Definition |
| `RRU.Phase1` | 114-116 | **A Phase-1 canonizer** (skeleton): maps a graph to the base its deferral descent reaches — the rigid residue handed to Phase 2. | `abbrev` |
| `RRU.ComputesResidue` | 118-122 | **The Phase-1 recovery obligation** — the one open input RRU-correctness reduces to: `∀ adj, p1 adj = rigidResidue adj` (the descent computes the iso-invariant `R(G)`). | Definition |
| `RRU.Poly` | 124-127 | **The Phase-1 cost obligation**: the descent reaches the handoff within a polynomial node budget (witness `defaultSpineChain_reaches_leaf`). | Definition |
| `RRU.reachesRigid` | 129-133 | **RRU — reaches rigid (③-side).** `ComputesResidue ⟹` Phase 1 always lands on a rigid (`IsBase`) residue; reduces to `rigidResidue_isBase`. | — |
| `RRU.isoInvariant` | 135-140 | **RRU — iso-invariant (①b/①c-side).** `ComputesResidue ⟹` the handoff transports under relabelling; reduces to `rigidResidue_relabel`. | — |
| `RRU.rru` | 142-151 | **RRU — Reaches Rigid Unconditionally (the Phase-1 deliverable).** `{ComputesResidue, Poly} ⟹` Phase 1 reaches a rigid residue, within budget, iso-invariantly — the Phase-1 half of the endgame reduced to two named obligations. | — |
| `RRU.phase1Root` | 167-172 | **The root Phase-1 (single-shot).** Individualize the visible support at the root — the non-singleton 1-WL cells of the initial colouring. Refinement-computable. | Definition, `noncomputable` |
| `RRU.phase1Root_eq_rigidResidue_of_recoverableAt` | 174-189 | **Per-graph core.** `OrbitRecoverableAt adj P₀ ∅ ⟹ phase1Root adj = rigidResidue adj`, via `movedSet_eq_nonsingletonCells_of_recoverable`. | — |
| `RRU.computesResidue_phase1Root_of_recoverable` | 191-196 | **`ComputesResidue` on the WL-1-recoverable domain.** `(∀ adj, OrbitRecoverableAt adj P₀ ∅) ⟹ ComputesResidue phase1Root`. | — |
| `RRU.phase1Root_eq_rigidResidue_of_pretransitive` | 198-211 | **`ComputesResidue` discharge on the vertex-transitive class — no recovery citation.** If `Aut^{P₀}(adj)` is transitive at `∅`, root recovery is vacuous and `phase1Root` computes `R(G)` unconditionally (DRGs/schemes/Cameron). | — |
| `RRU.phase1Root_reachesRigid_of_recoverable` | 213-219 | **Payoff (root domain).** Under root recoverability, `phase1Root` always lands on a rigid (`IsBase`) residue. | — |
| `RRU.phase1Root_isoInvariant_of_recoverable` | 221-227 | **Payoff (root domain).** Under root recoverability, `phase1Root`'s handoff transports under relabelling. | — |

## ChainDescent/ScratchConfinementCellAffine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellAffine.hne_cast` | 57-61 | — | — |
| `ConfinementCellAffine.isPrimitive_uncast` | 63-67 | — | — |
| `ConfinementCellAffine.AffineRealizedResidue` | 76-84 | — | Definition |
| `ConfinementCellAffine.isPrimitive_of_affineRealizedResidue` | 86-98 | — | — |
| `ConfinementCellAffine.hImprimTrans_of_affineRealizedResidue` | 100-111 | — | — |
| `ConfinementCellAffine.confinement_selectedCellIsOrbit_spine_cell_affine` | 115-137 | — | — |
| `ConfinementCellAffine.ConfinementCitationsCellAffine` | 155-184 | — | Structure |
| `ConfinementCellAffine.descentConfinement_of_bundle_cell_affine` | 186-194 | — | — |
| `ConfinementCellAffine.canon_complete_cell_affine` | 196-204 | — | — |
| `ConfinementCellAffine.descentCanon_showcase_cell_affine` | 206-215 | — | — |

## ChainDescent/ScratchConfinementCellComplete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellComplete.selectedCellIsOrbit_done_of_capstone_cell` | 42-62 | — | — |
| `ConfinementCellComplete.ConfinementCitationsCell` | 64-88 | — | Structure |
| `ConfinementCellComplete.descentConfinement_of_bundle_cell` | 90-94 | — | — |
| `ConfinementCellComplete.canon_complete_cell` | 96-104 | — | — |
| `ConfinementCellComplete.descentCanon_showcase_cell` | 106-115 | — | — |

## ChainDescent/ScratchConfinementCellImprim.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellImprim.selectedCellIsOrbit_of_frameSelectorTransitive` | 62-73 | — | — |
| `ConfinementCellImprim.confinement_selectedCellIsOrbit_spine_cell_total` | 75-106 | — | — |
| `ConfinementCellImprim.hImprimTrans_of_primitive` | 108-120 | — | — |
| `ConfinementCellImprim.confinement_selectedCellIsOrbit_spine_witt_classical_cell_total` | 124-148 | — | — |
| `ConfinementCellImprim.selectedCellIsOrbit_done_of_capstone_cell_total` | 152-174 | — | — |
| `ConfinementCellImprim.ConfinementCitationsCellTotal` | 176-204 | — | Structure |
| `ConfinementCellImprim.descentConfinement_of_bundle_cell_total` | 206-211 | — | — |
| `ConfinementCellImprim.canon_complete_cell_total` | 213-222 | — | — |
| `ConfinementCellImprim.descentCanon_showcase_cell_total` | 224-233 | — | — |

## ChainDescent/ScratchConfinementCellModel.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellModel.CellInvariant` | 42-47 | — | Definition |
| `ConfinementCellModel.cellRestrict` | 49-53 | — | Definition |
| `ConfinementCellModel.cellRestrict_apply` | 55-57 | — | `@[simp]` |
| `ConfinementCellModel.cellRestrictHom` | 59-64 | — | Definition |
| `ConfinementCellModel.CellActionFaithful` | 66-70 | — | Definition |
| `ConfinementCellModel.cellActionFaithful_of_isBase` | 72-102 | — | — |
| `ConfinementCellModel.cellInvariant_selCell_of_gInvariant` | 112-117 | — | — |
| `ConfinementCellModel.stabilizerAt_indivWarmRefine_invariant` | 119-127 | — | — |
| `ConfinementCellModel.cellInvariant_selCell_indivWarmRefine` | 129-134 | — | — |
| `ConfinementCellModel.cellRange_pretransitive` | 138-145 | — | — |
| `ConfinementCellModel.cellCard` | 149-150 | — | Definition, `noncomputable` |
| `ConfinementCellModel.cellEquivFin` | 152-154 | — | Definition, `noncomputable` |
| `ConfinementCellModel.cellGroupFin` | 156-160 | — | Definition, `noncomputable` |
| `ConfinementCellModel.cellGroupFin_card` | 162-172 | — | — |
| `ConfinementCellModel.cellGroupFin_pretransitive` | 174-184 | — | — |
| `ConfinementCellModel.htrans_cell_of_frameSelectorTransitive` | 193-214 | — | — |
| `ConfinementCellModel.CellSchemeModel` | 218-229 | — | Structure |
| `ConfinementCellModel.cellSchemeModel_of_group` | 231-257 | — | Definition, `noncomputable` |
| `ConfinementCellModel.cellSchemeModel_of_group_spine` | 259-279 | — | Definition, `noncomputable` |

## ChainDescent/ScratchConfinementCellP3.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellP3.PrimRank3ClassicalCell` | 38-44 | — | Definition |
| `ConfinementCellP3.largeBridge_confinementLargeScheme_cell` | 46-55 | — | — |
| `ConfinementCellP3.residue_primRank3ClassicalCell` | 57-68 | — | — |
| `ConfinementCellP3.cellResidue_imprimitive_or_cameron` | 70-85 | — | — |
| `ConfinementCellP3.confinement_selectedCellIsOrbit_spine_cell_discharged` | 87-109 | — | — |

## ChainDescent/ScratchConfinementCellWitt.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCellWitt.confinement_selectedCellIsOrbit_spine_witt_cell` | 31-48 | — | — |
| `ConfinementCellWitt.confinement_selectedCellIsOrbit_spine_witt_classical_cell` | 50-71 | — | — |

## ChainDescent/ScratchConfinementCompleteness.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementCompleteness.GraphIso` | 57-59 | — | Definition |
| `ConfinementCompleteness.iso_of_labelledAdj_eq` | 63-73 | — | — |
| `ConfinementCompleteness.canonForm?_complete_mpr` | 75-85 | — | — |
| `ConfinementCompleteness.CanonPartitionInvariant` | 95-102 | — | Definition |
| `ConfinementCompleteness.canonForm?_complete` | 104-112 | — | — |
| `ConfinementCompleteness.canonForm_eq_of_canonFormImages_eq` | 140-152 | — | — |
| `ConfinementCompleteness.dLeaf` | 156-158 | — | Definition, `noncomputable` |
| `ConfinementCompleteness.dChain` | 160-163 | — | Definition, `noncomputable` |
| `ConfinementCompleteness.dChain_isLeaf` | 165-166 | — | — |
| `ConfinementCompleteness.dChain_dirNonempty` | 168-172 | — | Instance, `noncomputable` |
| `ConfinementCompleteness.dCanonForm` | 174-176 | — | Definition, `noncomputable` |
| `ConfinementCompleteness.canonForm?_eq_dCanonForm` | 178-191 | — | — |
| `ConfinementCompleteness.CanonFormImagesIsoInvariant` | 193-203 | — | Definition |
| `ConfinementCompleteness.canonPartitionInvariant_of_imagesIsoInvariant` | 205-216 | — | — |
| `ConfinementCompleteness.canonForm?_complete_of_imagesIsoInvariant` | 218-226 | — | — |
| `ConfinementCompleteness.nonDiscreteSel_equivariant` | 255-267 | — | — |

## ChainDescent/ScratchConfinementX3.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3.indivOne` | 66-68 | — | Definition |
| `ConfinementX3.indivOne_equivariant` | 70-76 | — | — |
| `ConfinementX3.indivOne_eq_one_iff` | 78-81 | — | — |
| `ConfinementX3.indivOne_eq_zero_iff` | 83-84 | — | — |
| `ConfinementX3.indivOne_singleton` | 86-91 | — | — |
| `ConfinementX3.indivStep1` | 104-106 | — | Definition |
| `ConfinementX3.indivStep1_equivariant` | 108-117 | — | — |
| `ConfinementX3.indivStepOne` | 119-135 | — | Definition |
| `ConfinementX3.indivStepOne_χ'` | 137-138 | — | `@[simp]` |
| `ConfinementX3.pickOne` | 154-156 | — | Definition, `noncomputable` |
| `ConfinementX3.pickOne_targets` | 158-167 | — | — |
| `ConfinementX3.pickOne_nonempty` | 169-176 | — | — |
| `ConfinementX3.pickOne_card_le_one` | 178-184 | — | — |
| `ConfinementX3.descentStep` | 200-202 | — | Definition |
| `ConfinementX3.descentColouring` | 204-207 | — | Definition |
| `ConfinementX3.descentStep_transport` | 209-219 | — | — |
| `ConfinementX3.descentColouring_transport` | 221-234 | — | — |
| `ConfinementX3.labelledAdj_rankPerm_cross` | 251-274 | — | — |
| `ConfinementX3.ifCanon_transport_corresponding` | 289-311 | — | — |
| `ConfinementX3.ifCanon_aut_invariant` | 313-324 | — | — |
| `ConfinementX3.ifCanon_iso_invariant_of_reconcile` | 334-352 | — | — |

## ChainDescent/ScratchConfinementX3Complete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3Complete.descentCanon` | 62-68 | — | Definition, `noncomputable` |
| `ConfinementX3Complete.descentCanon_sound` | 70-74 | — | — |
| `ConfinementX3Complete.descentCanon_iso_of_eq` | 76-80 | — | — |
| `ConfinementX3Complete.DescentConfinement` | 82-91 | — | Definition |
| `ConfinementX3Complete.descentCanon_eq_of_iso` | 93-108 | — | — |
| `ConfinementX3Complete.descentCanon_complete` | 110-116 | — | — |
| `ConfinementX3Complete.selectedCellIsOrbit_done_of_capstone` | 131-153 | — | — |
| `ConfinementX3Complete.descentConfinement_of_citations` | 167-192 | — | — |
| `ConfinementX3Complete.descentCanon_complete_of_citations` | 194-218 | — | — |
| `ConfinementX3Complete.ConfinementCitations` | 229-255 | — | Structure |
| `ConfinementX3Complete.descentConfinement_of_bundle` | 257-260 | — | — |
| `ConfinementX3Complete.descentCanonForm?` | 262-265 | — | Definition, `noncomputable` |
| `ConfinementX3Complete.canon_sound` | 267-274 | — | — |
| `ConfinementX3Complete.canon_complete` | 276-285 | — | — |
| `ConfinementX3Complete.descentCanon_showcase` | 287-296 | — | — |

## ChainDescent/ScratchConfinementX3Recon.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3Recon.descentPicks` | 50-59 | — | Definition, `noncomputable` |
| `ConfinementX3Recon.descentPicks_zero` | 61-62 | — | `@[simp]` |
| `ConfinementX3Recon.descentPicks_succ_of_nonempty` | 64-71 | — | — |
| `ConfinementX3Recon.descentPicks_succ_of_empty` | 73-77 | — | — |
| `ConfinementX3Recon.descentColouring_descentPicks_succ` | 79-89 | — | — |
| `ConfinementX3Recon.reconcile_extend` | 100-121 | — | — |
| `ConfinementX3Recon.descentStep_fixed_of_aut` | 132-144 | — | — |
| `ConfinementX3Recon.descentColouring_fixed_of_aut` | 146-166 | — | — |
| `ConfinementX3Recon.descentColouring_append` | 170-176 | — | — |
| `ConfinementX3Recon.descentColouring_snoc` | 178-182 | — | — |
| `ConfinementX3Recon.descentColouring_snoc'` | 184-189 | — | — |
| `ConfinementX3Recon.discrete_transport_iff` | 191-202 | — | — |
| `ConfinementX3Recon.reconcile_one_level` | 213-279 | — | — |
| `ConfinementX3Recon.reconcile_descent` | 292-374 | — | — |
| `ConfinementX3Recon.warmRefine_preserves_singleton` | 386-390 | — | — |
| `ConfinementX3Recon.discrete_of_nonDiscreteSel_empty` | 392-394 | — | — |
| `ConfinementX3Recon.nonDiscreteSel_warmRefine_shrinks` | 396-447 | — | — |
| `ConfinementX3Recon.descentPicks_leaf` | 449-468 | — | — |
| `ConfinementX3Recon.descentPicks_leaf_univ` | 470-475 | — | — |
| `ConfinementX3Recon.reconcile_descent_top` | 477-494 | — | — |
| `ConfinementX3Recon.descentLeaf_canonForm_iso_invariant` | 504-525 | — | — |

## ChainDescent/ScratchConfinementX3Sel.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3Sel.nonSingletonVals` | 44-46 | — | Definition |
| `ConfinementX3Sel.mem_nonSingletonVals` | 48-57 | — | — |
| `ConfinementX3Sel.nonSingletonVals_transport` | 59-74 | — | — |
| `ConfinementX3Sel.minNSVal` | 78-80 | — | Definition, `noncomputable` |
| `ConfinementX3Sel.selCell` | 82-84 | — | Definition, `noncomputable` |
| `ConfinementX3Sel.minNSVal_transport` | 86-89 | — | — |
| `ConfinementX3Sel.selCell_transport` | 91-100 | — | — |
| `ConfinementX3Sel.selCell_nonempty_iff` | 102-125 | — | — |
| `ConfinementX3Sel.selCell_targets` | 127-142 | — | — |
| `ConfinementX3Sel.selCell_colour` | 144-150 | — | — |
| `ConfinementX3Sel.selCellRep` | 154-158 | — | Definition, `noncomputable` |
| `ConfinementX3Sel.selCellRep_targets` | 160-168 | — | — |
| `ConfinementX3Sel.selCellRep_nonempty` | 170-175 | — | — |
| `ConfinementX3Sel.selCellRep_card_le_one` | 177-181 | — | — |
| `ConfinementX3Sel.selCellRep_mem_selCell` | 183-188 | — | — |
| `ConfinementX3Sel.selCellRep_both_in_target` | 192-203 | — | — |

## ChainDescent/ScratchConfinementX3Spine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ConfinementX3Spine.oneStepIndivStep` | 42-49 | — | Definition, `noncomputable` |
| `ConfinementX3Spine.oneStepColouring` | 53-60 | — | Definition, `noncomputable` |
| `ConfinementX3Spine.oneStepD` | 62-69 | — | Definition, `noncomputable` |
| `ConfinementX3Spine.oneStepTrace` | 71-79 | — | Definition, `noncomputable` |
| `ConfinementX3Spine.oneStepSpineChain` | 81-88 | — | Definition, `noncomputable` |
| `ConfinementX3Spine.pickOne_partitionInvariant` | 92-103 | — | — |
| `ConfinementX3Spine.oneStepSpineChain_reaches_leaf` | 105-114 | — | — |
| `ConfinementX3Spine.oneStep_dirNonempty` | 118-122 | — | Instance, `noncomputable` |
| `ConfinementX3Spine.oneStep_canonForm_isLabelledAdj` | 124-131 | — | — |

## ChainDescent/ScratchExecutable.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Executable.triangle` | 35-36 | — | Definition |
| `Executable.path3` | 38-40 | — | Definition |
| `Executable.vertexRank_bij` | 44-50 | — | — |
| `Executable.rankInv` | 52-56 | — | Definition |
| `Executable.rankInv_spec` | 58-71 | — | — |
| `Executable.rankInv_eq_symm` | 73-77 | — | — |
| `Executable.canonAdjComp` | 81-84 | — | Definition |
| `Executable.canonAdjComp_eq` | 86-93 | — | — |
| `Executable.leafColouring` | 95-97 | — | Definition |
| `Executable.leaf_discrete` | 99-105 | — | — |
| `Executable.canonOutput` | 107-111 | — | Definition |
| `Executable.canonOutput_sound` | 113-124 | — | — |

## ChainDescent/ScratchOrbitalSchemeAutLower.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `le_schemeAutGroup_orbitalScheme` | 22-35 | — | — |
| `card_le_schemeAutGroup_orbitalScheme` | 37-46 | — | — |

## ChainDescent/ScratchRenumber.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Renumber.rankNat_strict_mono` | 34-47 | — | — |
| `Renumber.vertexRankNat_eq_iff` | 49-62 | — | — |
| `Renumber.refineStepR` | 66-69 | — | Definition |
| `Renumber.refineStepR_lt` | 71-74 | — | — |
| `Renumber.refineStepR_iff` | 76-84 | — | — |
| `Renumber.samePartition_refineStepR` | 86-91 | — | — |
| `Renumber.samePartition_iterate` | 95-106 | — | — |
| `Renumber.warmRefineR` | 108-111 | — | Definition |
| `Renumber.samePartition_warmRefineR` | 113-117 | — | — |
| `Renumber.discrete_warmRefineR` | 119-122 | — | — |
| `Renumber.refineRoundMat` | 135-140 | — | Definition |
| `Renumber.refineRoundMat_eq` | 142-147 | — | — |
| `Renumber.warmRefineMat` | 149-151 | — | Definition |
| `Renumber.warmRefineMat_eq` | 153-158 | — | — |

## ChainDescent/ScratchRenumberExec.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RenumberExec.canonOutputR` | 29-35 | — | Definition |
| `RenumberExec.canonOutputR_sound` | 37-59 | — | — |
| `RenumberExec.canonOutputMat` | 70-75 | — | Definition |
| `RenumberExec.canonOutputMat_eq` | 77-82 | — | — |
| `RenumberExec.canonOutputMat_sound` | 84-90 | — | — |
| `RenumberExec.render3` | 92-98 | — | Definition |

## ChainDescent/ScratchRenumberFast.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RenumberFast.materialize` | 32-36 | — | Definition |
| `RenumberFast.materialize_eq` | 38-39 | — | — |
| `RenumberFast.defaultColouringMat` | 41-49 | — | Definition |
| `RenumberFast.leafColouringMat` | 51-53 | — | Definition |
| `RenumberFast.leafLevelMat` | 55-57 | — | Definition |
| `RenumberFast.canonOutputFast` | 59-62 | — | Definition |
| `RenumberFast.canonOutputFast_sound` | 64-80 | — | — |
| `RenumberFast.render3` | 82-88 | — | Definition |

## ChainDescent/Spine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Discrete.warmRefine_preserves` | 532-541 | Warm refinement preserves discreteness: if `χ` is injective, so is `warmRefine adj P χ`. | — |
| `DirAssignment.default` | 713-720 | — | Definition |
| `LinearOracleSpec.some_isAut` | 1323-1335 | — | — |

## Publication.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Showcase.Iso` | 121-124 | Graph isomorphism on the project’s own `AdjMatrix`: some relabelling of `G` is `H`. Definitionally `CanonSpec.GraphIso`, which is why `①b` needed zero glue. | Definition |
| `Showcase.canonForm?` | 141-167 | ★★★ **THE SHOWCASE CANONIZER — cell-indexed since 2026-08-08 (`W-g`)**: `RecordDeepenCell.canonFormFast`, i.e. the fused descent at `recordKey` and `fun c => recordSupplyFast ++ Deepen.deepenCellSupply c`, run through `Select.selNodeFastC`. Each cell is judged by generators of descents anchored *in that cell* — which is what makes `③` provable at the object `①`/`②` are about. It `#eval`s. | Definition |
| `Showcase.canonForm?_record` | 169-175 | `①` for the showcase object, **global and with no hypothesis** — `recordDeepenCell_full_fast.1`. `Select.selNodeC_canonizer` needs only `KeyEquivariant` + `CellOrbitTransport`; the guarded cell-anchored supply delivers the second with no `SupplyEquivariant`. | — |
| `Showcase.cost` | 177-181 | The canonizer's operation count — `RecordDeepenCell.costFast`, the `CostM` cost projection of the very definition `canonForm?` is the value projection of. | Definition |
| `Showcase.residueRigidObstruction` | 330-333 | **(D2) the rigid/symmetry obstruction, DEFINED** as `¬ TwinFamily.TinhoferGraph G` — via `schurianAt_iff_no_rigidObstruction` this is *"some individualization-reachable colouring of `G` carries a rigid obstruction"*: structural, iso-invariant, algorithm-independent, so it clears the firewall. Replaces three `opaque` atoms that had made **both** ③ obligations unprovable in principle. ⚠ An **over-approximation** — a CFI graph is not Tinhofer although its obstruction is linear; W2's job is to narrow it. | Definition |
| `Showcase.UnhandledResidue` | 335-337 | **THE RESIDUE** — one disjunct today, by design: `residueRigidObstruction` (= `¬ TinhoferGraph`). D0 `residueNonSchurian` and D1 `residueHiddenJohnson` were **dropped, not kept as opaque placeholders**: an opaque disjunct makes the handled half of `unhandledResidue_nonvacuous` unprovable in principle. ⚠ Add `∨ NonLinearRigidObstruction` only once W2 gives it content. | Definition |
| `Showcase.costConst` | 387-388 | The pinned cost constant `= RecordDeepenCell.costConst = 69` (was `RecordKey.costConst = 57` before the cell-indexed swap: +8 per-cell supply billing, +4 the newly-billed deepen guard). `ring`-checked, not asserted. ⚠ A bound from declared flat charges, not a measurement of the algorithm's true constant. | Definition |
| `Showcase.costDeg` | 390-391 | The pinned cost degree `= RecordDeepenCell.costDeg = 13` — **unchanged** across the cell-indexed swap. ⚠ The bound is `costConst * (n+1) ^ costDeg`; the `n`-form is false at `n = 0`. ⚠⚠ The degree is a property of the *bound*, which over-bills in several places — it rules out exponentials, it does not establish 13 as the algorithm's true degree. | Definition |
| `Showcase.cameron_classification` | 281-286 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: G3 — the primitive-CC / Cameron classification (CFSG). ⚠ The citable threshold is Sun–Wilmes `exp(Õ(n^{1/3}))`; **never** instantiate at the quasi-poly `n^{log₂ n}`, where the statement is Babai’s OPEN conjecture. | ⏸ axiom (commented out) |
| `Showcase.skresanov_two_closure` | 287-290 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Skresanov rank-3 affine 2-closure (underpins all four Route-C families’ `|Aut|` side). | ⏸ axiom (commented out) |
| `Showcase.liebeck_rank3` | 291-294 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Liebeck affine-rank-3 classification. | ⏸ axiom (commented out) |
| `Showcase.ponomarenko_2sep` | 295-303 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Ponomarenko cyclotomic 2-separability (the 1-dim cyclotomic slice). | ⏸ axiom (commented out) |
| `Showcase.ftpg` | 304-310 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: fundamental theorem of projective geometry. ⚠ Wire only the **corrected difference-cone** form — the bare cone-preserving antecedent was false-as-formalized. | ⏸ axiom (commented out) |
| `Showcase.buekenhout_shult` | 311-318 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Buekenhout–Shult / Veldkamp–Tits, polar space of rank ≥ 3 is classical. **Correctness only, not a complexity bound.** | ⏸ axiom (commented out) |
| `Showcase.payne_thas` | 319-327 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Payne–Thas classical-GQ recognition. ⚠ **Must be narrowed** to a specific characterization before wiring — there is no general “classical GQ recognition” theorem, and unscoped it would be citation-shaped open mathematics. | ⏸ axiom (commented out) |
| `Showcase.witt_flag_transitivity` | 328 | ⏸ **INACTIVE — the `axiom` line is COMMENTED OUT** (2026-08-04): it was consumed by nothing, so declaring it only invited a reviewer to read it as this file’s trusted base. The `opaque … : Prop` and its citation doc-comment are retained; restoring it for W2/Route C is deleting `-- ⏸ ` from one line. Citation: Witt’s theorem (transitivity on isometric isotropic frames). **Correctness only**; a planned in-project build. | ⏸ axiom (commented out) |
| `Showcase.canon_sound` | 467-474 | **`①a` SOUNDNESS, UNCONDITIONAL** — when the canonizer answers, its output is a genuine relabelling of the input. Axiom-clean; the record’s `SoundOpt` half applied directly (`Labelled n` is definitionally the matrix type, so no glue). | — |
| `Showcase.canon_complete` | 476-501 | **`①b` COMPLETENESS, UNCONDITIONAL** — whenever it answers on both inputs, equal forms ⟺ isomorphic. Axiom-clean. **Free**: `CanonSpec.complete_of_isCanonicalFormOpt` says sound ∧ iso-invariant ⟹ complete. ⛔ Do **not** restate the resolver contract as the single unconditional `Covering` — a covering resolver is provably value-invisible, which pins the object to the retired `canonMin` anchor. | — |
| `Showcase.flag_iso_invariant` | 503-509 | **`①c` THE FLAG IS ISO-INVARIANT, UNCONDITIONAL** — flagging is a property of the isomorphism class. Axiom-clean; free from the record’s `IsoInvariantOpt` half, since one equation on `Option`s carries the answer **and** the flag. | — |
| `Showcase.canon_poly_or_flag` | 511-521 | **`②` POLY-OR-FLAG** — proved axiom-clean **on the LEFT disjunct**, so the cost claim needs no flag escape: `cost ≤ 69 * (n+1)^13` on every input. Fan-out `≤ 1` holds by construction and every component is billed, including the deepen guard. ⚠ See `costDeg` for what the degree does and does not certify. | — |
| `Showcase.residue_if_flag` | 549-563 | ★★★ **`③` — DISCHARGED 2026-08-08 (`W-g`), axiom-clean**: if the canonizer flags, the input is provably not a Tinhofer graph. `recordDeepenCell_full_fast.2.2` — the same object `①` and `②` are about, as the standing steer requires. ⚠ The residue is an **over-approximation** (CFI graphs count as residual though their obstruction is linear); narrowing it is W2. | — |
| `Showcase.unhandledResidue_nonvacuous` | 565-581 | ★★ **DISCHARGED 2026-08-04**, axiom-clean, from `RestrictedTransport.tinhoferGraph_nonvacuous`: handled witness `K₁,₂,₃`, residual witness `K₃ ⊔ C₄`. Both are structural facts about the *graphs*; neither mentions the algorithm. | — |
| `Showcase.canonizer` | 588-600 | **THE HEADLINE** — a complete iso-invariant (never wrong) **and** within the explicit polynomial budget, composed from the obligations. Axiom-clean, and since 2026-08-08 the whole file is: zero `sorry`, zero custom axioms, every obligation a property of one object. | — |
## ChainDescent/CanonicalForm.lean

**Mixed-composition Stage 0a — the canonical-form correctness framework** (`docs/chain-descent-mixed-composition.md`).
The spec is **sound ∧ iso-invariant**, deliberately NOT the global lex-min (the deferral schedule yields a
*different* iso-invariant canonical form). `complete_of_isCanonicalForm` makes ①b/①c free; the only real
obligation is iso-invariance of the construction. `lexMin` + `isCanonicalForm_lexMin` reduce a canonizer's
correctness to (i) each candidate is a relabelling + (ii) `cand (relabelAdj σ G) = cand G` (candidate-SET equality).

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CanonSpec.Labelled` | 35-36 | A candidate canonical output — a labelled adjacency matrix. | `abbrev` |
| `CanonSpec.GraphIso` | 40-42 | Graph isomorphism: some relabelling of `G` is `H` (matches `Publication.Iso`). | Definition |
| `CanonSpec.GraphIso.refl` | 44-45 | Reflexivity of `GraphIso` (via the identity permutation). | — |
| `CanonSpec.iso_of_labelledAdj_eq` | 47-55 | A common labelled image ⟹ isomorphic (`labelledAdj πG G = labelledAdj πH H → GraphIso G H`). | — |
| `CanonSpec.relabelAdj_eq_of_labelledAdj` | 57-64 | `labelledAdj π G = H.adj → relabelAdj π G = H` (structure-level restatement of `GraphIso`). | — |
| `CanonSpec.Sound` | 68-70 | The canonizer's output on `G` is a genuine relabelling of `G`. | Definition |
| `CanonSpec.IsoInvariant` | 72-74 | Relabelling the input leaves the output unchanged: `C (relabelAdj σ G) = C G`. | Definition |
| `CanonSpec.IsCanonicalForm` | 76-78 | A canonical form = `Sound ∧ IsoInvariant`. | Definition |
| `CanonSpec.complete_of_isCanonicalForm` | 80-93 | **THE payoff — completeness is FREE:** sound ∧ iso-invariant ⟹ `C G = C H ↔ GraphIso G H`. | — |
| `CanonSpec.lexMin` | 100-102 | The lex-least labelling in a nonempty finite candidate set (via `MatrixLex`). | Definition, `noncomputable` |
| `CanonSpec.lexMin_mem` | 104-110 | `lexMin` returns a genuine member of the candidate set. | — |
| `CanonSpec.lexMin_congr` | 112-115 | `lexMin` depends only on the candidate SET (nonemptiness proof irrelevant). | — |
| `CanonSpec.sound_lexMin` | 117-123 | Soundness of a lex-min canonizer, from: each candidate is a relabelling. | — |
| `CanonSpec.isoInvariant_lexMin` | 125-133 | Iso-invariance of a lex-min canonizer, reduced to `cand (relabelAdj σ G) = cand G`. | — |
| `CanonSpec.isCanonicalForm_lexMin` | 135-144 | Stage-0 assembly: a lex-min over a sound, set-iso-invariant candidate family is a canonical form. | — |
| `CanonSpec.SoundOpt` | 157-160 | §Stage-0a Soundness for a FLAGGING canonizer: whenever it answers, the output is a relabelling of the input. Exactly the `Publication.canon_sound` (①a) statement. | Definition |
| `CanonSpec.IsoInvariantOpt` | 162-165 | §Stage-0a Iso-invariance for a flagging canonizer: relabelling the input changes nothing — including WHETHER it flagged. One equation carrying both the output invariance and ①c. | Definition |
| `CanonSpec.IsCanonicalFormOpt` | 167-170 | §Stage-0a THE complete spec of the mixed canonizer: sound ∧ iso-invariant. Nothing else is required — in particular no global lex-min. | Definition |
| `CanonSpec.eq_of_graphIso` | 172-178 | §Stage-0a Isomorphic inputs receive the same answer (same value, or both flagged). The engine behind both ①b and ①c. | — |
| `CanonSpec.complete_of_isCanonicalFormOpt` | 180-194 | §Stage-0a ①b FOR FREE: a sound, iso-invariant flagging canonizer is a complete isomorphism invariant. The `Publication.canon_complete` statement. | — |
| `CanonSpec.flag_iso_invariant_of_isoInvariantOpt` | 196-200 | §Stage-0a ①c FOR FREE: flagging is a property of the isomorphism class. The `Publication.flag_iso_invariant` statement. | — |
| `CanonSpec.IsoInvariantPred` | 213-215 | §Stage-0a An iso-invariant predicate on graphs — the `handled` / ¬stalled side of the flag. | Definition |
| `CanonSpec.guardBy` | 217-220 | §Stage-0a Gate a total construction by a handled-predicate: answer when handled, flag otherwise. | Definition, `noncomputable` |
| `CanonSpec.isCanonicalFormOpt_guardBy` | 222-242 | §Stage-0a THE FLAG IS FREE: a canonical form gated by an iso-invariant handled-predicate is a flagging canonical form. So the flag adds no obligation beyond the equivariance of `stalled`. | — |
| `CanonSpec.isCanonicalFormOpt_some` | 244-255 | §Stage-0a The total theory embeds: a never-flagging canonical form is a flagging one. | — |
## ChainDescent/Descend.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Descend.decidableDiscrete` | 74-76 | §Stage-0b Decidability of `Discrete`, so the descent can test `is this a leaf?` computably. | Instance |
| `Descend.rankInv` | 80-82 | §Stage-0b Computable inverse of `vertexRank` (rank → vertex). Needed because `Colouring.rankPerm` is noncomputable, so the leaf cannot be emitted through it. | Definition |
| `Descend.vertexRank_surj` | 84-88 | §Stage-0b On a discrete colouring `vertexRank` is surjective (it underlies the bijection `rankPerm`). | — |
| `Descend.rankInv_spec` | 90-101 | §Stage-0b `rankInv` really inverts `vertexRank` on a discrete colouring. | — |
| `Descend.rankInv_eq_symm` | 103-107 | §Stage-0b `rankInv` is the inverse permutation `rankPerm.symm`. | — |
| `Descend.leafMatrix` | 109-111 | §Stage-0b The leaf matrix: relabel the input by colour-rank. Computable; the descent's output at a discrete node. | Definition |
| `Descend.leafMatrix_eq_labelledAdj` | 113-118 | §Stage-0b The computable leaf emit EQUALS `labelledAdj (rankPerm …)` — so it is a genuine relabelling. | — |
| `Descend.leafMatrix_sound` | 120-123 | §Stage-0b ①a at the leaf: the emitted matrix is a relabelling of the input. Base case of `SoundOpt descend`. | — |
| `Descend.indivOne` | 127-130 | §Stage-0b INDEX-FREE individualization (the X3 cut): mark one vertex with a parity bit on its existing colour, never `v.val`. An index-dependent individualization leaks the labelling into the leaf and cannot be iso-invariant. | Definition |
| `Descend.indivOne_singleton` | 132-137 | §Stage-0b The individualized vertex becomes a singleton (parity separates it). | — |
| `Descend.indivOne_refines_off` | 139-144 | §Stage-0b Off the individualized vertex, `indivOne` induces the same partition as the input colouring. | — |
| `Descend.cellOf` | 148-150 | §Stage-0b The colour class (cell) of a given colour. | Definition |
| `Descend.nonSingletonColours` | 152-154 | §Stage-0b The branchable colours — those whose cell is not a singleton. | Definition |
| `Descend.targetColour` | 156-158 | §Stage-0b The EQUIVARIANT target-cell selector: the least non-singleton colour value (a function of the colouring alone; no vertex index is read). `none` exactly when discrete. | Definition |
| `Descend.branches` | 160-168 | §Stage-0b The branch list — vertices of the target cell. A `List` (not `Finset`: `Finset.toList` is noncomputable), so its ORDER is labelling-dependent; harmless because the aggregate is a permutation-invariant minimum. | Definition |
| `Descend.mem_branches_iff` | 170-174 | §Stage-0b Membership in the branch list is exactly "carries the target colour". | — |
| `Descend.branches_ne_nil` | 176-197 | §Stage-0b A non-discrete colouring always has a branchable cell — so the descent can always take a step. Feeds the totality theorem. | — |
| `Descend.exists_partner_of_mem_branches` | 199-217 | §Stage-0b Every branch vertex sits in a NON-singleton cell (it has a same-coloured partner) — the engine of `ncol_lt_indivOne`, hence of totality. | — |
| `Descend.branches_nodup` | 219-225 | The branch list has no duplicates (a filter of `finRange`). §Turns "the narrowing has a unique member" into "has **length 1**" — i.e. it is what lets a resolver's *firing* be stated quantitatively at all. | — |
| `Descend.length_lt_of_missing` | 227-237 | A nodup list strictly inside another is strictly shorter. §The currency of **partial** firing: "the resolver discarded ≥1 branch" ⟹ "the fan-out actually went down". | — |
| `Descend.Refiner` | 246-247 | §Stage-1 A refinement round with its cost (`CostM`), carried as a PARAMETER so the `Encodable.encode` staller is not baked into the object. | `abbrev` |
| `Descend.Resolver` | 249-250 | §Stage-1 A branch-narrowing resolver with its cost: narrow the branch list, or defer. Takes the `AdjMatrix` (both instances need the graph). Consume and force are two instances, one per contract route. | `abbrev` |
| `Descend.refineV` | 252-253 | §Stage-1 The refiner's `value` projection (the `cost` half is what `②` will read). | Definition |
| `Descend.narrow` | 255-258 | §Stage-1 The NARROWED branch list — the resolver's value, defaulting to the full branch list on defer. The whole resolver contract is stated about this one object. | Definition |
| `Descend.deferAll` | 260-262 | §Stage-1 The baseline resolver: never narrows. `descend deferAll` is the honest exhaustive-branching object. | Definition |
| `Descend.narrow_deferAll` | 264-265 | §Stage-1 The baseline resolver narrows to the full branch list (i.e. not at all). | `@[simp]` |
| `Descend.allPairs` | 269-271 | §Stage-2 All index pairs in row-major order; the basis for `flatten` (and hence for `flatten_injective`). | Definition |
| `Descend.mem_allPairs` | 273-275 | §Stage-2 Every index pair occurs in `allPairs`. | — |
| `Descend.flatten` | 277-279 | §Stage-2 Row-major flattening of a labelled matrix, defined over `allPairs` so that injectivity is immediate. | Definition |
| `Descend.flatten_injective` | 281-283 | §Stage-2 A matrix is determined by its row-major entries. This is what makes `lexLe` a genuine total order, hence the aggregate a well-defined minimum. | — |
| `Descend.lexLeList` | 285-289 | §Stage-2 Computable lexicographic ≤ on `Nat` lists. | Definition |
| `Descend.lexLe` | 291-292 | §Stage-2 Computable row-major lexicographic ≤ on labelled matrices. | Definition |
| `Descend.lexMin?` | 294-300 | §Stage-2 The lex-least matrix of a list (`none` on the empty list). | Definition |
| `Descend.aggregate` | 302-304 | §Stage-0b Combine branch results: flag if any branch flagged, else take the lex-least leaf. Deterministic — which is all iso-invariance needs (the spec never asks WHICH leaf). | Definition |
| `Descend.descend` | 318-331 | §Stage-0b THE OBJECT: the computable, resolver-parameterized branching descent, in the cost monad. Correctness (①) is theorems about its `value`, cost (②) about its `cost`, and the executable IS this definition. Fuel is PER-LAYER, never threaded, so each resolver's poly-or-flag behaviour is local. | Definition |
| `Descend.canonForm?` | 333-335 | §Stage-0b The top-level canonizer object — the `value` projection of `descend`. This is what `SoundOpt`/`IsoInvariantOpt` are proved of and what `Publication.canonForm?` becomes. | Definition |
| `Descend.descentCost` | 337-340 | §Stage-0b The descent's cost — the `cost` projection of the SAME definition (no separate cost object, no bridge). | Definition |
| `Descend.descend_val_leaf` | 344-347 | §Stage-2 The descent emits the leaf matrix at any fuel once the colouring is discrete (discreteness is tested BEFORE fuel). | — |
| `Descend.descend_val_zero` | 349-351 | §Stage-2 Out of fuel on a non-discrete colouring, the descent flags. (A placeholder for the real mutual-stall flag — `canonForm?_ne_none` proves it never actually fires.) | — |
| `Descend.descend_val_succ` | 353-359 | §Stage-2 The descent's `value` at a branching node: the aggregate over the NARROWED branches. Isolates the value projection once, so every later proof is about `narrow` and nothing else. | — |
| `Descend.lexMin?_mem` | 366-382 | §Stage-2 The lex-min of a list is a member of it. | — |
| `Descend.aggregate_mem` | 384-392 | §Stage-2 The aggregate returns one of its inputs — the key to soundness of the branch case. | — |
| `Descend.lexLeList_refl` | 425-429 | §Stage-2 Reflexivity of list-lex ≤. | — |
| `Descend.lexLeList_total` | 431-443 | §Stage-2 Totality of list-lex ≤. | — |
| `Descend.lexLeList_trans` | 445-470 | §Stage-2 Transitivity of list-lex ≤. | — |
| `Descend.lexLeList_antisymm` | 472-485 | §Stage-2 Antisymmetry of list-lex ≤. | — |
| `Descend.lexLe_refl` | 487 | §Stage-2 Reflexivity of matrix-lex ≤. | — |
| `Descend.lexLe_total` | 488 | §Stage-2 Totality of matrix-lex ≤. | — |
| `Descend.lexLe_trans` | 489-490 | §Stage-2 Transitivity of matrix-lex ≤. | — |
| `Descend.lexLe_antisymm` | 491-492 | §Stage-2 Antisymmetry of matrix-lex ≤ (via `flatten_injective`). Makes `lexLe` a total order, hence the aggregate a genuine minimum. | — |
| `Descend.lexMin?_eq_none_iff` | 494-504 | §Stage-2 `lexMin?` flags exactly on the empty list. | — |
| `Descend.lexMin?_le` | 506-538 | §Stage-2 `lexMin?` really is the minimum: it is ≤ every member. | — |
| `Descend.lexMin?_perm` | 540-558 | §Stage-2 `lexMin?` is permutation-invariant — it depends only on the multiset of candidates. | — |
| `Descend.aggregate_perm` | 560-573 | §Stage-2 THE AGGREGATE IS PERMUTATION-INVARIANT. Discharges the obligation created by the index-ordered branch `List`: the labelling-dependent branch order provably never leaks into the output. | — |
| `Descend.descend_sound` | 394-412 | §Stage-2 ①a for the descent: whenever it answers, the answer is a relabelling. Holds for ANY refinement and ANY resolver — narrowing only removes branches, so a mis-narrowing resolver costs a branch, never correctness. | — |
| `Descend.soundOpt_canonForm?` | 414-418 | §Stage-2 `SoundOpt` for the top-level object — the `Publication.canon_sound` (①a) obligation, DISCHARGED. | — |
| `Descend.lexMin?_congr_mem` | 575-600 | §7 `lexMin?` depends only on the *set* of candidates (a minimum under a total order does). Strictly stronger than `lexMin?_perm` — multiplicities may differ. | — |
| `Descend.aggregate_congr_mem` | 602-622 | §7 **★ The aggregate depends only on the SET of branch results.** What the **consume** resolver needs: it *drops* branches, so the branch multiset genuinely shrinks — but the value set does not, and that is all the aggregate sees. | — |
| `Descend.aggregate_ne_none` | 624-641 | §Stage-2 The aggregate answers whenever the branch list is nonempty and no branch flagged — the step lemma of the totality theorem. | — |
| `Descend.transportColouring` | 649-651 | §Stage-2 Transport a colouring along a relabelling: χ on G becomes χ∘σ⁻¹ on `relabelAdj σ G`. | Definition |
| `Descend.discrete_transport` | 653-661 | §Stage-2 Discreteness transports along a relabelling. | — |
| `Descend.vertexRank_transport` | 663-667 | §Stage-2 The rank of σv under the transported colouring is the rank of v under the original — the reason the σ cancels in the leaf. | — |
| `Descend.indivOne_transport` | 669-678 | §Stage-2 Individualization commutes with transport. This is where the INDEX-FREE choice pays: an index-dependent individualization would fail this outright. | — |
| `Descend.cellOf_card_transport` | 680-692 | §Stage-2 Cell sizes are preserved under transport. | — |
| `Descend.image_transport` | 694-702 | §Stage-2 The set of colour values is preserved under transport. | — |
| `Descend.targetColour_transport` | 704-711 | §Stage-2 The target colour is the same natural number on both sides — so the branch set transports. | — |
| `Descend.leafMatrix_transport` | 713-731 | §Stage-2 THE HEART OF ①b: the emitted leaf matrices are LITERALLY EQUAL under relabelling. The σ cancels because the output is indexed by colour-RANKS, not by vertices. | — |
| `Descend.RefineEquivariant` | 757-760 | §Stage-2 Carried hypothesis on the refinement PARAMETER: the refinement round commutes with relabelling. (The encode-free round satisfies it; carried because `refine` is a parameter, so the Encodable.encode staller is not baked in.) | Definition |
| `Descend.TransportAt` | 762-766 | §Stage-2 The descent's iso-invariance AT A GIVEN FUEL — the graded induction statement, which the resolver contract is allowed to consume as its induction hypothesis. | Definition |
| `Descend.NarrowTransport` | 768-785 | §Stage-2 ★ THE RESOLVER CONTRACT: the narrowed-branch aggregate TRANSPORTS under relabelling. Strictly weaker than covering — it does NOT ask narrowing to preserve the aggregate, only to produce the same one on `G` and `σ·G`, which is what lets FORCE change the canonical form instead of having to know the answer. FUEL-GRADED (the IH is threaded in), which is what makes the CONSUME instance provable without circularity. | Definition |
| `Descend.branchVal_transport` | 787-796 | §Stage-2 The per-branch values agree under transport (`indivOne` equivariance + the refiner's equivariance + the IH). Shared by both contract routes. | — |
| `Descend.Covering` | 803-808 | §Stage-2 SUFFICIENT CONDITION 1 (the CONSUME route): narrowing does not change the aggregate, because every discarded branch is already reachable through a kept one (a verified path-fixing automorphism). Redundancy, not victory. The choice of representative is genuinely NON-equivariant — which is exactly what covering licenses. ⚠ It is NOT the general contract: see `canonForm?_eq_deferAll_of_covering`. | Definition |
| `Descend.CoveringAt` | 810-826 | §9 **★ The fuel-graded covering — the form a real resolver instance satisfies.** `Covering` with the induction hypothesis `TransportAt rf R fuel` threaded in. `consume` needs this: its covering witness *is* `descend_transport` at an automorphism, one fuel level down. | Definition |
| `Descend.coveringAt_of_covering` | 828-829 | §9 Unconditional covering implies the graded form. | — |
| `Descend.narrowTransport_of_coveringAt` | 831-838 | §9 **Sufficient condition 1 (graded).** Fuel-graded covering ⟹ the resolver contract. The entry point for `consume`. | — |
| `Descend.narrowTransport_of_covering` | 840-842 | §Stage-2 The CONSUME route into the contract: covering ⟹ `NarrowTransport`. | — |
| `Descend.NarrowEquivariant` | 850-852 | §Stage-2 SUFFICIENT CONDITION 2 (the FORCE route): the narrowing is a structural function of `(adj, χ)` and so transports. The discards are genuinely DIFFERENT and the aggregate CHANGES — consistently — yielding a different but equally valid canonical form. No global lex-min, no knowledge of the answer. Checkable: never break ties by vertex index. | Definition |
| `Descend.narrowTransport_of_narrowEquivariant` | 854-860 | §Stage-2 The FORCE route into the contract: equivariant narrowing ⟹ `NarrowTransport`. This is what lets the rigid solver enter Lean at all. | — |
| `Descend.covering_deferAll` | 862-864 | §Stage-2 The baseline resolver never narrows, so it is trivially covering. | — |
| `Descend.branches_transport_perm` | 733-748 | §Stage-2 The branch list transports UP TO PERMUTATION (it is built in index order) — which is exactly why `aggregate_perm` is needed. | — |
| `Descend.narrowEquivariant_deferAll` | 866-868 | §Stage-2 The baseline resolver is also trivially equivariant — `deferAll` takes BOTH contract routes. | — |
| `Descend.narrowTransport_deferAll` | 870-872 | §Stage-2 The exhaustive-branching object satisfies the resolver contract outright, carrying no resolver obligation at all. | — |
| `Descend.NarrowFn` | 895-896 | An **intermediate narrowing**: the reference list a resolver's aggregate is compared against. Definition. | `abbrev` |
| `Descend.NarrowFnEquivariant` | 898-901 | The intermediate narrowing transports under relabelling (`NarrowEquivariant`, for a bare function). Definition. | Definition |
| `Descend.CoveringOfAt` | 903-911 | **`R` covers the intermediate `N`** — fuel-graded, so a composite's consume half can still use the induction hypothesis. Definition. | Definition |
| `Descend.narrowTransport_of_coveringOfAt` | 913-923 | §**THE GENERAL RESOLVER CONTRACT — the third and unifying route.** Covering an *equivariant intermediate* `N` implies `NarrowTransport`. `Covering` is the case `N = branches`; `NarrowEquivariant` is `N = narrow R`; the **mixed** resolver is `N = the forced set`. This is what admits `Composite.forceThenConsume` — neither earlier route does, so the interleaved engine was previously not instantiable. | — |
| `Descend.narrowFnEquivariant_branches` | 925-927 | `branches` is an equivariant intermediate — exhibiting `Covering` as the special case of the general route. | — |
| `Descend.descend_transport` | 931-952 | §Stage-2 ①b/①c: the descent is ISO-INVARIANT. The branch case is EXACTLY the resolver contract — note it needs no refiner hypothesis, so `NarrowTransport` is the whole per-node obligation. | — |
| `Descend.isoInvariantOpt_canonForm?` | 954-964 | §Stage-2 `IsoInvariantOpt` for the top-level object — ①b and ①c then follow for free via Stage 0a. | — |
| `Descend.isCanonicalFormOpt_canonForm?` | 966-972 | §Stage-2 ★ THE STAGE-2 CAPSTONE: the descent IS a canonical form (sound ∧ iso-invariant), hence a complete isomorphism invariant with an iso-invariant flag. ①a/①b/①c all discharged for the real object, modulo exactly two carried hypotheses. | — |
| `Descend.canonForm?_complete` | 974-980 | §Stage-2 The `Publication.canon_complete` (①b) obligation, for the real object. | — |
| `Descend.canonForm?_flag_iso_invariant` | 982-987 | §Stage-2 The `Publication.flag_iso_invariant` (①c) obligation, for the real object. | — |
| `Descend.canonForm?_eq_deferAll_of_covering` | 993-1017 | §Stage-2 ★★ WHY COVERING WAS TOO STRONG: a COVERING resolver is VALUE-INVISIBLE — it computes exactly the same answer as the exhaustive `deferAll`, changing the cost but never the answer. So demanding covering of every resolver pins the object to the exhaustive branch-min (= the retired `canonMin` anchor), and a FORCE resolver could satisfy it only by already computing that min — i.e. only by KNOWING THE ANSWER. This is the theorem that retired the one-contract design. | — |
| `Descend.narrow_aut_invariant` | 1019-1033 | §Stage-2 An EQUIVARIANT narrowing is invariant under every colouring-preserving automorphism (`α·adj = adj`, `α·χ = χ` turn equivariance into `narrow = α · narrow`). | — |
| `Descend.narrow_eq_branches_of_orbit` | 1035-1058 | §Stage-2 ★★ THE NON-COLLAPSE THEOREM: an equivariant narrowing CANNOT FIRE on a cell that is a single orbit — a nonempty invariant subset of one orbit is the whole orbit. So FORCE provably cannot fire on a symmetric cell and CONSUME fires exactly there: the two contract routes have COMPLEMENTARY, NON-OVERLAPPING firing domains, and the design does not collapse into GI ∈ P. Graphs where neither fires are the residue. | — |
| `Descend.ncol` | 1068-1069 | §Stage-2 The number of colour classes — the descent's progress measure (discrete ⟺ `ncol = n`). | Definition |
| `Descend.ncol_le` | 1071-1073 | §Stage-2 There are at most `n` colour classes. | — |
| `Descend.discrete_of_ncol_eq` | 1075-1079 | §Stage-2 `n` colour classes ⟹ the colouring is discrete (pigeonhole) — the base case of totality. | — |
| `Descend.ncol_lt_indivOne_of_partner` | 1081-1109 | §Stage-2 Individualizing a vertex with a same-coloured PARTNER strictly increases the colour count — the partner form is exactly the hypothesis the widened `Reaches.step` and `Select.NodeProper` carry, so the sel descent's totality rides on this generalization. | — |
| `Descend.ncol_lt_indivOne` | 1111-1114 | §Stage-2 The branch-list form, now a corollary of the partner form: individualizing a branch vertex strictly increases the colour count, so the descent makes progress at every level. | — |
| `Descend.RefineSplits` | 1116-1120 | §Stage-2 The refiner genuinely REFINES — it never merges two colour classes. This is what rules out the degenerate constant refiner (which is `RefineEquivariant` by `rfl` and would flag on every graph), so it is the hypothesis that earns NON-VACUITY. | Definition |
| `Descend.ncol_le_refine` | 1122-1146 | §Stage-2 A genuinely-refining round never loses colour classes. | — |
| `Descend.NarrowProper` | 1148-1152 | §Stage-2 The resolver's narrowing stays inside the branch list and never empties it. Both intended instances satisfy this (consume keeps an orbit representative; force keeps the determined branch). | Definition |
| `Descend.narrowProper_deferAll` | 1154-1155 | §Stage-2 The baseline resolver is proper. | — |
| `Descend.NarrowProperAt` | 1157-1163 | **Properness at ONE graph.** `descend_ne_none` never uses the resolver's properness at any graph other than the one it descends on, so totality is really a *per-graph* statement. §Load-bearing for ③: whether a graph is handled is a property of **that graph**, so the residue predicate must not be forced to quantify over all graphs. Definition. | Definition |
| `Descend.narrowProperAt_of_narrowProper` | 1165-1167 | Global properness gives properness at every graph. | — |
| `Descend.descend_ne_none_at` | 1169-1193 | Totality at one graph — the per-graph form of `descend_ne_none`. | — |
| `Descend.canonForm?_ne_none_at` | 1195-1199 | **③-facing totality**: the descent answers on a graph whose resolver is proper *there*. | — |
| `Descend.Reaches` | 1211-1223 | **The descent's reachable node colourings**, over-approximated resolver-independently: the refined root, closed under "individualize a NON-SINGLETON-CELL vertex (the partner form — widened 2026-07-17 from the least cell so SEL-descents are covered) of a non-discrete node, then refine". The honest domain of any per-node capability claim (`Residue.Handled`, `Select.HandledS`) — strengthening a resolver only shrinks the true visit set. | Inductive |
| `Descend.descend_ne_none_reaches` | 1225-1256 | **Totality from properness on the REACHED set only** — the `∀ χ` of `descend_ne_none_at` was never needed; the induction re-establishes reachability for each child via the subset half. | — |
| `Descend.canonForm?_ne_none_reaches` | 1258-1267 | **③-facing totality, reached-set form:** the descent answers on a graph whose resolver is proper at every *reached* node. Strictly more applicable than `canonForm?_ne_none_at`; what `Residue.answers_of_handled` rides on. | — |
| `Descend.descend_ne_none` | 1269-1295 | §Stage-2 ★ TOTALITY: with a genuinely-refining refiner and a proper resolver the descent ALWAYS REACHES A LEAF (fuel suffices whenever `n ≤ ncol χ + fuel`). | — |
| `Descend.canonForm?_ne_none` | 1297-1302 | §Stage-2 ★ THE CANONIZER ANSWERS — `canonForm?` never flags, so the Stage-2 capstone is about a canonizer that COMPUTES rather than one that flags on everything. Fuel exhaustion is thereby a pure DEPTH bound, leaving `none` free for its real (Stage 4) mutual-stall meaning. | — |
## ChainDescent/Refine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Refine.rankNat_strict_mono` | 63-75 | §1 `vertexRankNat` is strictly monotone in the colour value. | — |
| `Refine.vertexRankNat_eq_iff` | 77-90 | §1 Rank compression preserves the partition: two vertices share a rank iff they share a colour. This is why renumbering a colouring is canonical — same fibres, same order. | — |
| `Refine.vertexRankNat_transport` | 92-111 | §1 Rank compression transports along a relabelling (the rank counts strictly-smaller vertices, and a permutation is a bijection of that set). | — |
| `Refine.constP` | 127-129 | §2 The constant pair-matrix. The descent's refiner sees only `(adj, χ)`, and a constant `P` transports trivially — so the `PMatrix` layer contributes no obligation. | Definition |
| `Refine.keyOf` | 131-133 | §2 The refinement KEY of a vertex: its old colour followed by its sorted signature. Already a `List Nat` — no `Encodable.encode` is ever formed. | Definition |
| `Refine.keyLt` | 135-136 | §2 Strict lexicographic order on refinement keys, computable — built on `Descend.lexLeList`, which is already proved a total order. | Definition |
| `Refine.keyLt_irrefl` | 138-139 | §2 Irreflexivity of the strict key order. | — |
| `Refine.keyLt_trans` | 141-147 | §2 Transitivity of the strict key order. | — |
| `Refine.keyLt_of_ne` | 149-159 | §2 Distinct keys are strictly comparable — the totality half of the order, which is what makes the rank well-defined. | — |
| `Refine.refineRound` | 161-164 | **★ THE ENCODE-FREE ROUND.** Recolour each vertex by the RANK OF ITS KEY among all keys. No `Encodable.encode` anywhere — colours land in `0..n-1` by construction. This is the round `descend`'s `refine` parameter was left open for. | Definition |
| `Refine.refineRound_lt` | 166-179 | §2 Colours never blow up (`< n`) — the whole point of the encode-free fork. | — |
| `Refine.refineRound_strict_mono` | 181-194 | §2 The round's colour is strictly monotone in the key. | — |
| `Refine.refineRound_eq_iff` | 196-207 | §2 The round has the same partition as the key: equal rank ⟺ equal key. | — |
| `Refine.refineRound_splits` | 209-213 | §2 **The round only REFINES** — it never merges two colour classes. The per-round half of `RefineSplits`, hence of totality. | — |
| `Refine.keyOf_transport` | 215-224 | §2 The refinement key transports along a relabelling (rides `sigKey_transport_iso`; the `PMatrix` hypothesis is `rfl` because `constP` is constant). | — |
| `Refine.refineRound_equivariant` | 226-254 | §2 **The round is EQUIVARIANT** — it commutes with relabelling. The per-round half of `RefineEquivariant`, hence of ①b. | — |
| `Refine.warmRefineR` | 258-260 | §3 Encode-free warm refinement: `n` encode-free rounds. The colouring the descent actually uses. | Definition |
| `Refine.iterate_splits` | 262-271 | §3 Iterating the round still only refines — lifts `refineRound_splits` through the `n` rounds. | — |
| `Refine.iterate_equivariant` | 273-283 | §3 Iterating the round preserves equivariance — lifts `refineRound_equivariant` through the `n` rounds. | — |
| `Refine.encodeFree` | 285-288 | **★ THE REFINER.** The encode-free warm round packaged as `descend`'s `Refiner`, carrying the cost model's own refinement cost. This is the instance the object's `refine` parameter was left open for. | Definition |
| `Refine.refineV_encodeFree` | 290-291 | §3 The refiner's value projection is `warmRefineR` (definitional). | `@[simp]` |
| `Refine.refineEquivariant_encodeFree` | 293-299 | **★ OBLIGATION 1 DISCHARGED.** The refiner is EQUIVARIANT — this is the hypothesis all of `①b` (`isoInvariantOpt_canonForm?`) had been carrying. | — |
| `Refine.refineSplits_encodeFree` | 301-305 | **★ OBLIGATION 2 DISCHARGED.** The refiner genuinely REFINES — this is what makes the descent TOTAL (`canonForm?_ne_none`), i.e. the flag is never a fuel artefact. | — |
| `Refine.roundVec` | 329-334 | §4 One encode-free round on MATERIALISED data: every vertex's key is computed once (otherwise `sigKey`, and with it the whole signature multiset, is rebuilt `n²` times per round). | Definition |
| `Refine.roundVec_get` | 336-338 | §4 The materialised round agrees pointwise with `refineRound`. | — |
| `Refine.roundVec_ofFn` | 340-345 | §4 The materialised round agrees with `refineRound` as a whole vector — the step lemma for `iterate_roundVec`. | — |
| `Refine.ColData` | 347-351 | §4 A **materialised** colouring. Its type is deliberately **not a function type**: Lean eta-expands a definition to the arity of its type, so a `Colouring`-valued definition is recomputed on every colour lookup. Wrapping the vector is what makes it a shared value. | Structure |
| `Refine.warmRefineVec` | 353-356 | §4 The warm round, **materialised** — returns `ColData` (a value), not a `Colouring` (a function). This is what makes the refined vector computed **once** rather than per colour lookup; see the sharing trap in §4. | Definition |
| `Refine.ColData.col` | 358-359 | §4 Hand out a colouring backed by the already-forced vector, so lookups are `O(1)` array reads. | Definition |
| `Refine.iterate_roundVec` | 361-370 | §4 Iterating the materialised round agrees with iterating `refineRound`. | — |
| `Refine.warmRefineVec_col_eq` | 372-379 | §4 **The runnable version computes exactly the reasoned-about one.** The proved equation that replaces `@[implemented_by]` — every theorem about `warmRefineR` transfers, and `#eval` cannot lie. | — |
| `Refine.encodeFreeFast` | 381-387 | §4 The runnable refiner — value-equal to `encodeFree` (`encodeFreeFast_eq`), so it inherits every theorem; only the evaluation strategy differs. This is the one to `#eval`. Do **not** refactor `(warmRefineVec adj χ).col` into a `Colouring`-valued definition — that reintroduces the sharing trap. | Definition |
| `Refine.encodeFreeFast_eq` | 389-392 | §4 The runnable refiner equals the reasoned-about one. | — |
| `Refine.refineEquivariant_encodeFreeFast` | 394-395 | §4 The runnable refiner is equivariant (transferred from `encodeFree`). | — |
| `Refine.refineSplits_encodeFreeFast` | 397-398 | §4 The runnable refiner genuinely refines (transferred from `encodeFree`). | — |
| `Refine.refineV_encodeFreeFast` | 400-404 | The runnable refiner's value projection is the reasoned-about round (`warmRefineR`) — the `refineV` face of `encodeFreeFast_eq`; lets a descent node colouring be read as `SealBridge.pathCol` verbatim. | — |
| `Refine.isCanonicalFormOpt_encodeFree` | 412-416 | §5 The canonizer on the encode-free refiner, modulo ONLY the resolver contract (`NarrowTransport`) — the refiner side of `①` is fully discharged. | — |
| `Refine.exhaustive_canonizer` | 418-428 | **★★ THE EXHAUSTIVE CANONIZER IS UNCONDITIONALLY A CANONICAL FORM THAT ANSWERS.** No carried hypotheses whatsoever: `①a`/`①b`/`①c` hold AND the descent never flags. The non-vacuity anchor for the whole track — every resolver added from here only narrows, so it shrinks the flagged residue and can never break this. | — |
## ChainDescent/PerformanceTest.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Refine.C3` | 10-12 | Test fixture: the 3-cycle. | Definition |
| `Refine.C4` | 14-16 | Test fixture: the 4-cycle. | Definition |
| `Refine.C5` | 18-20 | Test fixture: the 5-cycle (vertex-transitive — the worst case for the exhaustive resolver's branching). | Definition |
| `Refine.C6` | 22-24 | Test fixture: the 6-cycle. | Definition |
| `Refine.C7` | 27-29 | Test fixture: the 7-cycle. | Definition |
| `Refine.form` | 37-52 | The canonical form as a comparable value (via row-major `flatten`, since `Labelled n` is a function and has no `DecidableEq`). Used by the `#guard` regression checks. | Definition |
| `Refine.P5` | 53-54 | Test fixture: the 5-path — non-isomorphic to `C5`, used to check the canonizer actually distinguishes. | Definition |
| `Refine.rotP` | 68-71 | The cyclic rotation `i ↦ i + 1` of `Fin n` — a genuine automorphism source for cycles. | Definition |
| `Refine.rotSupply` | 72-76 | The rotation oracle **supply** for `Consume.consume`. Untrusted, like every supply: it verifies at the root and is *rejected* one level down, where individualization breaks the rotation symmetry. | Definition |
| `Refine.formC` | 77-103 | The canonical form computed with the **oracle** (`consume`) resolver, as a comparable value. | Definition |
| `Refine.F12` | 120-126 | A 3-regular graph on 12 vertices whose 1-WL leaves a **single cell of size 12** and whose cells are **not orbits** — the rigid case, where `force` fires (root fan-out 12 → 1). | Definition |
| `Refine.formF` | 127-156 | The canonical form computed with the **force** (`forceBy lookaheadKey`) resolver, as a comparable value. | Definition |
| `Refine.formM` | 178-219 | The canonical form under the **mixed** resolver, as a comparable value (regression-gate helper). | Definition |
| `Refine.dihSupply` | 229-233 | The **full** automorphism supply for a cycle (`Aut(Cₙ) = Dₙ = ⟨rotation, reflection⟩`) — regression-gate helper. The rotation-only supply is *incomplete*, and the guarded mixed descent correctly **flags** on it. | Definition |
| `Refine.gForce` | 234-250 | Guarded **force** canonical form (no supply ⟹ equivariant narrowing ⟹ its flag is iso-invariant). Regression-gate helper. | Definition |
| `Refine.gMix` | 251-259 | Guarded **mixed** canonical form with a supply that really generates `Aut(Cₙ)`. Regression-gate helper. | Definition |
| `Refine.gMatch` | 307-330 | Guarded mixed canonical form with the **structural** cascade-oracle supply (no hand-supplied generators). Regression-gate helper. | Definition |
| `Perf.F12` | 38-44 | The **Frucht graph** — smallest asymmetric cubic graph; 1-WL leaves one cell of 12. Kept **off the build path** (`Regression.G8` covers the same property 8× cheaper); it is the honest large-`n` cost sample. Definition. | Definition |
| `Perf.C7` | 46 | The 7-cycle (large-`n` symmetric sample, off the build path). Definition. | Definition |
| `Perf.gForce` | 73-83 | Guarded force form (perf file). Definition. | Definition |
| `Perf.gMatch` | 87-99 | Guarded mixed form with the structural supply (perf file). Definition. | Definition |
| `Perf.gDeep` | 123-132 | — | Definition |
| `Perf.gPartialFold` | 143-146 | The fold end-to-end **ANSWER**: guarded mixed descent, `constKey` + `partialMatchSupply 0`, `n = 24` — a full canonical form in ~3.5 min interpreted. | Definition |
| `Perf.gDeepFold` | 148-153 | The fold end-to-end **FLAG**: the same descent with `deepMatchSupply 0` stalls at the root copies cell. | Definition |
| `Perf.fold4Swapped` | 158 | Cross-copy relabelling of the fold — the supply-level `①c` observation's graph. | Definition |
| `Perf.fold4SwappedRoot` | 159-161 | Its materialized root (trap #1). | Definition |
| `Perf.vfold3` | 176-178 | The `s = 3` mirror-tied vertical cover (n = 15) — the F2a measurement graph. | Definition |
| `Perf.vfold3Root` | 180-190 | Materialized root (trap #1). | Definition |
| `Perf.vfold3Swapped` | 194 | Cross-copy relabelling — the supply-level `①c` observation's graph. | Definition |
| `Perf.vfold3SwappedRoot` | 195-197 | Its materialized root (trap #1). | Definition |
| `Perf.wcyc15` | 207 | Weighted `C₁₅` — `Aut = Z₅`: 25/25 seeds complete to order-5 rotations, narrow → 1. | Definition |
| `Perf.wcyc15Root` | 208-213 | Materialized root (trap #1). | Definition |
| `Perf.wcyc27` | 217 | Weighted `C₂₇` — `Aut = Z₉`: odd part 9 ≥ 7 (no C# path at any size) and height 2 (9 = 3²). | Definition |
| `Perf.wcyc27Root` | 218-225 | Materialized root (trap #1). | Definition |
| `Perf.vringB` | 231-239 | The voltage-ring edge predicate: rigid 6-vertex core, cross edge `(c,a)–(c+1,b)` = voltage 1; asymmetric pendant paths kill the WL reversal ghost and every reflection. | Definition |
| `Perf.vring18` | 241 | `Z₃` voltage-ring cover (the true tower-gadget shape), deck `Z₃` exactly, `Aut` involution-free. | Definition |
| `Perf.vring18Root` | 242-247 | Materialized root (trap #1). | Definition |
| `Perf.gDeckCycle` | 251-256 | End-to-end fused descent over `foldSupply ++ deckSupply` on the involution-free cycle — answers. | Definition |
| `Perf.wrB` | 324-328 | The WREATH witness edge predicate: `s` copies of the C₄+pendant core on a copy cycle, matched ONLY on the mirror-FIXED fibers {0,2,4} — each copy's mirror is an INDEPENDENT automorphism (`Aut ⊇ Z₂^s ⋊ D_s`). | Definition |
| `Perf.wr3` | 330 | `wrB` at s = 3 (n = 15) — the C2 wreath witness. Measured: `deck2Supply` FIRES on it (the identity-default finding, §12), falsifying the earlier claim that wreath gauges stall. | Definition |
| `Perf.wr3Root` | 331-341 | Root colouring of `wr3` (materialised through `ColData`, trap #1). | Definition |
| `Perf.onLine` | 369 | — | Definition |
| `Perf.inS` | 371-376 | — | Definition |
| `Perf.mpfg` | 378-381 | — | Definition |
| `Perf.mpB` | 383-386 | — | Definition |
| `Perf.mp7` | 388 | — | Definition |
| `Perf.mpRoot` | 389 | — | Definition |
| `Perf.mk42` | 390-393 | — | Definition |
| `Perf.wSupp` | 395-397 | — | Definition |
| `Perf.gaugeFun` | 399-413 | — | Definition |
| `Perf.mpN2` | 416-420 | — | Definition |
| `Perf.mfG` | 422-424 | — | Definition |
| `Perf.cont1` | 426-433 | — | Definition |
| `Perf.mpPin` | 454-461 | — | Definition |
| `Perf.transFun` | 492-498 | — | Definition |
| `Perf.orbitOf` | 500-501 | — | Definition |
| `Perf.mpKernelGens` | 503-508 | — | Definition |
| `Perf.mpDeepenGens` | 533-541 | — | Definition |
## ChainDescent/Consume.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Consume.IsColAut` | 50-53 | §1 **The verification gate.** `α` is an automorphism of `adj` that also preserves the colouring `χ` — the only thing `consume` ever trusts. | Definition |
| `Consume.decidableIsColAut` | 55-58 | §1 The gate is **decidable** (a finite edge-by-edge test), which is what makes an untrusted oracle supply safe to consume. | Instance |
| `Consume.IsColAut.relabel` | 60-69 | §1 A verified automorphism fixes the graph: `relabelAdj α adj = adj`. Half of what turns `descend_transport` into a same-graph branch equality. | — |
| `Consume.IsColAut.transport` | 71-76 | §1 A verified automorphism fixes the colouring: `transportColouring α χ = χ`. The other half. | — |
| `Consume.IsColAut.one` | 78-80 | §1 The identity is colouring-preserving — the base of the orbit search. | — |
| `Consume.IsColAut.comp` | 82-92 | §1 Colouring-preserving automorphisms are **closed under composition**, so a word in the verified generators is itself verified. This is what lets the orbit BFS accumulate a single witness. | — |
| `Consume.IsColAut.inv` | 94-103 | Colouring-preserving automorphisms are **closed under inverse** — completing `one`/`comp` into a subgroup. Needed by orbit-pruning, where a candidate reconstructed as a product/conjugate of verified generators (the P3b license) must itself certify as an automorphism. | — |
| `Consume.Reach` | 110-112 | §2 **The covering witness.** Some verified colouring-preserving automorphism carries `b` to `m`. | Definition |
| `Consume.Reach.rfl'` | 114-116 | §2 Every vertex is reachable from itself. | — |
| `Consume.Reach.step` | 118-122 | §2 Reachability extends along a verified generator — the induction step of the orbit search's soundness. | — |
| `Consume.Reach.colour` | 124-129 | §2 Reachable vertices share a colour, so an orbit never leaves the branch cell. This is why `consume`'s narrowing stays inside `branches`. | — |
| `Consume.orbStep` | 133-135 | §3 One BFS round: close the current vertex set under the verified generators. | Definition |
| `Consume.mem_orbStep_of_mem` | 137-141 | §3 The BFS step is extensive — it never loses a vertex it already had. | — |
| `Consume.orbit` | 143-146 | §3 The orbit of `b` under the verified generators (`n` BFS rounds). A *short* search only keeps more branches, never fewer, so its depth carries no soundness obligation. | Definition |
| `Consume.mem_iterate_self` | 148-154 | §3 `b` survives every BFS round. | — |
| `Consume.mem_orbit_self` | 156-158 | §3 `b` is in its own orbit — so `rep b` has something to be the minimum of. | — |
| `Consume.reach_of_mem_orbit` | 160-181 | §3 **Soundness of the orbit search.** Everything it finds is genuinely reachable by a verified automorphism — whatever the generator list was. | — |
| `Consume.minList` | 185-188 | §4 Least element of `b :: l` (computable). | Definition |
| `Consume.minList_mem` | 190-206 | §4 The minimum is the seed or a list member — so `rep b` always lies in `b`'s orbit. | — |
| `Consume.rep` | 208-213 | §4 **The orbit representative of `b`.** The choice is deliberately *not* equivariant (orbit members are indistinguishable to refinement); only its *result* transports, which is exactly what the `Covering` route licenses. | Definition |
| `Consume.rep_mem_orbit` | 215-220 | §4 The representative lies in the orbit it represents. | — |
| `Consume.reach_rep` | 222-225 | §4 **The covering witness, packaged.** The representative is reachable from the branch it replaces. | — |
| `Consume.Supply` | 229-236 | §5 **An oracle supply — UNTRUSTED.** Candidate permutations (`matchOracle` / the cascade oracle / the solver kernel), carrying *no* proof obligation. | `abbrev` |
| `Consume.gens` | 238-240 | The supply's **value** projection (the candidate generators). Definition. | Definition |
| `Consume.supplyCost` | 242-243 | The supply's **cost** projection — the oracle's own work, now billed to the descent. Definition. | Definition |
| `Consume.verified` | 245-247 | §5 The supply filtered through the decidable `IsColAut` check. Everything downstream uses only this. | Definition |
| `Consume.isColAut_of_mem_verified` | 249-254 | §5 **Everything surviving the filter is a genuine colouring-preserving automorphism.** The single lemma that makes an untrusted supply harmless. | — |
| `Consume.consume` | 256-265 | §5 **★ THE ORACLE RESOLVER.** Keeps one representative per orbit of the branch cell under the *verified* automorphisms, discarding the rest. | Definition |
| `Consume.narrow_consume` | 267-268 | §5 The narrowing `consume` performs, unfolded. | `@[simp]` |
| `Consume.consume_cost` | 270-274 | §**The oracle's own work is charged.** Supply cost + one edge-by-edge verification per candidate + one orbit BFS per branch. Previously `Supply` was cost-free, so the T-C "work per node" question — *the* open oracle problem — was invisible to `②`. | — |
| `Consume.exists_targetColour_of_mem` | 278-286 | §6 A nonempty branch list has a target colour, and its members carry it. | — |
| `Consume.narrow_consume_subset` | 288-298 | §6 **The narrowing stays inside the branch cell** — orbits cannot leave it, since a verified automorphism preserves the colouring. | — |
| `Consume.narrow_consume_ne_nil` | 300-309 | §6 The narrowing is never empty on a non-discrete node. | — |
| `Consume.narrowProper_consume` | 311-314 | §6 `consume` is a **proper** narrowing (inside the cell, never empty) — the hypothesis totality (`canonForm?_ne_none`) needs. | — |
| `Consume.branchVal_eq_of_isColAut` | 316-329 | §6 **★★ THE COVERING WITNESS.** A verified automorphism makes two branches *value-equal*: it is `descend_transport` at `σ = α`, where `relabelAdj α adj = adj` degenerates the transport equation into an equality between two branches of the *same* graph. This is where the fuel-graded `CoveringAt` earns its keep. | — |
| `Consume.coveringAt_consume` | 331-361 | §6 **★★★ `consume` IS SOUND — for EVERY supply, however wrong.** The narrowed aggregate equals the full one, because each discarded branch is value-equal to the kept representative of its orbit. A broken oracle costs branches, never correctness. | — |
| `Consume.narrowTransport_consume` | 363-366 | §6 `consume` satisfies the resolver contract (`NarrowTransport`), for every supply. | — |
| `Consume.consume_canonizer` | 370-382 | §7 **★★★ THE ORACLE-DRIVEN CANONIZER.** `①a`/`①b`/`①c` hold and the descent never flags, **with no hypothesis on the oracle at all**. | — |
| `Consume.consume_canonizer_fast` | 384-391 | §7 The same, on the runnable `encodeFreeFast` refiner. | — |
| `Consume.Closed` | 405-407 | A vertex set is closed under the generators — the orbit BFS's fixpoint condition. Definition. | Definition |
| `Consume.mem_orbStep_iff` | 409-421 | Membership in one BFS round: already present, or one generator step away. | — |
| `Consume.mem_orbStep_of_closed` | 423-427 | A closed set is a **fixpoint** of the BFS step. | — |
| `Consume.mem_iterate_of_closed` | 429-440 | Once closed, always closed: iterating the BFS from a closed set changes nothing. | — |
| `Consume.iterate_subset_succ` | 442-448 | The BFS is monotone — a round never loses a vertex. | — |
| `Consume.card_lt_of_not_closed` | 450-461 | **Every non-closed BFS round strictly grows the reached set** — the monovariant behind convergence. | — |
| `Consume.orbit_closed` | 463-495 | §**THE ORBIT BFS CONVERGES — `n` rounds suffice.** If round `n` were not closed, all `n+1` rounds would have strictly grown the set, forcing `> n` distinct vertices into `Fin n`. Without this the BFS is only a depth-`n` approximation, `rep` need not be constant on an orbit, and **consume could silently keep every branch** — the whole firing story rests on this. | — |
| `Consume.WordReach` | 499-504 | `m` is reachable from `b` by a **word in the supply's generators** (stronger than `Reach`, which asks only that *some* automorphism does it). Definition. | Inductive |
| `Consume.mem_orbit_of_wordReach` | 506-512 | The orbit list contains everything a word reaches — what convergence buys: the BFS *is* the whole orbit, not an approximation of it. | — |
| `Consume.minList_le_seed` | 516-524 | The running minimum never exceeds its seed. | — |
| `Consume.minList_le` | 526-536 | The running minimum is `≤` every list element. | — |
| `Consume.rep_eq_of_orbit_eq` | 538-548 | §**`rep` IS CONSTANT ON AN ORBIT.** Two vertices reaching the same set get the same representative, so consume maps them to **one** branch rather than two. This is exactly what `NarrowProper` could never give. | — |
| `Consume.CellIsOrbit` | 552-558 | **The oracle's FIRING obligation, stated.** The branch cell is a single orbit of the supply's *verified* generators. A `②` obligation, never a `①` one — but not optional: without it consume defers and the descent branches. Definition. | Definition |
| `Consume.orbit_subset_branches` | 560-566 | An orbit never leaves the branch cell (a verified automorphism preserves the colouring). | — |
| `Consume.closed_inv` | 579-593 | A finite forward-closed set is **inverse-closed** (a generator permutes it, so it maps it *onto* itself). What supplies the inverse words the orbit symmetry needs. | — |
| `Consume.mem_of_mem_orbit_of_closed` | 595-607 | **Minimality** — the orbit is contained in every closed set containing its seed. | — |
| `Consume.orbit_closed_inv` | 609-612 | The orbit is inverse-closed (convergence + `closed_inv`). | — |
| `Consume.self_mem_orbit_of_wordReach` | 614-625 | Reachability is **symmetric** on orbits: if a word takes `u` to `w`, then `u` lies in `w`'s orbit. | — |
| `Consume.orbit_eq_of_wordReach` | 627-634 | Connected vertices have the **same orbit set** — both inclusions, so `rep` can be compared. | — |
| `Consume.rep_eq_of_wordReach` | 636-642 | §**THE GRADED FIRING LEMMA — consume merges exactly what its generators connect**, with **no hypothesis on the supply**. One proved automorphism merges one pair; the whole cell's symmetry collapses the cell. **Partial power, partial progress** — the statement the perfect-endpoint singleton theorem cannot make. | — |
| `Consume.rep_const_of_cellIsOrbit` | 644-647 | On a cell that is one orbit, every branch has the same representative. | — |
| `Consume.dedup_map_length_one` | 649-669 | The dedup of a constant map over a nonempty list is a singleton — the shape both firing theorems land in. | — |
| `Consume.dedup_map_length_lt` | 671-699 | **A merge is a strict shortening** — two distinct branches with the same representative ⟹ the deduplicated narrowing is strictly shorter. One merged pair is one branch saved. | — |
| `Consume.consume_singleton_of_cellIsOrbit` | 701-706 | §**CONSUME FIRES — a symmetric cell costs ONE branch, not `|cell|`.** If the cell is a single orbit of the verified generators, the narrowing is a **singleton**: the fan-out is gone. The completeness counterpart to `consume_canonizer` (which is sound for *every* supply, including a useless one). | — |
| `Consume.consume_narrows_of_wordReach` | 708-717 | §**CONSUME FIRES ON PARTIAL POWER.** A *single* verified automorphism between two distinct branches already shortens the narrowing — the cell need **not** be one orbit. The oracle does not have to be perfect to be useful: it is rewarded for exactly the symmetry it can prove, and penalized for nothing. | — |
| `Consume.wordReach_of_mem_iterate` | 730-745 | Everything the orbit BFS reaches is reached by a **word** in the generators (the converse of `mem_orbit_of_wordReach`). | — |
| `Consume.mem_orbit_iff_wordReach` | 747-750 | The orbit list **is** the word-reachable set — not a depth-`n` approximation (convergence). | — |
| `Consume.decidableWordReach` | 752-760 | ★ `WordReach` IS DECIDABLE and the decision procedure is the orbit BFS itself — `orbit` is a computable `n`-round fixpoint and `mem_orbit_iff_wordReach` is already proved, so this is one `decidable_of_iff`. No `Classical.dec`, no search over `Equiv.Perm`. This is what makes a supply-guarded key EXECUTABLE. | Instance |
| `Consume.decidableCellIsOrbit` | 762-767 | Hence `CellIsOrbit` is decidable — two bounded `∀`s over the branch cell, each decided by the BFS. Honest cost: `≤ |cell|²` orbit closures. | Instance |
| `Consume.WordReach.trans` | 769-774 | Word-reachability is transitive. | — |
| `Consume.WordReach.symm` | 776-779 | Word-reachability is symmetric (the orbit is inverse-closed, `closed_inv`). | — |
| `Consume.wordReach_rep` | 781-783 | A branch reaches its own orbit representative. | — |
| `Consume.rep_eq_iff_wordReach` | 785-794 | **★★★ `rep` MERGES EXACTLY THE ORBIT.** Two branches share a representative **iff** the verified generators connect them. The `←` is `rep_eq_of_wordReach`; the `→` says consume merges **nothing more** — the least-index choice adds no spurious identifications. Hence the narrowing's *length* **counts orbits**, which is exactly what `Stall.StallEquivariant` needs and a merely-sound `rep` could never give. | — |
| `Consume.isColAut_conj_iff` | 798-820 | **The verification check transports.** `α` is a colouring-preserving automorphism of `(adj, χ)` iff its `σ`-conjugate is one of `(σ·adj, σ·χ)` — why a *structural* supply can be equivariant at all. | — |
## ChainDescent/Force.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Force.kmin?` | 90-96 | §1 The lex-least key of a list (`none` on empty), under the proved total order `lexLeList`. | Definition |
| `Force.kmin?_eq_none_iff` | 98-109 | §1 `kmin?` flags exactly on the empty list. | — |
| `Force.kmin?_mem` | 111-127 | §1 The minimum is one of the candidates — so the forced narrowing is never empty. | — |
| `Force.kmin?_le` | 129-166 | §1 The minimum really is `≤` every candidate. | — |
| `Force.kmin?_congr_mem` | 168-192 | §1 **`kmin?` depends only on the SET of candidates.** What lets the narrowing survive the fact that the branch list is built in *index* order. | — |
| `Force.Key` | 196-205 | §2 A **structural vertex key** — the invariant a forcing rule ranks branches by. (`List Nat`, so it is compared with the already-proved total order `lexLeList`.) | `abbrev` |
| `Force.keyV` | 207-209 | The key's **value** projection — what the ranking compares. Definition. | Definition |
| `Force.keyCost` | 211-213 | The key's **cost** projection — what `forceBy` is billed per evaluation. Definition. | Definition |
| `Force.KeyEquivariant` | 215-220 | §2 **★ THE ONLY ① OBLIGATION OF A FORCE RESOLVER.** The key commutes with relabelling — i.e. it never breaks ties by vertex index. Everything else about the rigid solver (P1/P3) is a ②/firing matter. | Definition |
| `Force.keepMin` | 222-227 | §2 Keep exactly the branches attaining the least key. | Definition |
| `Force.keepMin_none` | 229-232 | §2 No branches (a discrete node): nothing to narrow. | — |
| `Force.keepMin_some` | 234-238 | §2 The narrowing is the fibre of the least key. | — |
| `Force.forceBy` | 240-248 | §2 **★ THE FORCE RESOLVER.** Keep the branches of least key. The discards are genuinely *different* subproblems — the aggregate **changes** — but consistently on `G` and `σ·G`, which is all iso-invariance needs. **No global lex-min, no knowledge of the answer.** | Definition |
| `Force.narrow_forceBy` | 250-251 | §2 The narrowing `forceBy` performs, unfolded. | — |
| `Force.forceBy_cost` | 253-255 | §**The resolver is billed for every key evaluation.** Load-bearing: with a cost-free `Key`, the contract admits an **exponential** resolver no theorem objects to (take the key to be the subtree's own canonical form — equivariant, maximally firing, exhaustive). "It fires" only means something against a key charged for what it computes. | — |
| `Force.filter_map_comm` | 259-267 | §3 Mapping then filtering is filtering-by-the-composite then mapping. | — |
| `Force.narrowEquivariant_forceBy` | 269-304 | §3 **★★ THE FORCE ROUTE, DISCHARGED.** An equivariant key gives an equivariant narrowing, hence the whole resolver contract. This is the *entire* ① content of the rigid solver. | — |
| `Force.mem_keepMin_iff` | 306-336 | **The forced set is exactly the argmin of the key over the cell.** Every statement about force's firing is read off this one characterization. | — |
| `Force.narrowProper_forceBy` | 340-363 | §4 The forced narrowing stays inside the branch cell and never empties it — the hypothesis totality needs. | — |
| `Force.keyV_aut_invariant` | 380-388 | §**THE CEILING — an equivariant key is CONSTANT ON ORBITS.** A colouring-preserving automorphism cannot change a vertex's key, so force is blind to *precisely* the distinctions consume handles and can never cut inside an orbit. | — |
| `Force.mem_keepMin_of_aut` | 390-400 | **The forced set is a union of orbits** — an orbit representative of a kept branch is itself kept. The lemma that makes the mixed resolver sound: consuming *inside* the forced set never escapes it. | — |
| `Force.forceBy_singleton_of_separating` | 402-438 | §**THE FLOOR — a SEPARATING key removes ALL branching.** If the key distinguishes the cell's vertices pairwise, `forceBy` narrows it to a **single** branch. This is what makes the force route *useful* rather than merely sound, and it is exactly what the rigid solver's key must deliver — §11.12's P1/P3, on the `②`/firing side of the ledger. | — |
| `Force.keepMin_nodup` | 440-445 | The forced set is nodup (a filter of the nodup branch list) — needed to measure it. | — |
| `Force.forceBy_discards_of_key_ne` | 447-462 | Force discards a branch iff two branches get different keys — firing is *equivalent* to the key being non-constant on the cell. | — |
| `Force.forceBy_narrows_of_key_ne` | 464-479 | §**FORCE FIRES ON PARTIAL POWER.** A key that separates *any two* branches already shortens the narrowing — it need **not** separate the whole cell. A rigid solver that handles part of its residue contributes part of the saving, with no cliff. | — |
| `Force.force_canonizer` | 483-498 | §5 **★★★ THE FORCE-DRIVEN CANONIZER.** ①a/①b/①c and totality, modulo nothing but `KeyEquivariant key`. Note it computes a *different but equally valid* canonical form, not the exhaustive branch-min — which is precisely what frees the rigid solver from having to know the answer. | — |
| `Force.force_canonizer_fast` | 500-507 | §5 The same, on the runnable `encodeFreeFast` refiner. | — |
| `Force.forceBy_no_narrowing_on_orbit` | 509-520 | §5 **★★ NO GI ∈ P COLLAPSE.** `forceBy` cannot fire on a cell that is a single orbit: forcing is available only where the cell is genuinely *not* an orbit — exactly where **consume** cannot fire. Complementary, non-overlapping firing domains. | — |
| `Force.lookData` | 532-539 | §6 The refinement reached by individualizing `v`, as **materialised data**. ⚠ Returns `ColData`, not `Colouring` — a `Colouring`-valued definition is eta-expanded to full arity and re-runs the refinement on *every* colour lookup (`Refine.lean` §4). | Definition |
| `Force.lookData_col` | 541-545 | §6 The look-ahead colouring equals `warmRefineR`, so reification does not affect any proof. | — |
| `Force.lookaheadKey` | 547-568 | §6 **A concrete key that provably FIRES.** Individualize `v`, refine, and rank `v` by the *leaf it reaches* (falling back to a cell-size histogram when it does not discretize). Measured: root fan-out 12→1 on a rigid cubic graph; provably no narrowing at all on a vertex-transitive one. The cell-size histogram **alone** separates nothing on a rigid graph — the leaf matrix is what does. | Definition |
| `Force.keyV_lookaheadKey` | 570-574 | The look-ahead key's value: rank by the leaf reached if individualization discretizes, else by the cell-size histogram. | `@[simp]` |
| `Force.keyCost_lookaheadKey` | 576-578 | The look-ahead key costs one warm refinement per branch — polynomial, and **charged**. ⚠ Charged honestly it does not *pay*: on `F12` the root's keys alone cost `12·(n³+n²) = 22464`, exceeding the whole exhaustive descent (22477). It fires; it loses. The refinement it computes is the one the child then recomputes. | — |
| `Force.lookData_col_transport` | 580-586 | §6 The look-ahead colouring transports. | — |
| `Force.keyEquivariant_lookahead` | 588-606 | §6 **The look-ahead key is equivariant** — refinement, individualization and discreteness all transport, and both ranking invariants transport (`leafMatrix_transport` is *literal equality*; `cellOf_card_transport`). | — |
| `Force.lookahead_canonizer` | 608-615 | §6 **★ THE LOOK-AHEAD CANONIZER** — a fully concrete, hypothesis-free force-driven canonizer: sound, iso-invariant, complete, and it always answers. | — |
## ChainDescent/Composite.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Composite.forcedSet` | 75-76 | The forced set as a `NarrowFn` — the equivariant intermediate the mixed resolver covers. Definition. | Definition |
| `Composite.forceThenConsume` | 78-88 | §**THE MIXED RESOLVER — both moves at one cell.** Force first (narrow equivariantly to the least-key branches), then consume (one orbit representative among those). `descend` takes ONE resolver, so the interleaved engine (IR §11.11) — which needs *both* moves at the *same* cell, as almost every real residue does — was not instantiable from the two separate instances. Costs are summed, not hidden. Definition. | Definition |
| `Composite.narrow_forceThenConsume` | 90-92 | The composite's narrowing, unfolded: orbit representatives of the least-key branches. | — |
| `Composite.forcedSet_subset` | 94-97 | The forced set sits inside the branch cell. | — |
| `Composite.forcedSet_ne_nil` | 99-103 | The forced set is nonempty on a non-discrete node. | — |
| `Composite.rep_mem_forcedSet` | 112-122 | §**An orbit representative never escapes the forced set.** `KeyEquivariant` makes the key constant on orbits, so the argmin set is a union of whole orbits. Without this, consume could pick a representative force had discarded and the covering argument would collapse — this is the lemma the composite lives or dies on. | — |
| `Composite.narrowFnEquivariant_forcedSet` | 126-129 | The forced set is an equivariant intermediate (it *is* `narrow (forceBy key)`). | — |
| `Composite.coveringOfAt_forceThenConsume` | 131-165 | **The composite covers the forced set.** Consume's discards *within* it are value-equal to the kept representative (`descend_transport` at an automorphism), and that representative is still in the forced set. | — |
| `Composite.narrowTransport_forceThenConsume` | 167-172 | §**THE MIXED RESOLVER MEETS THE CONTRACT** — via the general `CoveringOfAt` route. It is **neither** `Covering` (force changes the aggregate) **nor** `NarrowEquivariant` (consume's representative choice is deliberately non-equivariant), which is why the generalized third route had to exist. | — |
| `Composite.narrowProper_forceThenConsume` | 174-190 | The composite is a proper narrowing (nonempty, inside the cell) — the totality hypothesis. | — |
| `Composite.composite_canonizer` | 194-207 | §**THE MIXED CANONIZER** — `①a`/`①b`/`①c` plus totality for the interleaved object, modulo **nothing but `KeyEquivariant`**, and *nothing at all* on the oracle supply (which stays untrusted). | — |
| `Composite.composite_canonizer_fast` | 209-216 | The runnable mixed canonizer (`encodeFreeFast` refiner — value-equal, so it inherits everything). | — |
| `Composite.forceThenConsume_singleton_of_cellIsOrbit` | 223-232 | §**FIRING, THE SYMMETRIC CASE.** If the cell is one orbit of the verified generators, the composite narrows it to **one** branch. Force provably *cannot* fire here, so this is consume's domain — and consume closes it completely. | — |
| `Composite.forceThenConsume_singleton_of_separating` | 234-254 | §**FIRING, THE RIGID CASE.** If the key separates the cell, the composite narrows it to **one** branch. Consume cannot fire here, so this is force's domain — and the key closes it completely. This is the precise firing obligation the rigid solver inherits: *separate the cell*. | — |
| `Composite.forceThenConsume_narrows_of_partial` | 285-338 | §**THE ANTI-PERFECTIONISM THEOREM — partial power ⟹ partial progress.** **Any** capability from **either** side (the supply proving one automorphism, or the key separating one pair) **strictly** reduces the fan-out. No threshold, no cliff: each resolver is rewarded for exactly the distinctions it can prove, and the *singleton* theorems are just the total-reward case. ⚠ Needed because those endpoint theorems, read alone, say "only a perfect oracle/key counts" and are silent on the realistic middle. The exhaustive force/consume split then buys **ATTRIBUTION** (`forceThenConsume_stall`): every surviving pair is assignable to one resolver's weakness — a measuring instrument, **not** an impossibility argument (a perfect key *is* GI ∈ P: the route's target, not a barrier). | — |
| `Composite.forceThenConsume_stall` | 340-360 | §**THE RESIDUE, NAMED.** A cell the composite cannot collapse is one where the supply does not connect it **and** the key does not separate it — neither move applies. That is the mutual stall (`②`'s real flag), and those graphs are exactly `UnhandledResidue`. | — |
## ChainDescent/Cost.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Cost.descend_cost_leaf` | 51-54 | A leaf costs one node. | — |
| `Cost.descend_cost_zero` | 56-58 | An unresolved node at zero fuel costs one node (the placeholder flag). | — |
| `Cost.descend_cost_succ` | 60-71 | The branch case's cost: the node, plus the resolver's work, plus — **per surviving branch** — one refinement and the subtree. §The sum is over `narrow`, not `branches`: **what the resolvers discard is never paid for.** | — |
| `Cost.ResolvedAll` | 75-80 | **The resolvers leave no fan-out** — every non-discrete node is narrowed to ≤ 1 branch. The *whole* hypothesis of the polynomial bound, and a statement about **firing**, not soundness. Definition. | Definition |
| `Cost.descend_cost_le_of_resolved` | 82-134 | **THE COST BOUND.** With bounded per-node refiner/resolver work and no residual fan-out, cost is **linear in the fuel** — the descent is a single path of depth ≤ n. | — |
| `Cost.descentCost_le_of_resolved` | 136-146 | §**② FOR THE TOP-LEVEL OBJECT.** A resolved descent costs `O(n·(c₁+c₂))` — **polynomial** whenever the per-node refiner and resolver costs are. The old `n⁴` (`CanonForm.descentCost_le`) was against a *single-path* object (`nbud = n`, assume-VT) and does **not** transfer to a branching one; this is its replacement, proved about the real object. | — |
| `Cost.CellResolved` | 154-158 | A cell the composite resolves: **either** the supply connects it (consume's domain) **or** the key separates it (force's domain). Per-cell, not per-graph — a graph may be handled by consume at one cell and force at the next, which is what the **mixed** resolver is for. Definition. | Definition |
| `Cost.resolvedAll_of_cellResolved` | 160-167 | Every resolved cell is narrowed to a single branch — the firing theorems, applied. | — |
| `Cost.poly_of_cells_resolved` | 169-189 | §**THE ② PAYOFF — POLYNOMIAL ON THE RESOLVED SET.** *A graph every one of whose cells is **either** supply-connected **or** key-separated is canonized in time polynomial in `n`.* With `Composite.composite_canonizer` (sound, iso-invariant, complete, always answers) this is **poly-time canonization on the resolved set** — no hypothesis on the oracle's correctness, none on the key beyond `KeyEquivariant`. The residue is its complement, and `forceThenConsume_stall` *attributes* each residual cell to one side's weakness. ⚠ `ResolvedAll` is **sufficient**, a lower bound on the handled set — **not a wall**: bounded non-stacking fan-out is also polynomial and is not yet captured. | — |
| `Cost.refiner_cost` | 191-195 | The refiner's per-node cost is exactly `n³` — one of the two summands discharged outright. | — |
## ChainDescent/Stall.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Stall.aggregate_nil` | 69-71 | §**The object already HAS a flag channel.** The empty narrowing aggregates to `none`, and `none` propagates to the root — so a resolver can flag by returning `some []`, and the mutual-stall flag needs **no change to `descend`** and no re-proof of ①. | `@[simp]` |
| `Stall.stalled` | 75-80 | **The node has stalled**: the resolvers left ≥ 2 branches in the **target cell**. A **local, structural predicate of the node** — never of the traversal, which is what `①c` requires. ⚠ **Reads as "the LEAST-COLOUR cell stalled", not "the node stalled"**: the target selector (`branches`/`targetColour`) is blind to resolvability, so this can fire on a cell that another cell's resolution would have exposed (**fusion's live bite** — see `Stall` §5b). Fixing it needs a resolver-aware **selector parameter** on `descend`. Definition. | Definition |
| `Stall.guard` | 85-89 | §**THE STALL GUARD** — run the resolver; if it leaves ≥ 2 branches, **flag** instead of branching. Deferral is not a cheap mode of a healthy run, it **is** the failure: every node consumes or forces, and one that can do neither *is* the residue. So the descent is a single path or it stops — there is no exhaustive fallback to be polynomial *about*. Definition. | Definition |
| `Stall.narrow_guard` | 91-96 | The guarded narrowing: empty when stalled, otherwise the underlying resolver's. | — |
| `Stall.guard_cost` | 98-104 | The guard is free (it reads a length) — the guarded resolver costs what the underlying one costs. | — |
| `Stall.narrow_guard_length_le_one` | 110-118 | The guarded narrowing never exceeds one branch — **by construction**. | — |
| `Stall.resolvedAll_guard` | 120-123 | §**`Cost.ResolvedAll` HOLDS BY CONSTRUCTION.** It stops being a hypothesis about the graph and becomes a property of the object: the guard *makes* it true. | — |
| `Stall.descentCost_guard_le` | 125-142 | §**★★★ THE GUARDED DESCENT IS UNCONDITIONALLY POLYNOMIAL.** No hypothesis on the graph, the oracle supply, or the key: the descent is a **single path** of depth ≤ n on every input, because a node the resolvers cannot resolve **flags** rather than branching. This is `poly` **and** `flag` — never `poly` **or** `exponential`. Supersedes the reading of `Cost.descentCost_le_of_resolved` as a conditional bound to be widened. | — |
| `Stall.descentCost_guard_le_encodeFree` | 144-149 | The bound at the built refiner (`c₁ = n³`): polynomial as soon as the resolver is. | — |
| `Stall.StallEquivariant` | 156-162 | **The stall predicate is iso-invariant.** ⚠ **The price of having a flag, and a genuinely new obligation.** `consume`'s supply is *untrusted* because a covering resolver is **value**-invisible — but a **flag is not value-invisible**: `stalled` reads the narrowing's *length*, which depends on how many orbits the supply actually proves. A supply good on `G` and junk on `σ·G` makes `G` answer and `σ·G` flag ⟹ **`①c` false**. Soundness still needs nothing from the supply; the flag needs it **equivariant**. (Counterexample witnessed in `PerformanceTest`.) Definition. | Definition |
| `Stall.stallEquivariant_of_narrowEquivariant` | 164-170 | An **equivariant** narrowing gives stall-equivariance for free (same length up to a permutation) — which is why the **force-only** route pays nothing for its flag. | — |
| `Stall.narrowEquivariant_guard` | 172-184 | The guard preserves `NarrowEquivariant`: both sides stall together, and are otherwise unchanged. | — |
| `Stall.guarded_force_canonizer` | 188-204 | §**★★★ THE FORCE ROUTE, GUARDED — a canonical form that is UNCONDITIONALLY POLYNOMIAL and flags exactly at the mutual stall.** `①a`/`①b`/`①c` modulo nothing but `KeyEquivariant`, *and* a single path on **every** input. It no longer "always answers" (the guard deliberately breaks `NarrowProper`) — **that is the point: it answers or it flags, and it is polynomial either way.** | — |
| `Stall.guarded_choice_transports` | 244-256 | The guarded descent's one choice is **iso-invariant**: select `v` at a node of `G` ⟹ select `σ v` at the corresponding node of `σ·G`. ⛔ **NOT a no-fusion theorem** — an earlier description claimed it dissolved fusion; that was WRONG and is retracted. **Fusion is a dependency of EXPOSURE** (a decision's *type* is not visible until other decisions are resolved: a ring's rigid decisions surface only after `{root, direction}` are consumed; Chang-A has 24 automorphisms certifiable only *after* rigid decisions), not a meta-product over orderings. See `Stall` §5b for fusion's **live bite**: the target-cell selector is blind to resolvability, so the descent can flag on a cell another cell's resolution would have exposed. | — |
| `Stall.narrow_guard_eq_nil_iff` | 268-276 | The guarded descent flags at a node **exactly** when that node stalled — the `③` hook. | — |
## ChainDescent/Residue.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Residue.guardedRef` | 71-73 | The guarded composite's reference narrowing: the forced set, emptied when the node stalls. Definition. | Definition |
| `Residue.narrowFnEquivariant_guardedRef` | 75-86 | The reference transports — given `StallEquivariant` (an equivariant supply; the flag's price, `Stall.StallEquivariant`). | — |
| `Residue.coveringOfAt_guarded` | 88-122 | The guarded composite covers its reference: empty on both sides when stalled, otherwise the composite's own covering argument. | — |
| `Residue.narrowTransport_guarded` | 124-130 | **The guarded MIXED resolver meets the contract** — modulo `KeyEquivariant` + `StallEquivariant`. Needed the general `CoveringOfAt` route: the guarded composite is neither `Covering` nor `NarrowEquivariant`. | — |
| `Residue.guarded_mixed_canonizer` | 132-138 | §**★★★ THE GUARDED MIXED CANONIZER** — sound, iso-invariant, complete, **and unconditionally polynomial** (`Stall.descentCost_guard_le`). The full object: both moves, one cell, a real flag, a real cost bound. | — |
| `Residue.Handled` | 152-164 | **★★ THE BOUNDARY PREDICATE (re-based 2026-07-16 onto `Descend.Reaches`):** at every REACHABLE non-discrete colouring the branch cell is supply-connected (consume) or key-separated (force). Positive, iteratively improvable (family-by-family via `HandledBridge.handled_of_seal`, supply-by-supply via `OrbitPrune.handled_congr`); the residue is its exact complement. The old ∀-all-colourings form was undischargeable in principle (the seal speaks only at committed paths). | Definition |
| `Residue.handled_of_forall` | 166-171 | Compatibility: the old universally-quantified capability (all colourings) still lands — it is strictly stronger than `Handled`. | — |
| `Residue.handled_of_root_discrete` | 173-185 | **The innermost ring of the boundary:** a 1-WL-rigid graph (refined root already discrete) is handled by ANY resolvers — the root is then the only reachable node, so the capability demand is vacuous. | — |
| `Residue.narrowProper_guard_of_handled` | 187-202 | On a handled graph no node stalls, so the guarded narrowing is proper. | — |
| `Residue.answers_of_handled` | 204-219 | §**★★★ A HANDLED GRAPH ANSWERS.** The guarded descent never flags on it — and it was already unconditionally polynomial. So on `Handled`: **sound, iso-invariant, complete, polynomial, and it answers.** | — |
| `Residue.Residue` | 223-225 | **THE UNHANDLED RESIDUE — defined, not asserted**: some cell defeats **both** resolvers. A *definition* (not an `opaque` atom), so its non-vacuity is provable. Definition. | Definition |
| `Residue.residue_if_flag` | 227-232 | §**★★★ ③ — THE DESCENT FLAGS ONLY ON THE RESIDUE** (`Publication.residue_if_flag`, for the real object). | — |
| `Residue.residue_iff` | 234-248 | Unfolded: a residual graph has a **reachable** cell **neither** supply-connected **nor** key-separated — exactly `Composite.forceThenConsume_stall`'s attribution, so each residual cell is assignable to **one** side's weakness, and it is a cell the descent can actually be confronted with. | — |
| `Residue.emptySupply` | 267-268 | The empty supply certifies nothing (non-vacuity witness). Definition. | Definition |
| `Residue.constKey` | 270-271 | A constant key separates nothing (non-vacuity witness). Definition. | Definition |
| `Residue.keyEquivariant_constKey` | 273 | The constant key is trivially equivariant — so the witness below uses a *legal* resolver, not an ill-formed one. | — |
| `Residue.not_wordReach_nil` | 275-280 | With no generators, nothing is word-reachable but the point itself. | — |
| `Residue.adjE2` | 282-285 | The empty graph on two vertices — the smallest graph whose swap symmetry survives refinement; the shared witness of both non-vacuity halves (`residue_nonvacuous` here, `HandledBridge.adjE2_handled` with the deep oracle). | Definition |
| `Residue.residue_nonvacuous` | 287-322 | **★★ The residue is INHABITED, at a genuinely REACHED node:** the empty 2-graph's root — non-discrete by refiner equivariance under the swap — defeats the certify-nothing resolvers (`emptySupply`/`constKey`). Pairs with `HandledBridge.adjE2_handled`: same graph, handled once the supply is real. | — |
## ChainDescent/MatchSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Consume.rankSwap` | 55-68 | The **colour-match permutation**: send the vertex of rank `i` under `ψv` to the vertex of rank `i` under `ψw`. Computable (via `rankInv`), and a genuine `Equiv` because `vertexRank` is injective on a discrete colouring. Definition. | Definition |
| `Consume.rankSwap_apply` | 70-71 | `rankSwap` unfolded. | `@[simp]` |
| `Consume.lookData` | 75-78 | The refinement reached by individualizing `v`, **materialised** (⚠ never a `… → Colouring n` definition — the eta-expansion trap). Definition. | Definition |
| `Consume.lookData_col` | 80-82 | The look-ahead colouring equals `warmRefineR` after individualization. | — |
| `Consume.matchCol` | 84-93 | The construct-and-check candidate at the level of **colourings** (not `ColData`) — phrased so the transport lemmas can rewrite under it. | Definition |
| `Consume.matchFrom` | 95-97 | The rank-match on **already-materialised** refinements. §Factored out precisely so `matchSupply` can refine each branch **once** and then pair over the results — calling `matchCandidate adj χ v w` in both loops re-refines per *pair* (`|cell|²` instead of `|cell|`), an `O(n)` factor measured at 3.5 min → 4 s on the Frucht graph. Definition. | Definition |
| `Consume.matchCandidate` | 99-101 | **The construct-and-check candidate** (`CascadeOracle.matchOracle` §C.4, rebuilt over `(adj, χ)`): individualize `v` and `w`, refine both; if both discretize, hand back the colour-match permutation. A *candidate only* — `Consume.verified` re-checks it edge-by-edge, so nothing here is trusted. Definition. | Definition |
| `Consume.matchCandidate_eq_of_isColAut` | 103-141 | §**★★ THE ORACLE RECONSTRUCTS THE AUTOMORPHISM EXACTLY.** If some colouring-preserving automorphism `α` carries `v` to `w` and individualizing `v` **discretizes**, the construction fires and returns **`α` itself** — not merely *an* automorphism. Proof is the descent's own transport layer: `α·adj = adj`, `α·χ = χ` ⟹ the `w`-side refinement is the `v`-side one transported by `α` ⟹ ranks transport ⟹ the rank-matching permutation is forced to be `α`. | — |
| `Consume.matchSupply` | 145-160 | §**★ THE COLOUR-MATCH SUPPLY** — the cascade oracle as a `Consume.Supply`. Queries `matchCandidate` on every ordered pair of branch vertices. Untrusted as always (`verified` filters it), so `consume_canonizer` holds for it with no obligation. ★ Being a **structural function of `(adj, χ)`** it also repairs **`①c`**: the demo supplies hand back a fixed generator list, are non-equivariant, and provably break flag iso-invariance. Definition. | Definition |
| `Consume.mem_gens_matchSupply` | 162-167 | A constructed candidate is in the supply's output. | — |
| `Consume.mem_verified_matchSupply` | 169-176 | A genuine automorphism between branch vertices survives verification — it was *reconstructed*, so it verifies. | — |
| `Consume.Discretizing` | 180-184 | **The one-step depth witness** (the cascade oracle's `hdisc`): individualizing any branch vertex discretizes the refinement. ⚠ **Far stronger than it sounds — it EXCLUDES CYCLES** (individualizing one vertex of `C₇` leaves `{0},{1,6},{2,5},{3,4}`). Where the Cameron / node-4 obstruction lives is *not* in the construction but here. Definition. | Definition |
| `Consume.cellIsOrbit_matchSupply` | 186-204 | §**★★★ `matchSupply` CERTIFIES EVERY ORBIT IT CAN SEE.** At a `Discretizing` node, every colouring-preserving automorphism between branch vertices is recovered, verified and available to `consume` ⟹ a branch cell that *is* an orbit is certified as one and collapses to a single branch. This is the cascade oracle's honest `hdisc`-only firing (`matchOracle_fires_of_insertDiscrete`) — **no `CellsAreOrbits`, no localisation** — in the resolver's vocabulary. ⚠ **Measured: one step is NOT ENOUGH** — `C₇` is not `Discretizing`, so this flags on cycles. The multi-step / cross-branch harvest (`lockstep_disc_imp_stab_trivial`) is the gap. | — |
| `Consume.rankInv_transport` | 218-226 | `rankInv` transports: the vertex of rank `i` under `σ·ψ` is the `σ`-image of the vertex of rank `i` under `ψ`. | — |
| `Consume.rankSwap_conj` | 228-242 | **★ THE COLOUR-MATCH PERMUTATION CONJUGATES**: `rankSwap (σ·ψv) (σ·ψw) = σ · rankSwap ψv ψw · σ⁻¹`. | — |
| `Consume.matchCol_transport` | 244-263 | The candidate constructor transports up to conjugation, **including its failure mode**: it declines to construct on `σ·G` exactly where it declines on `G`. | — |
| `Consume.lookData_col_transport` | 265-271 | The look-ahead refinement transports (refiner equivariance + `indivOne_transport`). | — |
| `Consume.matchCandidate_conj` | 273-279 | **★ THE CANDIDATE CONJUGATES** — the engine of `SupplyTransport.gensEquivariant_matchSupply`, hence of the flag's iso-invariance. | — |
| `Consume.mem_gens_matchSupply_iff` | 281-294 | Membership in `matchSupply`, characterised: its generators are exactly the candidates the construction built on some ordered pair of branch vertices. | — |
## ChainDescent/Regression.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Regression.C5` | 49-50 | The 5-cycle: vertex-transitive ⟹ **every cell is an orbit** — consume's domain, force's blind spot. Definition. | Definition |
| `Regression.P5` | 52-54 | The 5-path: `Aut = ℤ₂`, and individualizing **discretizes** ⟹ it is `Consume.Discretizing`, so the colour-match oracle can actually fire on it. Definition. | Definition |
| `Regression.G8` | 56-63 | §**A cubic non-vertex-transitive graph on 8 vertices** (two triangles; `6`,`7` in none). Being **regular**, 1-WL leaves a **single cell of all 8**; not being vertex-transitive, that cell is **not an orbit** — force's domain, at `n = 8` instead of the Frucht graph's `n = 12`. **~8× cheaper**, and the reason the regression suite left the critical path's slow lane. Definition. | Definition |
| `Regression.dihSupply` | 65-68 | The full `Aut(Cₙ) = Dₙ`, as a **fixed** generator list — hence **not equivariant**, which is exactly what the `①c` counterexample needs. Definition. | Definition |
| `Regression.form` | 72-73 | Exhaustive canonical form, as a comparable value. Definition. | Definition |
| `Regression.formC` | 82-83 | Oracle-driven canonical form (`consume`). Definition. | Definition |
| `Regression.gForce` | 106-107 | Guarded **force** canonical form. Definition. | Definition |
| `Regression.gMatch` | 116-117 | Guarded **mixed** form with the **structural** cascade-oracle supply. Definition. | Definition |
| `Regression.gMix` | 145-148 | Guarded **mixed** form with the fixed-generator (non-equivariant) supply — the `①c` counterexample. Definition. | Definition |
| `Regression.C4` | 163 | The 4-cycle — the cheapest P2 witness (a reflection fixes each vertex ⟹ the one-step oracle provably cannot fire). | Definition |
| `Regression.gDeep` | 165-167 | Guarded **mixed** form with the bounded-depth oracle at depth `d`. Definition. | Definition |
| `Regression.gPruned` | 182-186 | Guarded **mixed** form with the reference-matching pruned supply. Definition. | Definition |
| `Regression.coreE` | 202-205 | Edge predicate of the fold demo's 6-vertex core (path `0…5` + chord `1-3`) — 1-WL-discrete, hence asymmetric. | Definition |
| `Regression.core6` | 207 | The fold demo's core graph. Definition. | Definition |
| `Regression.fold4` | 209-211 | **The F_k fold witness:** 4 disjoint copies of the core — copies are 1-WL twins, the branch cell is the 4 copies of one core vertex (`docs/chain-descent-fold-tower-plan.md` §3). | Definition |
| `Regression.core6Root` | 213-215 | Materialized root colouring — `ColData`-backed (standing trap #1: an inline `Colouring`-typed expression re-runs refinement per lookup). | Definition |
| `Regression.fold4Root` | 216 | Materialized fold root colouring — same trap-#1 discipline, at `n = 24` the difference between ~2 s and minutes. | Definition |
| `Regression.gSel` | 251-252 | The fused canonizer (`Select.canonFormFastS?`, `lookaheadKey` + `matchSupply`) flattened for the §9 dominance-parity and flag-parity guards. | Definition |
| `Regression.gSelDeep` | 254-255 | The fused canonizer over the depth-`d` oracle, flattened — the C₄ `d = 1` parity guard against `gDeep`. | Definition |
| `Regression.vcoreB` | 287-291 | `C₄` + pendant — the mirror (1↔3) survives every pin on the mirror axis, so a copy is NEVER refinement-discretized (the WL-blind mechanism in miniature). | Definition |
| `Regression.vfold2` | 293-296 | **The F2a witness:** 2 copies of the mirror-tied core, one vertical matching edge per fiber. | Definition |
| `Regression.vfold2Root` | 298 | Materialized root colouring (trap #1). | Definition |
| `Regression.wEdge` | 328-333 | Weighted cycle edge function: edge `i—i+1` of `C_N` has weight `i % 3 + 1` — `Aut = Z_{N/3}`, involution-free for odd `N/3` (kills every reflection). | Definition |
| `Regression.wcyc9` | 335 | **The F2b witness**: weighted `C₉`, `Aut = Z₃` exactly — no involutions in `Aut` at all, so every involution-based constructor is structurally out. | Definition |
| `Regression.wcyc9Root` | 336-338 | Materialized root colouring (trap #1). | Definition |
| `Regression.wcyc9Swapped` | 349 | Cross relabelling — the supply-level `①c` observation's graph. | Definition |
| `Regression.wcyc9SwappedRoot` | 350-351 | Its materialized root (trap #1). | Definition |
| `Regression.vfoldT` | 376-383 | The twisted/untwisted vertical 3-fold: `twist01` crosses the `{1,3}` fiber edges of the (0,1) copy-pair. | Definition |
| `Regression.ut` | 385-389 | **The F3a witness** `U3 ⊔ T3` (n = 30): non-isomorphic by twist parity, 1-WL-merged — the distinguishable-but-WL-merged cell force must separate. | Definition |
| `Regression.utRoot` | 391 | Materialized root colouring (trap #1). | Definition |
| `Regression.C7` | 422 | — | Definition |
| `Regression.gTree` | 424-426 | — | Definition |
| `Regression.c7Root` | 437 | — | Definition |
| `Regression.c7Seed` | 438-445 | — | Definition |
| `Regression.t3` | 460 | The one-pair-twisted triple cover alone (n = 15; `ut`'s T block) — the F2c witness: its commuting mirror gauge stalls fold AND deck. | Definition |
| `Regression.t3Root` | 461-463 | Root colouring of `t3` (ColData-materialised, trap #1). | Definition |
| `Regression.mpOnLine` | 487 | Fano line membership `{i, i+1, i+3} mod 7` for the mp7 witness. | Definition |
| `Regression.mpInS` | 488-493 | Even-subset membership for the mp7 CFI gadgets. | Definition |
| `Regression.mpFG` | 494-497 | Foot–gadget adjacency of the Fano multipede. | Definition |
| `Regression.mp7` | 498-501 | The FANO MULTIPEDE (n = 42): the C3 witness — symmetric pin-blind CFI cover, gauge = the [7,3,4] simplex code (arity-3 checks, girth 6, min weight 4); fold/deck/deck2 + manual deck3 all measured dead (`PerformanceTest` §13); the kernel supply consumes its whole gauge (§14, `Regression` §15). | Definition |
| `Regression.mp7Root` | 502-505 | mp7's root colouring (ColData — trap #1). | Definition |
| `Regression.g8Root` | 598-604 | — | Definition |
## ChainDescent/SealBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SealBridge.refineRound_samePartition` | 57-63 | **P0/1.** One encode-free round (`Refine.refineRound`, which *ranks* `sigKey`s) has the **same partition** as one stock round (`refineStep = Encodable.encode ∘ sigKey`) at the constant `P`. | — |
| `SealBridge.warmRefineR_samePartition` | 65-78 | **★ P0/1 — THE REFINER BRIDGE.** The descent's `Refine.warmRefineR` and the seal's `warmRefine … (constP n)` induce the **same partition**, so every partition-level statement crosses between the two vocabularies freely. | — |
| `SealBridge.refines_warmRefine` | 92-94 | Warm refinement refines its input (split-only), in `Refines` form. | — |
| `SealBridge.refines_warmRefine_of_stable` | 96-109 | **★ P0/2 — `warmRefine` IS THE COARSEST STABLE REFINEMENT.** Any colouring that is stable and refines `χ` already refines `warmRefine χ`. The engine of the confluence: refinement done *early* is never refinement the fixpoint would not have done anyway. | — |
| `SealBridge.stable_warmRefine` | 111-114 | `warmRefine χ` is a `refineStep`-fixpoint up to partition, in `Refines` form (from `warmRefine_refineStep_samePartition`). | — |
| `SealBridge.indivOne_refines` | 118-129 | Individualizing refines: `indivOne χ v` never merges two `χ`-classes. | — |
| `SealBridge.indivOne_mono` | 131-145 | `indivOne` is **monotone** in the colouring it individualizes: a finer `χ` gives a finer `indivOne χ v`. | — |
| `SealBridge.indivOne_congr` | 147-150 | `indivOne` respects `samePartition` (both directions of `indivOne_mono`). | — |
| `SealBridge.warmRefine_indivOne_confluent` | 154-195 | **★★★ P0/3 — CONFLUENCE.** `W (indivOne (W χ) v) ≅ W (indivOne χ v)`: refining **before** individualizing does not change the stable partition. This is what reconciles the descent's *interleaved* individualize-refine chain with the seal's *batch* `individualizedColouring n T`, and it is the only non-bookkeeping step of the bridge. | — |
| `SealBridge.indiv_eq_iff` | 199-220 | Two vertices share an `individualizedColouring n T` colour **iff** they are equal or both uncommitted. | — |
| `SealBridge.samePartition_indivOne_insert` | 222-257 | **P0/5.** One more `indivOne` on top of a set-individualization = individualizing the bigger set: `indivOne (individualizedColouring n D) v ≅ individualizedColouring n (insert v D)`. | — |
| `SealBridge.pathCol` | 261-265 | **The descent's colouring after committing the path `p`** (head = most recently individualized) — exactly the colouring `descend` carries at the node reached by branching along `p`. | Definition |
| `SealBridge.pathCol_samePartition` | 267-297 | **★★ P0 — THE PARTITION BRIDGE.** The descent's node colouring `pathCol adj p` and the seal's `warmRefine adj (constP n) (individualizedColouring n p.toFinset)` induce the **same partition**: "same cell" means the same thing on both sides. | — |
| `SealBridge.relabel_of_isAut` | 301-309 | A graph automorphism fixes the graph under relabelling: `IsAut α adj → relabelAdj α adj = adj`. | — |
| `SealBridge.transport_pathCol` | 311-333 | **A path-fixing automorphism preserves the descent's colouring EXACTLY** (not merely up to partition): `indivOne` and the refiner are both equivariant and `α` fixes every committed vertex, so the whole chain of colourings is `α`-invariant. | — |
| `SealBridge.isColAut_of_pathFixing` | 335-340 | **P0 — the seal's `ResidualAut` IS the descent's `IsColAut`.** An automorphism fixing the committed path pointwise is a colouring-preserving automorphism of the descent's node colouring. | — |
| `SealBridge.horb_of_cellsAreOrbits` | 344-357 | **★★★ P0 — THE DELIVERABLE. `CellsAreOrbits` ⟹ the `horb` hypothesis of `Consume.cellIsOrbit_matchSupply`.** The seal corpus proves `CellsAreOrbits` (≡ `OrbitRecoverableAt` ≡ `TwinsRealizedByResidualAut` ≡ the deep clause of `SchemeRecoveredByDepth`) on CFI, rank-≤2 schemes, the four sealed form families, and — via Spielman — at a bounded base. **Every one of those now reaches the supply, with no re-proof.** | — |
| `SealBridge.cellIsOrbit_of_cellsAreOrbits` | 359-375 | **★★★ P0 — THE ORACLE FIRES ON THE SEAL'S CLASS.** At a node that localises (`CellsAreOrbits`, the seal's own carried hypothesis) and discretizes in one step (`Discretizing`, the cascade oracle's `hdisc`), `matchSupply` certifies the branch cell as an orbit and `consume` collapses it. ⚠ The `Discretizing` half is the frontier this bridge does **not** close (it forces trivial point stabilizers — why `matchSupply` flags on `C₇`); localisation is now importable rather than re-proved. | — |

## ChainDescent/SupplyTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SupplyTransport.dedup_map_length_eq_card_image` | 61-67 | The deduplicated image of a list is its `Finset` image — both count *distinct values*. | — |
| `SupplyTransport.card_image_congr_of_iff` | 69-91 | **★ P1 — THE COUNTING LEMMA.** Two maps inducing the **same fibres** on `s` have images of the same size. This is what lets a deliberately *non-equivariant* representative choice still produce an **invariant count**. | — |
| `SupplyTransport.GensEquivariant` | 95-101 | **P1 — the supply's transport obligation.** On the relabelled graph the supply hands back exactly the `σ`-conjugates of what it hands back here. **Free for a structural supply** (a function of `(adj, χ)`); **impossible for an accumulating one** (the C# harness's global `PermutationGroup`), which is a real design constraint on any future supply. | Definition |
| `SupplyTransport.SupplyEquivariant` | 103-107 | `GensEquivariant` on the **verified** list — the only thing the resolver ever reads. | Definition |
| `SupplyTransport.supplyEquivariant_of_gensEquivariant` | 109-123 | Verification commutes with conjugation (`Consume.isColAut_conj_iff`), so an equivariant supply yields an equivariant *verified* list. The form a concrete supply should discharge. | — |
| `SupplyTransport.conj_symm` | 127-137 | The conjugation relation between two generator lists, read backwards. | — |
| `SupplyTransport.wordReach_conj` | 139-151 | A word in `G` becomes the conjugate word in `G' = σGσ⁻¹`. | — |
| `SupplyTransport.wordReach_conj_iff` | 153-162 | **★ P1 — ORBITS TRANSPORT.** The verified generators on `σ·G` connect `σu` to `σw` **iff** the originals connect `u` to `w`: the orbit *partition* of the branch cell is a genuine isomorphism invariant, even though the representative chosen from each orbit is not. | — |
| `SupplyTransport.stallEquivariant_forceThenConsume` | 166-197 | **★★★ P1 — THE FLAG'S ISO-INVARIANCE, DISCHARGED.** `Stall.StallEquivariant` — carried by all three `Residue` capstones and instantiated by nothing — follows from `KeyEquivariant` + `SupplyEquivariant`. The proof never transports the (non-equivariant, least-index) `rep`: it transports the **orbit partition** and the **forced set**, and observes via `Consume.rep_eq_iff_wordReach` that the narrowing's *length* counts **orbits**. | — |
| `SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport` | 199-228 | — | — |
| `SupplyTransport.guarded_mixed_canonizer` | 230-238 | **★★★ THE GUARDED MIXED CANONIZER WITH NO CARRIED FLAG HYPOTHESIS** — sound, iso-invariant, complete and unconditionally polynomial, for **any** equivariant key and **any** equivariant supply. | — |
| `SupplyTransport.gensEquivariant_matchSupply` | 247-268 | **★★ `matchSupply` IS EQUIVARIANT** — the construction conjugates (`Consume.matchCandidate_conj`), *including its failure mode*: it declines on `σ·G` exactly where it declines on `G`. The non-vacuity witness for `GensEquivariant`. | — |
| `SupplyTransport.supplyEquivariant_matchSupply` | 270-271 | `matchSupply` satisfies the verified-list form of the transport obligation. | — |
| `SupplyTransport.matchSupply_guarded_canonizer` | 273-285 | **★★★ THE FIRST CONCRETE MIXED CANONIZER.** Every parameter is a named, built object — the encode-free refiner, the look-ahead key, the colour-match oracle — and **no hypothesis is carried**: ①a (sound), ①b (complete), ①c (iso-invariant answer *and* flag), plus unconditional polynomiality via `Stall.descentCost_guard_le`. Everything still open is a **firing** question, not a correctness one. | — |
## ChainDescent/DeepMatchSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `DeepMatch.seqsLen` | 71-74 | All vertex sequences of length exactly `k` (the depth-`d` search space's rungs). | Definition |
| `DeepMatch.mem_seqsLen` | 76-90 | Membership in `seqsLen n k` **is** having length `k` — nothing else. | — |
| `DeepMatch.allSeqs` | 92-95 | **P2's search space: every sequence of length `≤ d`.** No representative is ever *chosen* — a choice would be non-canonical (cell members are exactly what 1-WL cannot distinguish), breaking `GensEquivariant` and hence `①b`/`①c`. | Definition |
| `DeepMatch.mem_allSeqs` | 97-106 | Membership in `allSeqs n d` **is** having length `≤ d`. | — |
| `DeepMatch.mem_allSeqs_map` | 108-112 | **★ THE SEARCH SPACE IS σ-INVARIANT, trivially** — membership depends only on the **length**. This one line is why the bounded-depth oracle escapes `lockstep_disc_imp_stab_trivial` (which refutes an equivariant *choice function*, not an exhaustive enumeration). | — |
| `DeepMatch.exists_preimage_seq` | 114-116 | Every sequence in the search space is the `σ`-image of one in it. | — |
| `DeepMatch.deepCol` | 120-129 | **The colouring reached by individualizing a sequence in order, refining after each** — literally `descend`'s own step, iterated. Index-free, so it transports (unlike the seal's index-coloured `indivWithSeq`), and position-distinct, so it discretizes (unlike the uniform-coloured `indivWithSet`). ⚠ Spec only — never evaluated (the executable path is `deepData`). | Definition |
| `DeepMatch.deepData` | 131-134 | The **materialised** deep colouring (`ColData`-valued, so each level is forced once — the eta-expansion trap). | Definition |
| `DeepMatch.deepData_col` | 136-146 | The runnable deep colouring computes exactly the reasoned-about one. | — |
| `DeepMatch.deepCol_transport` | 148-166 | **★ THE DEEP COLOURING TRANSPORTS** (`indivOne` is index-free; the refiner is equivariant). | — |
| `DeepMatch.deepCandidate` | 170-173 | Individualize `v` then `sv`, and `w` then `sw`; if both discretize, colour-match. A *candidate only* — `Consume.verified` re-checks it. | Definition |
| `DeepMatch.matchCol_self_transport` | 175-188 | A discrete colouring and its `α`-transport colour-match to **exactly `α`**. | — |
| `DeepMatch.deepCandidate_eq_of_isColAut` | 190-206 | **★★ THE ORACLE RECONSTRUCTS THE AUTOMORPHISM EXACTLY, AT DEPTH.** If individualizing `v` then `s` discretizes, the pair `(v,s)` against `(α v, α·s)` constructs **`α` itself** — and `α·s` has the *same length* as `s`, so it is **in the search space**. That is the whole design: we never guess `α`'s continuation, we enumerate all of them. | — |
| `DeepMatch.deepCandidate_conj` | 208-220 | The candidate conjugates — the engine of `GensEquivariant`. | — |
| `DeepMatch.deepTable` | 224-233 | The `(branch, sequence)` table, each deep colouring materialised **once** (the per-branch base refinement is bound *outside* the sequence loop — recomputing it would be the `O(n)`-in-the-algorithm bug `matchSupply` originally shipped). | Definition |
| `DeepMatch.mem_deepTable_iff` | 235-246 | Membership in the table, characterised. | — |
| `DeepMatch.deepTable_col` | 248-255 | Every table row's colouring **is** the deep colouring it is indexed by. | — |
| `DeepMatch.deepMatchSupply` | 257-263 | **★ THE BOUNDED-DEPTH ORACLE.** Colour-match every `(branch, sequence ≤ d)` pair against every other. Untrusted (`consume_canonizer` holds for it with no obligation). ⚠ Cost is `n^{O(d)}`: **polynomial for bounded `d`, quasi-polynomial at `d = Θ(log n)`, sub-exponential at Spielman's `d = Õ(n^{1/3})` — exactly the seal's ladder.** Billed in `supplyCost`, so `②` sees it. | Definition |
| `DeepMatch.mem_gens_deepMatchSupply_iff` | 265-284 | Membership in the supply, characterised: its generators are exactly the candidates built on some pair of `(branch, sequence ≤ d)`. | — |
| `DeepMatch.gensEquivariant_deepMatchSupply` | 288-314 | **★★ THE BOUNDED-DEPTH ORACLE IS EQUIVARIANT** — because the search space is `σ`-invariant and the deep colouring transports. **No representative is ever chosen**, which is exactly what a stabilizer-chain supply cannot arrange (its within-cell pick is non-canonical, so its generators are not `σ`-conjugates and `①b`/`①c` — both routing through `StallEquivariant` — would fail). | — |
| `DeepMatch.supplyEquivariant_deepMatchSupply` | 316-318 | The verified-list form of the transport obligation, for `deepMatchSupply d`. | — |
| `DeepMatch.SeparatesAt` | 322-326 | **The depth witness.** Every branch vertex, plus **some** sequence of `≤ d` further individualizations, discretizes. This is the descent-side form of the seal's `SeparatesAtBoundedBase` / `CascadesAt` — the *same* hypothesis the cascade oracle carries (P0's confluence identifies batch and interleaved individualization). | Definition |
| `DeepMatch.separatesAt_zero_iff` | 328-342 | **`matchSupply` is the `d = 0` case**: `SeparatesAt … 0` *is* `Consume.Discretizing`. So the bounded-depth oracle is a strict generalization, not a replacement. | — |
| `DeepMatch.cellIsOrbit_deepMatchSupply` | 344-367 | **★★★ THE ORACLE FIRES.** Given the **depth** witness (`SeparatesAt`) and **localisation** (`horb`, which `SealBridge.horb_of_cellsAreOrbits` imports straight from the seal's `CellsAreOrbits`), `deepMatchSupply d` certifies the branch cell as an orbit and `consume` collapses it. The proof is the design in one line: `α·s` has the same length as `s`, so the pair that reconstructs `α` **is enumerated**. | — |
| `DeepMatch.deepMatchSupply_guarded_canonizer` | 371-381 | **★★★ THE BOUNDED-DEPTH MIXED CANONIZER** — sound, complete, iso-invariant (answer **and** flag) and unconditionally polynomial in the descent, for **every** `d`, with **no carried hypothesis**. `d` buys *firing*, never correctness. | — |
## ChainDescent/OrbitPrune.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `OrbitPrune.minList_congr` | 61-70 | The minimum of a seeded list depends only on which elements the list *contains*. | — |
| `OrbitPrune.rep_congr` | 72-78 | **★ P3/1 — `rep` IS A FUNCTION OF THE ORBIT RELATION.** Two generator lists that word-reach the same pairs give the *same* representative, even though `rep` is a least-index pick and neither list determines the other. | — |
| `OrbitPrune.SameOrbits` | 82-85 | **Two supplies prove the SAME ORBITS** — the only thing about a supply the object can see. | Definition |
| `OrbitPrune.SameOrbits.symm` | 87-88 | `SameOrbits` is symmetric. | — |
| `OrbitPrune.narrow_forceThenConsume_congr` | 90-96 | The mixed resolver's narrowing is unchanged across `SameOrbits`. | — |
| `OrbitPrune.narrow_guard_congr` | 98-109 | The **guard** reads only the narrowing, so it is unchanged too. | — |
| `OrbitPrune.descend_val_congr` | 111-128 | **Resolvers with the same narrowing compute the same VALUE** — the *cost* may differ, which is exactly the point of pruning. | — |
| `OrbitPrune.canonForm?_congr` | 130-133 | …and hence the same canonical form. | — |
| `OrbitPrune.rep_congr_at` | 143-147 | — | — |
| `OrbitPrune.SameOrbitsOnBranches` | 149-154 | — | Definition |
| `OrbitPrune.narrow_forceThenConsume_congr_branch` | 156-166 | — | — |
| `OrbitPrune.canonForm?_eq_of_sameOrbitsOnBranches` | 168-174 | — | — |
| `OrbitPrune.guarded_mixed_canonizer_of_sameOrbitsOnBranches` | 176-187 | — | — |
| `OrbitPrune.canonForm?_eq_of_sameOrbits` | 191-197 | **★★ The guarded mixed canonizers of two `SameOrbits` supplies are the SAME FUNCTION.** | — |
| `OrbitPrune.guarded_mixed_canonizer_of_sameOrbits` | 199-208 | **★★★ P3 — `①` TRANSFERS ACROSS `SameOrbits`, FOR FREE.** A supply that proves the same orbits as an already-certified one inherits `①a`/`①b`/`①c` with **no equivariance obligation of its own**. This is the license every pruned/optimized supply runs on: it may make any internal choice it likes (a pruned enumeration *must* pick a representative sequence, so `GensEquivariant` is unavailable to it), provided the **group it generates** is unchanged. Reusable by any future supply optimization. | — |
| `OrbitPrune.stallEquivariant_congr` | 210-216 | The **flag**'s iso-invariance transfers (it is read off the same narrowing). | — |
| `OrbitPrune.cellIsOrbit_congr` | 218-221 | **Firing** transfers across `SameOrbits`. | — |
| `OrbitPrune.cellResolved_congr` | 223-227 | `②`'s per-cell resolution predicate transfers. | — |
| `OrbitPrune.handled_congr` | 229-231 | `③`'s `Handled` transfers — **the residue is unchanged** by pruning. | — |
| `OrbitPrune.rankSwap_left_mul` | 235-243 | **★ P3/2 — the `w`-side identity.** Replacing the `w`-side colouring by its `g`-transport **left-multiplies** the colour-match by `g`: `rankSwap ψᵥ (g·ψ_w) = g · rankSwap ψᵥ ψ_w`. | — |
| `OrbitPrune.rankSwap_right_mul` | 245-257 | **★ P3/2 — the `v`-side identity.** Replacing the `v`-side colouring by its `g`-transport **right-multiplies** by `g⁻¹`, so both sides of the enumeration may be pruned. | — |
| `OrbitPrune.matchCol_left_mul` | 259-269 | The `w`-side identity, lifted to the candidate constructor (failure mode included). | — |
| `OrbitPrune.matchCol_right_mul` | 271-281 | The `v`-side identity, lifted to the candidate constructor. | — |
| `OrbitPrune.deepCol_aut` | 283-289 | Deepening along the `g`-image of a sequence gives the `g`-transported colouring, for `g` an automorphism the supply has already **verified**. | — |
| `OrbitPrune.deepCandidate_left_mul` | 291-302 | **★★★ THE `w`-SIDE PRUNING LICENSE.** `deepCandidate v sv (g w) (g·sw) = g · deepCandidate v sv w sw`. A pruned-away candidate is `g · c` with **both** factors already in the generated group ⟹ the **group is unchanged**, and since `Consume.CellIsOrbit` is stated via `WordReach` (a *word* in the generators), the pruned-away element survives as a **product**. | — |
| `OrbitPrune.deepCandidate_right_mul` | 304-312 | **★★★ THE `v`-SIDE PRUNING LICENSE** (right-multiplication by `g⁻¹`). | — |
## ChainDescent/SealDepthBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SealDepthBridge.refines_trans` | 63-65 | Refinement (`χ₁` finer than `χ₂`) is transitive. | — |
| `SealDepthBridge.discrete_of_refines` | 67-69 | A finer colouring of a **discrete** one is discrete — refinement only ever splits classes, so it cannot merge an injective colouring. | — |
| `SealDepthBridge.warmRefineR_refines` | 71-74 | The encode-free warm round **refines its input** (`iterate_splits`: it never merges a colour class). | — |
| `SealDepthBridge.warmRefineR_mono` | 76-86 | The encode-free warm round is **monotone** — a finer input gives a finer output. Transferred from the stock `warmRefine adj (constP n)` (`warmRefine_refines_initial`) through `SealBridge.warmRefineR_samePartition`, since both refiners induce the same partition. | — |
| `SealDepthBridge.deepCol_mono` | 88-96 | **`deepCol` is monotone in its starting colouring** — refining the input refines every deepened colouring. Induction on the sequence; the step is `warmRefineR_mono ∘ indivOne_mono`. | — |
| `SealDepthBridge.deepCol_cons_refines` | 98-105 | **★ PREPENDING A VERTEX ONLY REFINES.** `deepCol adj χ (v :: s)` refines `deepCol adj χ s`: individualizing the branch vertex `v` first gives a finer start, and `deepCol` is monotone. The whole depth bridge rests on this — an `s` that discretizes from `χ` still discretizes after `v` is pinned. | — |
| `SealDepthBridge.CascadesFrom` | 109-113 | **The seal's depth content, in the descent's vocabulary.** Some set `S₀` of size `≤ k` discretizes when individualized (with refinement) on top of `χ` via `deepCol`. The descent-side restatement of `Cascade.SeparatesAtBoundedBase` / `OrbitRecovery.CascadesAt`; connecting the two at the partition level is the follow-on P2c. | Definition |
| `SealDepthBridge.separatesAt_of_cascadesFrom` | 115-125 | **★★★ THE DEPTH BRIDGE.** `CascadesFrom adj χ k ⟹ DeepMatch.SeparatesAt adj χ k`, with the **same bound `k`** — the first theorem to ever *produce* `SeparatesAt` (previously only `#guard`ed on cycles). The witness sequence for **every** branch vertex is the one set `S₀.toList`: prepending the branch vertex only refines (`deepCol_cons_refines`), and a finer colouring of a discrete one is discrete. | — |
| `SealDepthBridge.cellIsOrbit_of_cascadesFrom_of_horb` | 129-139 | **★★★ THE DEPTH ANALOGUE OF `SealBridge.cellIsOrbit_of_cellsAreOrbits`.** Depth (`CascadesFrom`) + localisation (`horb`, imported from the seal's `CellsAreOrbits` by `SealBridge.horb_of_cellsAreOrbits`) ⟹ the bounded-depth oracle `deepMatchSupply k` certifies the branch cell as an orbit at this node, so `consume` collapses it to one branch. The per-node firing the sealed families supply. | — |
| `SealDepthBridge.deepCol_pathCol` | 143-156 | **★ DEEPENING A DESCENT NODE = COMMITTING THE LONGER PATH.** `deepCol adj (SealBridge.pathCol adj p) s = SealBridge.pathCol adj (s.reverse ++ p)` — an **exact** equality, because `pathCol adj (v :: p)` is definitionally `warmRefineR adj (indivOne (pathCol adj p) v)` = exactly `deepCol`'s step. The whole `P2c` vocabulary bridge rests on this one line. | — |
| `SealDepthBridge.cascadesFrom_pathCol_of_cascadesAt` | 158-175 | **★★★ THE SEAL'S DEPTH HYPOTHESIS, AT A DESCENT NODE.** `CascadesAt adj (constP n) k` (a **global** bounded-base discreteness witness, `= SeparatesAtBoundedBase`) ⟹ the descent-side `CascadesFrom adj (pathCol adj p) k` at **every** committed path `p`, from the *same* `S₀`: deepening reaches the longer path (`deepCol_pathCol`), whose partition is `warmRefine ∘ individualizedColouring` (`pathCol_samePartition`), and a superset individualization stays discrete. | — |
| `SealDepthBridge.cellIsOrbit_pathCol_of_seal` | 177-190 | **★★★ THE FULL SEAL → DEEP FIRING BRIDGE.** Depth (`CascadesAt`) **and** localisation (`CellsAreOrbits`) — both discharged by the sealed families (`theorem_1_HOR_*`, the four form families, `viaSpielman`) — together fire `deepMatchSupply k` at the descent node `pathCol adj p`, so `consume` collapses the branch cell. Both halves are now imports; the depth+localisation completion of P0's `cellIsOrbit_of_cellsAreOrbits` (which had only localisation). | — |
| `SealDepthBridge.cascadesAt_of_separatesAtBoundedBase` | 207-210 | The seal's engine interface **is** the descent's depth hypothesis: `SeparatesAtBoundedBase S bound` unfolds to `CascadesAt (schemeAdj S) (constP n) bound`. Definitionally equal — `Refine.constP n` *is* the seal's own `fun _ _ => POE.unknown`, so no PMatrix translation layer exists or is needed. | — |
| `SealDepthBridge.cellIsOrbit_pathCol_of_spielman` | 212-221 | **★★ THE `viaSpielman` POC IMPORT.** A scheme separating at a bounded base fires `deepMatchSupply bound` at every committed path of the descent on the scheme's own adjacency, given localisation there — demonstrating the seal→supply import is generic in the bound, sub-exponential rung included. ⚠ Scope: Spielman's `Õ(n^{1/3})` is citable for claw-bounded SRGs only, and this fires on `schemeAdj S`, not on a graph *realizing* `S` (that hop is `RouteCTransport`). The **poly** rungs (`theorem_1_HOR_*`) are the real workhorse. | — |
## ChainDescent/PrunedSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `PrunedSupply.wordReach_congr_mem` | 47-52 | `WordReach` reads only whether a generator is **in** the list — never its position or multiplicity. Induction on the reach derivation. | — |
| `PrunedSupply.sameOrbits_of_verified_mem` | 54-59 | Two supplies whose **verified** lists have the same membership prove the same orbits (`OrbitPrune.SameOrbits`) — via `wordReach_congr_mem` both ways. | — |
| `PrunedSupply.refCol?` | 63-66 | The colouring of the first **discrete** table entry, if any — the single reference `prunedSupply` matches everything against (`matchCol r _` is `none` unless `r` is discrete). | Definition |
| `PrunedSupply.prunedSupply` | 68-76 | **★ THE REFERENCE-MATCHING ORACLE.** Match the one reference entry against every table entry — `|table|` colour matches instead of `|table|²`. Untrusted (`consume` re-verifies). | Definition |
| `PrunedSupply.gens_prunedSupply` | 78-84 | The pruned candidate list unfolded: `(refCol?).elim [] (fun r => table.filterMap (matchCol r ·.col))`. | — |
| `PrunedSupply.mem_gens_prunedSupply` | 86-99 | Membership in the pruned candidate list: `g` is a candidate iff `refCol? = some r` and some table entry `q` has `matchCol r q.col = some g`. | — |
| `PrunedSupply.mem_gens_deepMatchSupply_raw` | 101-114 | Membership in the all-pairs (`deepMatchSupply`) candidate list: `g` is a candidate iff some ordered pair of table entries `matchCol`s to it. | — |
| `PrunedSupply.discrete_refCol` | 118-124 | Whatever `refCol?` returns is **discrete** — it is the `find?` predicate. | — |
| `PrunedSupply.refCol_eq_deepCol` | 126-131 | The reference is one of the table entries' colourings — so a reference match is an all-pairs candidate (the pruned ⊆ deep direction). | — |
| `PrunedSupply.refCol_isSome_of_discrete` | 133-140 | A **discrete** table entry forces the reference to exist (`refCol? = some _`). | — |
| `PrunedSupply.mem_branches_of_isColAut` | 142-146 | A verified automorphism **permutes the branch cell** — it preserves colours and `branches` is a colour class. | — |
| `PrunedSupply.exists_image_entry` | 148-174 | **★ THE KEY CONSTRUCTION.** For a verified automorphism `g` and reference `r = (v₀, s₀)`, the `g`-image `(g v₀, s₀.map g)` is **also a table entry** (length-closed enumeration), with colouring `g`-transport of `r`, so `matchCol r (that) = some g` — every verified `g` is a reference match (the deep ⊆ pruned direction). | — |
| `PrunedSupply.verified_mem_iff` | 178-195 | **★★★ THE VERIFIED SETS ARE EQUAL.** `g ∈ verified prunedSupply ↔ g ∈ verified deepMatchSupply` — pruned⊆deep (a ref match is an all-pairs candidate) and deep⊆pruned (`exists_image_entry`). | — |
| `PrunedSupply.sameOrbits_deepMatchSupply` | 197-201 | **★★★ `prunedSupply d` PROVES THE SAME ORBITS AS `deepMatchSupply d`** — the entire `①` obligation of the pruned supply, discharged, with no equivariance proof of its own. | — |
| `PrunedSupply.prunedSupply_guarded_canonizer` | 203-211 | **★★★ THE PRUNED MIXED CANONIZER.** `①a`/`①b`/`①c` for the guarded composite over the cheaper reference-matching supply — inherited from `deepMatchSupply`'s equivariance through the `SameOrbits` reduction, no equivariance proof on `prunedSupply`. | — |
| `PrunedSupply.prunedSupply_lookahead_canonizer` | 213-218 | The pruned mixed canonizer with the concrete `lookaheadKey`. | — |
## ChainDescent/HandledBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `HandledBridge.ValidPath` | 71-83 | **A validly-reachable committed path**: each successive vertex drawn from a NON-SINGLETON cell of the node it extends (partner form — widened 2026-07-17 in lockstep with `Reaches.step` so sel-descents are covered). Valid `p.toFinset` still ranges over strictly fewer sets than `∀ T`, which keeps the weakest hook lighter. | Inductive |
| `HandledBridge.reaches_pathCol_valid` | 85-97 | **★★ The reachable-node induction, validity-carrying:** every reached node colouring IS `pathCol adj p` for a VALID `p` (the branch step's `v ∈ branches` side condition is retained). Feeds the weakest hook. | — |
| `HandledBridge.reaches_pathCol` | 99-103 | Validity-forgetting corollary of `reaches_pathCol_valid` — enough for the `∀ T` hook. | — |
| `HandledBridge.handled_of_seal_selected` | 107-127 | **★★ THE WEAKEST HOOK:** localisation demanded only for the TARGET cell (the `SelectedCellIsOrbit` shape — `Consume.CellIsOrbit` reads nothing else) and only at validly-reachable committed sets ⟹ `Handled key (deepMatchSupply k)`, every key. Use when a family's localisation is earned along the descent's own choices; the `∀ T` hook implies this one's hypothesis. | — |
| `HandledBridge.selectedOrbits_of_cellsAreOrbits` | 129-139 | **The two hooks are a lattice, in code:** `∀ T, CellsAreOrbits` restricts to the target cell at any path — so `handled_of_seal` is the `∀ T` instance of `handled_of_seal_selected`. | — |
| `HandledBridge.handled_of_seal` | 141-152 | **★★★ THE FIRST STRUCTURAL DISCHARGE OF `Residue.Handled`:** seal depth (`CascadesAt` at bound `k` — what `theorem_1_HOR_*`/the sealed families produce) + localisation at every committed set (`∀ T, CellsAreOrbits`) ⟹ `Handled key (deepMatchSupply k)` for EVERY key. The mixed-canonizer analogue of `reachesRigidOrCameron`: the improvable boundary, extended per family with no re-proof. | — |
| `HandledBridge.handled_of_seal_selected_pruned` | 154-162 | The weakest hook on the cheap reference-matching supply — same `SameOrbits` transfer, no new proof. | — |
| `HandledBridge.handled_of_seal_pruned` | 164-171 | The seal boundary transferred to the cheap reference-matching supply through `SameOrbits` — no new proof (P3a's reduction doing its job). | — |
| `HandledBridge.seal_graph_answers` | 175-183 | **★★ Showcase:** a seal-covered graph is canonized by the guarded mixed canonizer — sound, iso-invariant, complete, single path of ≤ n+1 nodes, and it ANSWERS. | — |
| `HandledBridge.seal_graph_answers_pruned` | 185-191 | The showcase corollary with the cheap pruned supply. | — |
| `HandledBridge.emptyAdj` | 201-203 | The edgeless graph on `n` vertices — vertex-transitive, so 1-WL alone never finishes it (`n ≥ 2`); the concrete handled family's carrier. | Definition |
| `HandledBridge.cellsAreOrbits_emptyAdj` | 205-226 | **Localisation at every committed set, discharged concretely:** on the edgeless graph every permutation is an automorphism, and a same-cell pair is never committed (`warmRefine_refines`), so a transposition fixing the committed set realizes the orbit. | — |
| `HandledBridge.handled_emptyAdj` | 228-233 | **★★ THE FIRST INHABITED `Handled` INSTANCE — a family:** the edgeless graphs, every `n`, every key, via `handled_of_seal` at the trivial depth bound (`cascadesAt_univ`). Not vacuous: the supply genuinely fires at every reached node. | — |
| `HandledBridge.adjE2_handled` | 235-240 | **★ THE RESIDUE SHRINKS, AT THEOREM LEVEL:** the very graph `residue_nonvacuous` shows residual for the certify-nothing resolvers is handled by the deep oracle — the non-vacuity pair is about ONE graph, differing only in resolver strength. | — |
| `HandledBridge.adjE2_answers` | 242-248 | The shrink witness answers under the guarded mixed canonizer with the deep oracle. | — |
## ChainDescent/ClosureCalculus.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SingletonAt` | 79-81 | — | Definition |

## ChainDescent/PartialMatch.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `PartialMatch.SingletonAt` | 62-65 | `u`'s colour class is a singleton — the pointwise form of `Discrete`, read support-locally. | Definition |
| `PartialMatch.singletonAt_of_discrete` | 70-72 | A discrete colouring makes every vertex a singleton — the subsumption direction's engine. | — |
| `PartialMatch.singletonAt_transport` | 74-83 | Singleton-ness transports: the transported class at `u` is a singleton iff the class at `σ⁻¹u` is. | — |
| `PartialMatch.uniqueAt` | 95-100 | The unique vertex of colour `c`, if exactly one — the only lookup the constructor performs; canonical, no representative chosen. | Definition |
| `PartialMatch.uniqueAt_self` | 102-107 | At a singleton vertex the lookup returns exactly that vertex. | — |
| `PartialMatch.uniqueAt_transport` | 121-138 | The lookup transports: `uniqueAt` on the transported colouring is the `σ`-image of the lookup — engine of both the reconstruction and `GensEquivariant`. | — |
| `PartialMatch.pmFun` | 142-147 | The raw support-local map: forward-match on `ψ₁`-singletons, backward-match on `ψ₂`-singletons, identity elsewhere. Total; the permutation check lives in `partialMatch`. | Definition |
| `PartialMatch.partialMatch` | 149-155 | **The support-local candidate constructor:** assemble `pmFun` and its mirror into an `Equiv.Perm` iff they are two-sided inverses (decidable); else decline. Untrusted like `matchCol`, but never demands global discreteness. | Definition |
| `PartialMatch.CatchesAt` | 159-164 | **The catch condition:** every moved vertex a `ψ`-singleton (any `α`), OR `α` an **involution** with every moved vertex singleton on ONE side — the fold case (one copy discretized). | Definition |
| `PartialMatch.pmFun_transport_eq` | 179-211 | **★ The reconstruction, pointwise:** on a catchable pair the raw map is exactly `α` — forward reads `α` off singleton colours, backward reads `α⁻¹ = α` (involution), identity is `α` off the support. | — |
| `PartialMatch.catchesAt_symm` | 222-247 | The catch condition holds symmetrically for `α⁻¹` against the transported colouring — what makes the two-sided inverse check pass. | — |
| `PartialMatch.partialMatch_transport_of_catches` | 249-261 | **★★ THE RECONSTRUCTION:** on a catchable pair the constructor returns exactly `α` — `matchCol_self_transport` with global discreteness replaced by a (half-)discretized support. | — |
| `PartialMatch.pmFun_conj` | 265-285 | The raw map conjugates under `σ` (via the `SingletonAt`/`uniqueAt` transport lemmas). | — |
| `PartialMatch.partialMatch_conj` | 303-318 | The constructor transports up to conjugation, **including its failure mode** — the `matchCol_transport` analogue, so the supply's equivariance proof is `deepMatchSupply`'s verbatim. | — |
| `PartialMatch.pCandidate` | 322-325 | The deep candidate, support-locally: individualize-and-refine along both sequences, then `partialMatch`. | Definition |
| `PartialMatch.pCandidate_eq_of_isColAut` | 327-340 | **The oracle reconstructs a catchable automorphism exactly, at depth** — `α·s` has the same length as `s`, so the partner is enumerated; no guessing, no choice. | — |
| `PartialMatch.pCandidate_conj` | 342-354 | The candidate conjugates — the engine of `GensEquivariant`. | — |
| `PartialMatch.partialMatchSupply` | 356-363 | **★ THE SUPPORT-LOCAL BOUNDED-DEPTH ORACLE** — the `deepTable` enumeration verbatim with `matchCol` replaced by `partialMatch`; untrusted; cost formula identical to `deepMatchSupply d`. | Definition |
| `PartialMatch.mem_gens_partialMatchSupply_iff` | 365-384 | Generator membership = some enumerated `(branch, seq≤d)` pair's candidate. | — |
| `PartialMatch.gensEquivariant_partialMatchSupply` | 388-415 | **★★ The supply is equivariant** — length-characterized search space + conjugating constructor; no representative is ever chosen (standing trap #7). | — |
| `PartialMatch.supplyEquivariant_partialMatchSupply` | 417-419 | Packaged for the guard. | — |
| `PartialMatch.SupportSeparatesAt` | 423-429 | **The support-local depth witness:** every branch pair is connected by an automorphism whose support is (half-)discretized within some `≤ d` continuation — on a `k`-fold cover this holds at the `d` that discretizes ONE copy, where `SeparatesAt` needs `d ≥ k−2`. | Definition |
| `PartialMatch.supportSeparatesAt_of_separatesAt` | 431-441 | **The strict-generalization half:** every `deepMatchSupply` firing configuration (`SeparatesAt` + localisation) is a `partialMatchSupply` one. | — |
| `PartialMatch.wordReach_partialMatch_of_catches` | 443-458 | **Graded firing, per pair:** one catchable automorphism puts its pair into the verified `WordReach` — each verified copy transposition merges its two copies, whatever happens elsewhere in the cell. | — |
| `PartialMatch.cellIsOrbit_partialMatchSupply` | 460-467 | **★★★ THE ORACLE FIRES:** under the support-local witness the branch cell is certified one orbit and consume collapses it to one branch — on a fold, at the depth that discretizes one copy, independent of `k`. | — |
| `PartialMatch.partialMatchSupply_guarded_canonizer` | 471-480 | **★★★ THE SUPPORT-LOCAL MIXED CANONIZER** — ①a/①b/①c + single guarded path, every `d`, NO carried hypotheses. F1 of `docs/chain-descent-fold-tower-plan.md`; MEASURED: the 4-fold cover answers at `d = 0` where `deepMatchSupply` is dead at `d = 0` AND `d = 1` (132× the cost). | — |
## ChainDescent/SupplyCost.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SupplyCost.sum_map_const` | 62-67 | §1 Sum of a constant map is `length · c` — the counting workhorse for flatMaps of uniform-length blocks. | — |
| `SupplyCost.length_pairTable_le` | 69-78 | §1 **Generic all-pairs bound.** Matching every element of `l` against every other yields ≤ `|l|²` candidates — the harvest shape of `matchSupply`/`deepMatchSupply`/`partialMatchSupply`. | — |
| `SupplyCost.branches_length_le` | 80-87 | §1 The branch cell has ≤ `n` vertices — discharges the `B.length ≤ n` side condition at the descent's only resolver call site. | — |
| `SupplyCost.seqsLen_length` | 89-100 | §1 Exactly `n^k` individualization sequences of length `k`. | — |
| `SupplyCost.allSeqs_length_le` | 102-118 | §1 **The oracle's `n^{O(d)}` in closed form**: `|allSeqs n d| = Σ_{k≤d} n^k ≤ (n+1)^d` — polynomial in `n` for each fixed `d`. | — |
| `SupplyCost.tableBound` | 120-121 | §1 The `(branch, sequence)` table size bound `n·(n+1)^d`. | Definition |
| `SupplyCost.deepTable_length_le` | 123-132 | §1 `|deepTable adj χ d| ≤ tableBound n d` — the size of the deep oracles' search table, bounded. | — |
| `SupplyCost.verified_length_le` | 134-137 | §1 The verified list is a filter of the candidate list, so `gB` bounds both. | — |
| `SupplyCost.matchSupplyBound` | 141-142 | §2 `matchSupply`'s work: one refinement per branch + all-pairs rank matches (`n⁴ + n⁴` shape). | Definition |
| `SupplyCost.pairSupplyBound` | 144-147 | §2 The all-pairs deep oracles' work at `T = tableBound n d`: materialisation `T·(d+1)·n³` + matches `T²·n²`. | Definition |
| `SupplyCost.refSupplyBound` | 149-152 | §2 The reference-matching oracle's work: one match per entry — the measured `|table|²→|table|` cut, as a named bound. | Definition |
| `SupplyCost.supplyCost_matchSupply_le` | 156-163 | §3 `supplyCost matchSupply ≤ matchSupplyBound n` — the first poly `supplyCost` theorem for a concrete supply (`d = 0`). | — |
| `SupplyCost.gens_matchSupply_length_le` | 165-170 | §3 `matchSupply` hands back ≤ `n²` candidates. | — |
| `SupplyCost.supplyCost_deepMatchSupply_le` | 172-180 | §3 `supplyCost (deepMatchSupply d) ≤ pairSupplyBound n d` — explicit polynomial for each fixed `d`. | — |
| `SupplyCost.gens_deepMatchSupply_length_le` | 182-185 | §3 The deep oracle hands back ≤ `tableBound²` candidates. | — |
| `SupplyCost.supplyCost_partialMatchSupply_le` | 187-197 | §3 The support-local fold oracle (F1) prices identically to the deep oracle — `≤ pairSupplyBound n d`; the fold family's consume side is paid for at the fixed `d` that discretizes one copy. | — |
| `SupplyCost.gens_partialMatchSupply_length_le` | 199-204 | §3 The support-local oracle hands back ≤ `tableBound²` candidates. | — |
| `SupplyCost.supplyCost_prunedSupply_le` | 206-216 | §3 `supplyCost (prunedSupply d) ≤ refSupplyBound n d` — the `|table|²→|table|` win, now a theorem rather than a measurement. | — |
| `SupplyCost.gens_prunedSupply_length_le` | 218-225 | §3 The pruned oracle hands back ≤ `tableBound` candidates (not `tableBound²` — the pruning's whole point, visible in the bound). | — |
| `SupplyCost.consumeNodeBound` | 229-233 | §4 The consume resolver's per-node budget from a supply's `(sB, gB)` bounds: supply work + per-candidate verification + per-branch orbit BFS. | Definition |
| `SupplyCost.consume_cost_le` | 235-244 | §4 **The consume node cost, discharged**: any supply with `supplyCost ≤ sB` and `|gens| ≤ gB` gives `(consume S adj χ B).2 ≤ consumeNodeBound n sB gB` at `|B| ≤ n` — two lemmas per future supply (F2 included) and the descent bound follows. | — |
| `SupplyCost.keepMin_length_le` | 252-257 | §5 Force's narrowing never grows the cell (`keepMin` is `B` or a filter of it). | — |
| `SupplyCost.forceThenConsume_cost_le` | 259-276 | §5 **The mixed node cost, key-abstract**: per-node `≤ n·kc + n² + consumeNodeBound` given any key-cost bound `kc` — stated against an abstract key so F3's ring key inherits it on arrival. | — |
| `SupplyCost.keyCost_lookaheadKey_le` | 278-282 | §5 The current concrete key's bound: `kc = n³ + n²` (one refinement + the read-off). | — |
| `SupplyCost.pathBound` | 286-288 | §6 The guarded single-path budget at per-node resolver cost `c₂` — definitionally the RHS of `Stall.descentCost_guard_le_encodeFree`. | Definition |
| `SupplyCost.descentCost_guard_consume_le` | 290-298 | §6 **The generic consume-only ②**: any supply with poly work/candidate bounds gives the guarded consume descent an explicit polynomial `descentCost` on every input (answer or flag alike). | — |
| `SupplyCost.descentCost_guard_consume_matchSupply_le` | 300-304 | §6 ② for the one-step oracle: `descentCost = O(n⁵)`, explicit. | — |
| `SupplyCost.descentCost_guard_consume_deepMatchSupply_le` | 306-313 | §6 ② for the bounded-depth oracle — explicit polynomial in `n` for each fixed `d` (the audit's "poly regime at bounded depth", as a theorem). | — |
| `SupplyCost.descentCost_guard_consume_partialMatchSupply_le` | 315-322 | §6 ② for the support-local fold oracle (F1) — the fold family's consume route fires AND is paid for. | — |
| `SupplyCost.descentCost_guard_consume_prunedSupply_le` | 324-331 | §6 ② for the reference-matching oracle, with the pruning win visible in the bound (`gB = tableBound`). | — |
| `SupplyCost.descentCost_guard_mixed_le` | 333-342 | §6 **The generic mixed ②** — key abstract via `kc`; F3's ring key drops in with one `keyCost` lemma. | — |
| `SupplyCost.descentCost_pruned_lookahead_le` | 344-353 | §6 **★ ② for the concrete canonizer of record** (`lookaheadKey` + `prunedSupply d`; ① side = `prunedSupply_lookahead_canonizer`): an explicit polynomial `descentCost` on every input, for each fixed `d` — the project's first end-to-end cost theorem for a concrete canonizer. | — |
| `SupplyCost.handled_answers_poly` | 357-371 | §7 **★ The ②+③ capstone.** On a `Handled` graph the guarded mixed canonizer ANSWERS and runs within the explicit `pathBound` budget — "which graphs are handled" is now the only question not riding on an undischarged `c₂`. | — |
## ChainDescent/ImprimitiveDischarge.lean

The `hImprim` discharge layer (2026-07-17): §1 forward-M1 (`G₀Irreducible ⟹ IsPrimitive`, the dual of M1.2),
§2 the vacuous discharge of the seal's imprimitive branch on the irreducible-affine class, §2b primitivity
transport along `SchemeRealizes` (realized residues covered), §3 the elementary-abelian translation scheme —
the first inhabited `AbelianConsumed` instance and the imprimitive-branch non-vacuity witness. Promoted from
`ScratchAffinePrimitive.lean` + `ScratchSchemeRealizesPrimitive.lean` (both retired).

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `irreducible_imp_isPrimitive_affineScheme` | 58-181 | **§1 Forward M1 — irreducible `G₀` ⟹ `affineScheme G₀` primitive.** The dual of `isPrimitive_affineScheme_imp_irreducible`, completing the M1 ⟺: a closed subset's difference-vectors form a `G₀`-invariant subspace (`+`-closure = the intersection-number closure at the concrete triple; scaling = char-`p` iterated addition), which irreducibility collapses to `⊥`/`⊤` ⟹ `I = {0}`/`univ`. | — |
| `affineScheme_rel_relDiff` | 183-203 | §1 Every relation of `affineScheme` is realized: `R_k` contains `(0, affineRelDiff k)` (Fact A exported — the orbital of the representative-pair difference is the relation itself). | — |
| `hImprim_affine_of_irreducible` | 219-227 | **§2 The `hImprim` discharge, irreducible-affine class.** For irreducible `G₀` the seal's carried `hImprim : ¬IsPrimitive → SchemeBlockRecovered ∨ AbelianConsumed` is a theorem — the antecedent is refuted by forward M1. Exactly the hypothesis shape every seal capstone consumes. | — |
| `hImprim_cyclicAffineScheme` | 229-235 | §2 `hImprim` discharged for `cyclicAffineScheme` (the full-generator rank-2 `K_{p^d}` case) via `G0cyc_irreducible`. | — |
| `hImprim_G0pow_of_adjoin` | 237-248 | §2 `hImprim` discharged for the **genuine cyclotomic slice** — `G0pow β` with field-generating `β` (`Algebra.adjoin = ⊤`). The imprimitive cyclotomic members (`β` in a proper subfield) are exactly what stays uncovered. | — |
| `reachesRigidOrCameron_viaAffineIrreducible_prim` | 250-271 | **§2 ★ The affine-irreducible seal with `hImprim` REMOVED** — the first seal capstone whose imprimitive branch is closed by a theorem: given irreducibility, the carried set shrinks from `{G3, hbound, hImprim}` to `{G3, hbound}` (and `hbound` loses its irreducibility antecedent). | — |
| `isPrimitive_of_schemeRealizes` | 289-358 | **§2b Primitivity transports along a scheme realization.** Conjugation `π ↦ f π f⁻¹` is a bijection `S.SchemeAutGroup ≅ X.SchemeAutGroup` intertwined by `f`; preprimitivity transports along the equivariant bijection (`MulAction.isPreprimitive_congr`), bridged both ends by `isPreprimitive_iff_isPrimitive`. | — |
| `affineScheme_hne` | 367-371 | §2b Every relation of `affineScheme` occurs — the orbital scheme's `hne` hypothesis, free via `orbMk_out`. | — |
| `isPrimitive_of_realizes_affineScheme` | 373-383 | §2b ★ The seam's primitivity leg end-to-end: a residue realized as an irreducible-affine model (`SchemeRealizes f S (affineScheme G₀)`, carried like Route C's `hreal`) is primitive. | — |
| `hImprim_of_realizes_affineScheme` | 385-396 | **§2b The `hImprim` discharge at an arbitrary REALIZED residue** — the route-2 endpoint: wherever the descent's recovered residue realizes an irreducible-affine scheme, the imprimitive branch is closed by a theorem. | — |
| `neg_mem_bot_two` | 413-423 | §3 Over `ZMod 2` negation IS the identity (`−x = x`), so `affineScheme`'s `hneg` holds for the trivial group — the char-2 entry ticket for `G₀ = ⊥`. | — |
| `translationScheme` | 425-429 | **§3 The elementary-abelian translation scheme** `affineScheme ⊥` over `F₂`: relations = difference vectors, `Aut` = the `2^d` translations. The CFI-gauge witness scheme. | Definition, `noncomputable` |
| `translationScheme_relOfPair_eq_iff` | 431-443 | §3 With `G₀ = ⊥` the orbital is exactly the difference: two pairs share a relation iff their differences are equal. | — |
| `diffClass` | 445-447 | §3 The relation class of a difference vector — the scheme's relations enumerated by `Z₂^d`. | Definition, `noncomputable` |
| `diffClass_inj` | 449-451 | §3 Distinct differences get distinct relation classes. | — |
| `diffClass_zero` | 453-454 | §3 The zero difference is the diagonal relation `R₀`. | — |
| `rel_eq_diffClass` | 456-463 | §3 Any related pair's relation is the class of its difference (via translation-invariance of `relOfPair`). | — |
| `transPerm` | 465-467 | §3 The translation permutation `x ↦ x + t` on `Fin (2^d)` through the coordinate equivalence (public replacement for the file-private `affinePermFin` at `g₀ = 1`). | Definition, `noncomputable` |
| `transPerm_apply` | 469-471 | §3 `transPerm t x = affineE (affineE.symm x + t)`. | — |
| `isAut_transPerm` | 473-482 | §3 Translations are automorphisms of the labelled scheme graph (differences are translation-invariant). | — |
| `residualAut_translationScheme_eq` | 484-495 | §3 **Every residual automorphism IS a translation** — the colour-preserving automorphisms of the complete Cayley colour graph of an abelian group are exactly the translations. | — |
| `residualAbelian_translationScheme` | 497-515 | §3 **The translation residual is ABELIAN** — the honest `ResidualAbelian` instance leg B was designed for (no reflection in characteristic 2; for odd order the reflection makes it dihedral and this FAILS — see the seal-handoff 2026-07-17 reflection finding). | — |
| `not_isBase_translationScheme` | 517-532 | §3 The translation residual is non-trivial (`d ≠ 0`): a non-zero translation moves the origin. | — |
| `abelianConsumed_translationScheme` | 534-540 | **§3 ★ The FIRST concrete `AbelianConsumed` instance** — leg B fires on the elementary-abelian translation scheme. Both `hImprim` target predicates were previously zero-instantiated (the recurring vacuity failure mode); this closes the leg-B half. | — |
| `not_isPrimitive_translationScheme` | 542-627 | §3 **The translation scheme is IMPRIMITIVE for `d ≥ 2`** — the difference classes of the subspace `{0, e₀}` form a proper non-trivial closed subset (the constructive direction of the M1 block ⟺ subspace bridge, in char 2). | — |
| `hImprim_nonvacuous_witness` | 629-638 | **§3 ★ `hImprim`'s conclusion, non-vacuously, on a genuinely IMPRIMITIVE scheme** — imprimitive ∧ (`SchemeBlockRecovered ∨ AbelianConsumed`) for the translation scheme, `d ≥ 2`: the first machine-checked witness that the seal's imprimitive branch can actually fire. | — |
## ChainDescent/Select.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Select.NodeRes` | 74-78 | **The NODE RESOLVER interface (sel rewrite increment 1, handoff §6.1 design pass)** — at a non-discrete node, pick a cell, narrow it, and return the kept children `(v, χᵥ)` WITH their already-computed refined colourings (the §6.4 hand-forward); `[] = flag` = the true mutual stall. One interface covers resolver-aware selection AND the duplicate-refine fix. | `abbrev` |
| `Select.descendS` | 80-92 | **The generalized descent** — `descend` with the per-node step delegated to a `NodeRes`: leaf on discrete, else aggregate over the resolver's children (which arrive with their colourings — no per-child refine in the recursion). Fuel per-layer, never threaded, as in `descend`. | Definition |
| `Select.canonFormS?` | 94-97 | Top-level value projection of `descendS` (root colouring from the refiner — the root has no parent to hand it forward). | Definition |
| `Select.descentCostS` | 99-101 | Top-level cost projection of the same definition (root refine billed + descent cost). | Definition |
| `Select.descendS_val_leaf` | 105-108 | A discrete node emits its leaf matrix at any fuel (mirror of `descend_val_leaf`). | — |
| `Select.descendS_val_zero` | 110-112 | Fuel exhaustion on a non-discrete node emits `none` (mirror of `descend_val_zero`). | — |
| `Select.descendS_val_succ` | 114-119 | The successor value equation: the node's value is the aggregate over the node resolver's children values (mirror of `descend_val_succ`, with the children handed forward). | — |
| `Select.descendS_cost_succ` | 121-126 | The successor cost equation: `1 +` the node resolver's cost (probe + children refinements) `+` the children's descent costs. | — |
| `Select.descendS_val_stall` | 128-134 | **The `[] = flag` channel, stated once** — a node resolver returning no children flags the node, and the flag propagates to the root through `aggregate`. For a fused selector this IS the true mutual stall (no cell resolvable). | — |
| `Select.blindNode` | 138-144 | **The blind instance = today's per-node step, packaged**: least non-singleton cell (`branches`), the resolver's narrowing, one refine per kept child. | Definition |
| `Select.blindNode_children` | 146-149 | The blind instance's children are exactly `narrow R adj χ`, each paired with its refined colouring. | `@[simp]` |
| `Select.sum_map_add` | 151-158 | Local helper: sums distribute over a pointwise-added map (the cost-rearrangement engine of `descendS_blind`). | — |
| `Select.descendS_blind` | 160-180 | **★ THE SAFETY NET — the blind instance IS today's object, as an EXACT `CostM` equation (value AND cost)**: `descendS (blindNode rf R) = descend rf R`. Everything built so far is literally the new object's special case; the sel migration proceeds against this equation with nothing proved twice. | — |
| `Select.canonFormS?_blind` | 182-186 | The top-level value equality: `canonFormS? rf (blindNode rf R) = canonForm? rf R`. | — |
| `Select.descentCostS_blind` | 188-192 | The top-level cost equality: `descentCostS rf (blindNode rf R) = descentCost rf R`. | — |
| `Select.NodeProper` | 196-202 | **Obligation 1 of the node-resolver contract** — every emitted child individualizes a vertex with a same-coloured partner (⟹ `ncol` strictly increases ⟹ the depth bound is honest) and hands forward EXACTLY its refined colouring (`vc.2 = refineV rf (indivOne χ vc.1)`) — the hand-forward is licensed by a proved equation, never trusted. (Obligation 2, `NodeEquivariant`, comes with the transport pass.) | Definition |
| `Select.nodeProper_blindNode` | 204-213 | The blind instance is `NodeProper` whenever the resolver's narrowing stays inside the branch cell (the same `hsub` the totality theorems already carry). | — |
| `Select.descendS_sound` | 221-240 | **`①a` for the generalized object, UNCONDITIONAL** — any node resolver: a leaf is only emitted at a discrete colouring, and `leafMatrix_sound` makes it a relabelling regardless of where the child colouring came from (soundness never inspects the hand-forward). | — |
| `Select.soundOptS_canonFormS?` | 242-246 | `SoundOpt` for the top-level `canonFormS?` — any refiner, any node resolver. | — |
| `Select.NodeTransportAt` | 255-260 | The generalized descent's iso-invariance at a given fuel — the graded induction statement (mirror of `TransportAt`). | Definition |
| `Select.NodeTransport` | 262-272 | **★ THE NODE-RESOLVER CONTRACT** — the children's aggregate transports under σ, fuel-graded (the IH is threaded in, so an instance may use the descent's own iso-invariance one level down, as the fused consume half must). Constrains the chosen cell AND the kept children jointly (mirror of `NarrowTransport`). | Definition |
| `Select.descendS_transport` | 274-294 | **The transport induction** (mirror of `descend_transport`): the node contract is the whole per-node obligation ⟹ `NodeTransportAt` at every fuel. | — |
| `Select.isoInvariantOptS_canonFormS?` | 296-306 | `IsoInvariantOpt` for `canonFormS?`, from refiner equivariance (root colouring only) + the node contract. | — |
| `Select.isCanonicalFormOptS_canonFormS?` | 308-313 | **★ THE CAPSTONE — `descendS` IS A CANONICAL FORM** (`①a`/`①b`/`①c` for the generalized object), modulo exactly `RefineEquivariant` + `NodeTransport`. | — |
| `Select.canonFormS?_complete` | 315-321 | Completeness, free (Stage 0a on the capstone) — mirror of `canonForm?_complete`. | — |
| `Select.canonFormS?_flag_iso_invariant` | 323-329 | The flag is iso-invariant, free — and for a FUSED node resolver the flag IS the true mutual stall, so this is `①c` for the mutual-stall semantics the design intends. | — |
| `Select.NodeEquivariant` | 333-341 | **Sufficient condition 1 (the equivariant route)** — the transported node's children are up-to-permutation the σ-images of the originals (vertex AND handed colouring); mirror of `NarrowEquivariant` at the node level. Serves force-only/structural instances; the fused selector's consume half (a `rep` pick) is NOT equivariant and discharges `NodeTransport` by a covering argument instead. | Definition |
| `Select.nodeTransport_of_nodeEquivariant` | 343-348 | An equivariant node resolver meets the contract (`aggregate_perm` + the graded IH pointwise). | — |
| `Select.nodeTransportAt_blind_iff` | 350-354 | The two objects' graded IHs coincide at the blind instance (via the `descendS_blind` safety net). | — |
| `Select.nodeTransport_blindNode` | 356-363 | **Sufficient condition 2 — CONSERVATIVITY: the OLD contract discharges the NEW one at the blind instance.** Every `NarrowTransport` instance already proved (consume for every supply, force via `KeyEquivariant`, the guarded composite) hands `descendS` its contract with no new proof. | — |
## ChainDescent/SelectNode.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Select.cellList` | 65-68 | The cell of colour `c` as a list, in index order — `branches` generalized from the least cell to any cell (they coincide at `targetColour`). | Definition |
| `Select.mem_cellList_iff` | 70-73 | Cell membership is colour equality: `v ∈ cellList χ c ↔ χ v = c`. | — |
| `Select.branches_eq_cellList` | 75-80 | At the target colour the cell IS the branch list — the definitional bridge between the fused and blind objects. | — |
| `Select.cellList_nodup` | 82-83 | Cell lists have no duplicates (filters of `finRange`). | — |
| `Select.cellList_ne_nil` | 85-95 | A non-singleton colour's cell is nonempty. | — |
| `Select.exists_partner_of_mem_cellList` | 97-109 | Every member of a non-singleton cell has a same-coloured partner — `exists_partner_of_mem_branches` at an arbitrary colour; feeds `NodeProper` and the widened `Reaches.step`. | — |
| `Select.cellList_transport_perm` | 111-123 | The cell of a FIXED colour transports up to permutation (colour values are canonical, so no colour translation appears) — mirror of `branches_transport_perm`. | — |
| `Select.nonSingletonColours_transport` | 125-133 | The non-singleton colour set is literally invariant under transport — the first half of `targetColour_transport`, exposed because the fused selector filters the SET, not only its min. | — |
| `Select.keepMin_subset` | 137-139 | Generic-`B` form: the forced set sits inside its base list. | — |
| `Select.keepMin_ne_nil` | 141-152 | Generic-`B` form: `keepMin` never empties a nonempty base list. | — |
| `Select.keepMin_nodup_of_nodup` | 154-158 | Generic-`B` form: `keepMin` preserves nodup. | — |
| `Select.mem_keepMin_of_aut'` | 160-169 | `Force.mem_keepMin_of_aut` at an arbitrary base list: a colour-automorphism image of a kept vertex is kept whenever it is in the base at all (an equivariant key is constant on orbits). | — |
| `Select.keepMin_transport_perm` | 171-198 | `keepMin` transports over any permutation-related pair of base lists — the generic-`B` core of `Force.narrowEquivariant_forceBy` (which is this at `B = branches`). | — |
| `Select.cellNarrowV` | 202-207 | The per-cell mixed narrowing against an ALREADY-COMPUTED verified list `V` — the shared-probe form (trap #2: phrasing on `S` re-evaluates the supply once per probed cell, measured ~10× per node). | Definition |
| `Select.cellNarrow` | 209-215 | **The mixed narrowing of the cell of colour `c`**: per-cell `keepMin`, then one orbit representative per verified-automorphism orbit from the node's ONE shared verified list. | Definition |
| `Select.cellNarrow_targetColour` | 217-223 | At the target colour the per-cell narrowing IS `narrow (forceThenConsume key S)` — the blind object's step, recovered exactly. | — |
| `Select.rep_mem_cellList` | 225-231 | An orbit representative stays in its vertex's cell (verified automorphisms preserve colour). | — |
| `Select.rep_mem_keepMin_cell` | 233-243 | **The per-cell forced set is a union of orbits** (mirror of `Composite.rep_mem_forcedSet`): a kept vertex's representative is itself kept — consume inside the cell never escapes the per-cell argmin. | — |
| `Select.cellNarrow_subset` | 245-248 | The per-cell narrowing stays inside its cell. | — |
| `Select.cellNarrow_ne_nil` | 250-260 | A non-singleton cell's narrowing is nonempty — so "narrowed to ≤ 1" means exactly one, and a committed cell always yields a child. | — |
| `Select.selColourV` | 264-268 | The selector against an already-computed verified list (shared-probe form). | Definition |
| `Select.selColour` | 270-274 | **The selected colour: least colour whose cell the mixed narrowing collapses to ≤ 1**; `none` = the TRUE MUTUAL STALL. Design pin: "makes progress" = narrows to ≤ 1, NOT strictly. | Definition |
| `Select.selColour_def` | 276-280 | The reasoning-side unfolding of `selColour` (a filtered `Finset.min` — the `V`-sharing is runtime-only). | — |
| `Select.selColour_spec` | 282-288 | A selected colour is a non-singleton colour whose cell narrowed to ≤ 1. | — |
| `Select.selColour_none` | 290-302 | The flag fires only at a true mutual stall: NO non-singleton cell narrows to ≤ 1. | — |
| `Select.selColour_of_target_resolvable` | 304-322 | **★ The dominance hook**: if the least cell resolves, it is the selected cell (min over a subset containing the superset's min) — what makes "no strength increase" a theorem. | — |
| `Select.nsColours` | 324-327 | The non-singleton colours as a COMPUTABLE list (`Finset.toList` is noncomputable; the probe's bill must `#eval`). | Definition |
| `Select.cellList_length_eq_card` | 329-336 | A cell's list length is its `Finset` card — the computable/`nonSingletonColours` bridge. | — |
| `Select.mem_nsColours_iff` | 338-343 | `nsColours` has exactly the `nonSingletonColours` membership. | — |
| `Select.selProbeCost` | 345-352 | The probe's bill: supply once per node, one verification per candidate, per cell one key evaluation per member plus scan plus orbit BFS — cells partition `V`, so the sums total one size-`n` cell's bill. | Definition |
| `Select.selNodeCore` | 354-362 | The node step against an already-computed verified list and probe bill — the shared core all `selNode` forms route through. | Definition |
| `Select.selNode` | 364-378 | **★ The fused node resolver**: probe all cells against the ONE per-node supply evaluation, commit to the least resolvable colour, hand each kept child its refined colouring (§6.4 hand-forward); `[] = flag` = the true mutual stall. | Definition |
| `Select.selNode_eq` | 380-384 | The reasoning-side unfolding: `selNode = selNodeCore` at `verified S`/`selProbeCost` (definitional — the sharing is runtime-only). | — |
| `Select.selNodeFast` | 386-409 | **The RUNNABLE fused resolver** (trap #1 measured live: generic `refineV rf …` children ≈ 30 ms/colour-lookup — partial applications re-run the refinement): children built through `Refine.ColData`, forced once. | Definition |
| `Select.selNodeFast_eq` | 411-413 | The runnable resolver IS `selNode` at `encodeFreeFast` — definitionally (`rfl`), so every theorem transfers verbatim. | — |
| `Select.canonFormFastS?` | 415-417 | The runnable top-level fused canonizer (root colouring materialised once too). | Definition |
| `Select.canonFormFastS?_eq` | 419-424 | The runnable top-level object IS `canonFormS?` at `encodeFreeFast`/`selNode` — definitionally (`rfl`). | — |
| `Select.selNode_children_none` | 426-431 | No selected colour ⟹ no children (the flag channel of the fused instance). | — |
| `Select.selNode_children_some` | 433-441 | A selected colour's children are its narrowing, each with its refined colouring. | — |
| `Select.selNode_children_length_le_one` | 445-454 | **★ No exponential, by construction** (acceptance criterion 3): the fused resolver emits at most ONE child, unconditionally — `Stall.guard`'s job absorbed into the instance. | — |
| `Select.selNode_children_length_one` | 456-464 | A committed cell yields exactly one child (nonempty + ≤ 1). | — |
| `Select.nodeProper_selNode` | 466-476 | `NodeProper` discharged for the fused instance: every child individualizes a partnered vertex and is handed exactly its refined colouring (definitionally). | — |
| `Select.cellNarrow_length_transport` | 485-514 | Per-cell mirror of `stallEquivariant_forceThenConsume`: the narrowing's length COUNTS ORBITS meeting the per-cell forced set, and both the orbit partition and the forced set transport — `rep` itself never has to. | — |
| `Select.selColour_transport` | 516-527 | **★ The chosen colour transports as a VALUE** (mirror of `targetColour_transport`, with the resolvability conjunct riding on the orbit count) — why choosing a CELL is canonical while a within-cell vertex pick is not. | — |
| `Select.branchValS_transport` | 529-537 | Per-branch value transport for the generalized descent (mirror of `Descend.branchVal_transport`). | — |
| `Select.branchValS_eq_of_isColAut` | 539-549 | The covering witness at the `descendS` level: a verified automorphism makes two branches value-equal (`branchValS_transport` at `σ = α`). | — |
| `Select.aggregate_cellNarrow_eq` | 551-571 | The per-cell covering step (mirror of `coveringOfAt_guarded`'s un-stalled branch): the aggregate over kept representatives equals the aggregate over the per-cell forced set. | — |
| `Select.nodeTransport_selNode` | 573-623 | **★★★ The fused instance meets the node contract** from exactly the guarded blind object's hypotheses (`KeyEquivariant` + `SupplyEquivariant` — NO new class): chosen colour transports; per-cell covering on each side; the forced set transports with value-equal entries. | — |
| `Select.selNode_canonizer` | 627-636 | **★★★ The fused canonizer** — ①a/①b/①c for the resolver-aware selector; its flag is the TRUE mutual stall. | — |
| `Select.selNode_match_canonizer` | 638-644 | The first CONCRETE fused canonizer (`encodeFreeFast` + `lookaheadKey` + `matchSupply`) — no hypothesis carried. | — |
| `Select.cellNarrow_congr` | 648-654 | `SameOrbits` supplies give the same per-cell narrowing (`rep_congr` pointwise). | — |
| `Select.selColour_congr` | 656-663 | `SameOrbits` supplies select the same colour. | — |
| `Select.selNode_children_congr` | 665-675 | `SameOrbits` supplies emit the same children (values; costs may differ — the point). | — |
| `Select.descendS_selNode_val_congr` | 677-695 | The fused descents over `SameOrbits` supplies compute the same VALUE at every fuel. | — |
| `Select.canonFormS?_selNode_congr` | 697-700 | The fused canonizers over `SameOrbits` supplies are the same function (value side). | — |
| `Select.selNode_canonizer_of_sameOrbits` | 702-713 | **★★ The reduction, fused** (mirror of `guarded_mixed_canonizer_of_sameOrbits`): a pruned supply inherits the fused capstone from any orbit-equal equivariant reference — NO equivariance proof of its own. | — |
| `Select.selNode_pruned_canonizer` | 715-722 | The fused canonizer at the record supply (`prunedSupply d`), every depth — via the fused `SameOrbits` reduction. | — |
| `Select.exists_targetColour_of_not_discrete` | 731-739 | A non-discrete colouring has a target colour. | — |
| `Select.aggregate_singleton` | 741-744 | `aggregate [x] = x` — the single-child descent step reads off. | — |
| `Select.descendS_selNode_val_of_guard` | 746-793 | The fuel-graded dominance induction: wherever the guarded blind descent answers, the fused descent answers with the SAME value (blind survives ⟹ least cell resolved ⟹ least resolvable = least ⟹ identical step). | — |
| `Select.canonFormS?_selNode_dominates` | 795-803 | **★★ THE DOMINANCE THEOREM** (acceptance criterion 1): same refiner/key/supply — wherever the guarded blind object answers, the fused object answers with the SAME canonical form. The residue can only shrink; no resolver-strength increase anywhere. | — |
| `Select.selNode_stall_iff` | 807-828 | **★ The flag semantics `Publication` §1 names, as a characterization**: the fused resolver emits no child iff NO non-singleton cell narrows to ≤ 1 (contrast `Stall.stalled`, which reads only the least cell). | — |
| `Select.NodeResolved` | 837-839 | The fused resolver can act: SOME non-singleton cell narrows to ≤ 1 — strictly weaker per node than `Cost.CellResolved` at the same key/supply strength. | Definition |
| `Select.HandledS` | 841-844 | The sel-aware capability predicate: every reached non-discrete node has some resolvable cell. | Definition |
| `Select.nodeResolved_of_cellResolved` | 846-855 | The blind payload implies the fused one node-by-node: a resolved least cell IS a resolvable cell. | — |
| `Select.handledS_of_handled` | 857-860 | **★ The residue DEFLATES**: `Handled ⟹ HandledS`, same key, same supply. | — |
| `Select.residue_of_not_handledS` | 862-865 | Contrapositive: the sel-aware residue sits INSIDE the blind residue. | — |
| `Select.handledS_of_sameOrbits` | 867-874 | `HandledS` transfers along `SameOrbits` (the fused object reads the supply only through its orbits). | — |
| `Select.handledS_of_seal` | 876-883 | The seal populates the sel-aware predicate too: depth + `∀T` localisation ⟹ `HandledS` for the deep oracle (through the widened `handled_of_seal`). | — |
| `Select.descendS_ne_none_reaches` | 887-919 | Totality for the generalized descent (mirror of `descend_ne_none_reaches`): a `NodeProper` resolver emitting a child at every reached non-discrete node reaches a leaf — the widened partner-form `Reaches` is exactly what the induction needs. | — |
| `Select.selNode_ne_nil_of_nodeResolved` | 921-928 | A `NodeResolved` node is never a stall for the fused resolver. | — |
| `Select.answersS_of_handledS` | 930-942 | **★★ The answers theorem**: the fused canonizer ANSWERS on every `HandledS` graph — with `handledS_of_handled` it recovers every blind answers-instance. | — |
| `Select.not_handledS_if_flagS` | 944-950 | ③a for the fused object: the flag names the sel-aware residue — which sits inside the blind residue. | — |
| `Select.descendS_cost_leaf` | 954-957 | The generalized descent's leaf cost is 1. | — |
| `Select.descendS_cost_zero` | 959-961 | The generalized descent's fuel-0 non-leaf cost is 1. | — |
| `Select.descendS_cost_le_of_le_one` | 963-1002 | The single-path cost bound for the generalized descent (mirror of `descend_cost_le_of_resolved`) — the fan-out hypothesis is ≤ 1, which `selNode` meets BY CONSTRUCTION with no firing hypothesis. | — |
| `Select.descentCostS_le_of_le_one` | 1004-1013 | The top-level ② shape for the generalized object. | — |
| `Select.selNode_cost_none` | 1015-1021 | The stall node bills exactly the probe. | — |
| `Select.selNode_cost_some` | 1023-1032 | A committed node bills the probe plus its children's refinements. | — |
| `Select.selNode_cost_le` | 1034-1052 | The fused resolver's per-node bill: the probe plus at most ONE child refinement. | — |
| `Select.cellList_length_le` | 1054-1057 | Every cell has at most `n` members. | — |
| `Select.nsColours_length_le` | 1059-1063 | At most `n` non-singleton colours. | — |
| `Select.selProbeBound` | 1065-1068 | The probe's budget, coarsely: ≤ `n` cells × (`n` keys + scan + `n` orbit-BFS runs against ≤ `gB` generators). | Definition |
| `Select.selProbeCost_le` | 1070-1103 | The probe is bounded by `selProbeBound` from supply-cost, candidate-count and per-vertex key-cost bounds — the fused analogue of `consume_cost_le`. | — |
| `Select.descentCostS_selNode_pruned_lookahead_le` | 1105-1122 | **★★ ② end-to-end for the fused canonizer of record** (`lookaheadKey` + `prunedSupply d`): explicit polynomial on EVERY input, per fixed `d` — and unlike the guarded bound it carries no `ResolvedAll`. | — |
| `Select.descentCostS_selNode_match_lookahead_le` | 1124-1138 | The same for the one-step oracle: explicit polynomial, no hypotheses. | — |
| `Select.selNode_pruned_record` | 1140-1155 | **★★★ The fused capstone of record — ①+②+③a in one place**: sound/complete/flag-iso-invariant, explicit polynomial budget unconditionally, flag = the sel-aware residue (inside the blind residue). | — |
| `Select.nsList` | 1171-1173 | The vertices of the non-singleton cells — the all-cells harvest roots, computably. | Definition |
| `Select.nsList_length_le` | 1175-1178 | At most `n` harvest roots. | — |
| `Select.allCellsMatchSupply` | 1180-1189 | **★ The all-cells colour-match supply** — `matchSupply` with the harvest widened from the least cell to every non-singleton cell (untrusted as always; the exposure witness's enabler). | Definition |
| `Select.mem_gens_allCellsMatchSupply_iff` | 1191-1204 | Membership characterised: exactly the candidates built on ordered pairs of harvest roots. | — |
| `Select.cellList_length_transport` | 1206-1209 | Per-colour cell size is transport-invariant (list form of `cellOf_card_transport`). | — |
| `Select.nsList_transport_perm` | 1211-1230 | The harvest roots transport up to permutation (mirror of `branches_transport_perm`). | — |
| `Select.gensEquivariant_allCellsMatchSupply` | 1232-1254 | **★★ The all-cells supply is equivariant** (mirror of `gensEquivariant_matchSupply`): candidates conjugate, roots transport — the fused capstone instantiates with no new hypothesis. | — |
| `Select.supplyEquivariant_allCellsMatchSupply` | 1256-1258 | The verified list conjugates (via `supplyEquivariant_of_gensEquivariant`). | — |
| `Select.selNode_allCellsMatch_canonizer` | 1260-1267 | The fused canonizer over the all-cells harvest — concrete, no hypotheses; the instance the exposure witness runs. | — |
| `Select.supplyCost_allCellsMatchSupply_le` | 1269-1277 | The all-cells harvest prices exactly like `matchSupply` (`|nsList| ≤ n` replaces `|branches| ≤ n`). | — |
| `Select.gens_allCellsMatchSupply_length_le` | 1279-1284 | At most `n²` candidates. | — |
| `Select.descentCostS_selNode_allCells_le` | 1286-1300 | ② for the fused all-cells object: explicit polynomial on every input. | — |
| `Select.branches_subset_nsList` | 1302-1318 | `nsList` extends `branches`: every branch vertex is a harvest root — the all-cells harvest only widens. | — |

## ChainDescent/SelectWitness.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `SelectWitness.Z4S` | 58-63 | The Z₄ chiral subdivided wheel (n = 14, `Aut = Z₄`): least cell = the apex 2-orbit whose pins keep `γ²` alive — the exposure-witness graph (blind + least-rooted harvest FLAGS; fused + all-cells harvest ANSWERS). | Definition |
| `SelectWitness.rootZ` | 65 | The witness graph's materialised root colouring. | Definition |
## ChainDescent/FoldSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Fold.sameCellRel` | 61-63 | Same-cell adjacency — the VERTICAL edges of a fold cover (copies of one core vertex are 1-WL twins). | Definition |
| `Fold.crossCellRel` | 65-67 | Cross-cell adjacency — the horizontal (within-copy) edges; removing the vertical edges leaves the copies. | Definition |
| `Fold.sameCellRel_transport` | 69-72 | The vertical relation transports under relabelling. | — |
| `Fold.crossCellRel_transport` | 74-77 | The horizontal relation transports under relabelling. | — |
| `Fold.relStep` | 81-83 | One closure round: everything reached plus every `rel`-successor. | Definition |
| `Fold.relComp` | 85-88 | The `rel`-component of `b` as computed (`n` closure rounds) — **no convergence proof is ever needed**: every downstream statement is relative to what it computes. | Definition |
| `Fold.mem_relStep_iff` | 90-92 | Membership through one closure round. | — |
| `Fold.mem_relComp_transport` | 94-125 | **★ Components transport, membership-level** — the engine of everything equivariant in the file. | — |
| `Fold.uniqueMem` | 137-141 | The unique vertex satisfying `P`, if exactly one — the fiber-partner lookup; canonical, no representative chosen. | Definition |
| `Fold.uniqueMem_eq_some` | 143-148 | The lookup returns the unique witness. | — |
| `Fold.uniqueMem_transport` | 173-185 | The lookup transports: `uniqueMem` of the conjugated predicate is the `σ`-image. | — |
| `Fold.swapFun` | 189-198 | The fiber-wise copy swap (spec form): a copy-`u₁` vertex maps to its unique same-cell-component partner in copy `u₂`, mirrored; identity elsewhere. | Definition |
| `Fold.swapCand` | 200-206 | **The structural candidate constructor** (spec form): keep the swap iff it is an involution (decidable); untrusted — `Consume.verified` re-checks `IsColAut`. | Definition |
| `Fold.swapFunFast` | 215-224 | ζ-equal rfl-twin of `swapFun` — components bound once per call (~500× runtime, measured). | Definition |
| `Fold.swapFunFast_eq` | 226 | The twin IS the spec (`rfl`, ζ-reduction) — every `swapFun` theorem applies unchanged. | — |
| `Fold.swapCandFast` | 228-232 | ζ-equal rfl-twin of `swapCand` — the form `foldSupply` evaluates. | Definition |
| `Fold.swapCandFast_eq` | 234 | The twin IS the spec (`rfl`). | — |
| `Fold.swapFun_eq_of_foldSwap` | 238-272 | **★ The reconstruction, pointwise:** if `τ` maps each copy-`u₁` vertex to its UNIQUE fiber partner in copy `u₂` (mirrored) and is the identity off both copies, `swapFun` computes exactly `τ` — the hypotheses are the cover geometry. | — |
| `Fold.swapCand_eq_of_foldSwap` | 274-290 | **★★ THE RECONSTRUCTION:** a clean fold pair's copy-swap automorphism is returned exactly. | — |
| `Fold.swapFun_conj` | 294-334 | The raw swap conjugates under `σ` (via component and lookup transport). | — |
| `Fold.swapCand_conj` | 353-368 | The constructor transports up to conjugation, **including its failure mode** — the `matchCol_transport` analogue. | — |
| `Fold.foldSupply` | 372-378 | **★ THE STRUCTURAL FOLD SUPPLY** — every branch-cell pair seeds a copy-swap candidate; involution gate + verification filter the junk; **no refinement involved**, so a refinement-blind copy costs nothing. Billed flat `|cell|²·n⁵`. | Definition |
| `Fold.mem_gens_foldSupply_iff` | 380-389 | Generator membership = some branch-cell seed pair's candidate. | — |
| `Fold.gensEquivariant_foldSupply` | 393-415 | **★★ The supply is equivariant** — the pair enumeration is the branch cell (transports) and the candidate conjugates; membership-only reasoning, no representative chosen (trap #7). | — |
| `Fold.supplyEquivariant_foldSupply` | 417-418 | Packaged for the guard and the fused selector. | — |
| `Fold.wordReach_foldSupply` | 422-435 | **Graded firing, per pair:** a verified swap carrying `u₁` to `u₂` puts the pair into the verified `WordReach`; compositions (`τ₁₂·τ₁₃·τ₁₂`) come free as words. | — |
| `Fold.cellIsOrbit_foldSupply` | 437-446 | **★★★ THE ORACLE FIRES:** every branch pair connected by a verified swap ⟹ the cell is one orbit, one branch — with no refinement involved. | — |
| `Fold.foldSupply_guarded_canonizer` | 450-456 | **★★★ The guarded (blind) mixed canonizer over the structural fold supply** — no carried hypotheses. | — |
| `Fold.foldSupply_selNode_canonizer` | 458-465 | **★★★ The FUSED (resolver-aware) canonizer over the structural fold supply** — the selector probes every cell with its verified list, so a fold cell resolves wherever it sits in the colour order. F2a capstone of `docs/chain-descent-fold-tower-plan.md`. | — |
## ChainDescent/DeckSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deck.candPred` | 72-83 | Forcing predicate: `w` is a viable image for `v` under partial map `m` — colour agrees, and adjacency (both directions, full weight equality, non-edges included) plus injectivity agree with every assigned vertex. Generalizes the C# induced-4-cycle rule. | Definition |
| `Deck.forceRound` | 85-92 | One forcing round (spec form): an unassigned vertex is assigned iff its candidate set is a `uniqueMem` singleton — no choice, ambiguity waits or stalls. | Definition |
| `Deck.seedMap` | 94-96 | The one-point seed `u₁ ↦ u₂`. | Definition |
| `Deck.propagate` | 98-102 | `n` forcing rounds from the seed (monotone; a no-assignment round is a fixpoint; no convergence proof needed — statements are relative to the computed value). | Definition |
| `Deck.deckFun` | 104-106 | Candidate map: propagated image where assigned, identity elsewhere (junk is caught by the gates). | Definition |
| `Deck.deckCand` | 108-115 | **The propagation candidate**: forward and reverse propagations gated as two-sided inverses; `Consume.verified` re-checks `IsColAut`. Stalls/contradictions fail the gate — sound by construction. | Definition |
| `Deck.uniqueFilter` | 119-124 | List-based unique lookup — value-equal to `uniqueMem` without the `Finset.choose`/`∃!`-decide overhead at evaluation. | Definition |
| `Deck.uniqueFilter_eq_uniqueMem` | 126-166 | The evaluation lookup computes exactly `uniqueMem` — every `uniqueMem` lemma transfers to the fast path. | — |
| `Deck.candPredV` | 168-177 | Vector-state forcing predicate — all reads are `.get` on forced data (trap #1 discipline). | Definition |
| `Deck.roundVecD` | 179-186 | One forcing round, **data → data** (the `Refine.roundVec` pattern). The function-typed round compounds exponentially under iterate — measured live this build. | Definition |
| `Deck.propagateVec` | 188-191 | The runnable propagation (Vector-state rounds); `propagateVec_eq` transfers every spec theorem. | Definition |
| `Deck.candPredV_ofFn` | 193-210 | Bridge: the Vector predicate over `Vector.ofFn m` equals the spec predicate over `m`. | — |
| `Deck.roundVecD_ofFn` | 212-229 | Bridge, one round: `roundVecD` over `Vector.ofFn` equals `Vector.ofFn` of the spec round (the `roundVec_ofFn` shape). | — |
| `Deck.iterate_roundVecD` | 231-240 | Bridge, iterated: `k` Vector rounds equal `Vector.ofFn` of `k` spec rounds (the `iterate_roundVec` shape). | — |
| `Deck.propagateVec_eq` | 242-246 | **The runnable propagation computes exactly the reasoned-about one** — the `warmRefineVec_col_eq` shape. | — |
| `Deck.deckCandFast` | 248-256 | The runnable candidate — value-equal to `deckCand`; the `let`s bind forced Vectors (data, not functions), one propagation per side per candidate. | Definition |
| `Deck.deckCandFast_eq` | 258-265 | The runnable candidate equals the spec candidate — the supply evaluates what the theorems describe. | — |
| `Deck.forceRound_sound` | 269-306 | One round preserves the invariant `m ⊆ ρ`: a forced value is the unique constraint-satisfier and `ρ`'s value satisfies, so they coincide. | — |
| `Deck.propagate_sound` | 308-331 | **★ Soundness of the propagation**: everything assigned agrees with ANY colour-automorphism extending the seed. Corollary: ≤ 1 automorphism extends a completed seed. | — |
| `Deck.propagate_seed` | 333-348 | The seed survives every round (rounds are monotone on assignments). | — |
| `Deck.deckCand_eq_of_isColAut` | 350-384 | **★★ The reconstruction**: if a colour-automorphism `ρ` extends the seed and both propagations complete, the candidate IS `ρ`. Completion is decidable and measured, never assumed. | — |
| `Deck.mconj` | 388-390 | Conjugated partial map — the transported assignment state for the equivariance proofs. | Definition |
| `Deck.candPred_conj` | 392-428 | The forcing predicate transports: `candPred` on the relabelled graph at conjugated arguments equals `candPred` here. | — |
| `Deck.forceRound_conj` | 430-450 | One forcing round commutes with conjugation (via `uniqueMem_transport`). | — |
| `Deck.seedMap_conj` | 452-461 | The seed transports. | — |
| `Deck.propagate_conj` | 463-479 | The full propagation commutes with conjugation (round-by-round induction). | — |
| `Deck.deckFun_conj` | 481-490 | The candidate map conjugates pointwise. | — |
| `Deck.deckCand_conj` | 509-527 | The candidate transports up to conjugation, **including its failure mode** — the `swapCand_conj` analogue, so supply equivariance is the standard proof. | — |
| `Deck.deckSupply` | 531-537 | **★ The propagation supply**: every branch-cell pair seeds a propagation candidate; gates + `IsColAut` filter the junk. Cost billed flat at `|cell|²·n⁵`. | Definition |
| `Deck.mem_gens_deckSupply_iff` | 539-550 | Membership in the emitted generators = some branch-cell seed pair whose (spec) candidate is the generator. | — |
| `Deck.gensEquivariant_deckSupply` | 554-576 | **★★ The propagation supply is equivariant** — cell enumeration transports, candidate conjugates; no representative ever chosen (trap #7). | — |
| `Deck.supplyEquivariant_deckSupply` | 578-579 | `①c` in the form the resolver reads — from `gensEquivariant_deckSupply`. | — |
| `Deck.wordReach_deckSupply` | 583-595 | Graded firing, per pair: a verified propagation candidate carrying `u₁` to `u₂` puts the pair into the verified `WordReach`. | — |
| `Deck.cellIsOrbit_deckSupply` | 597-606 | **★★★ The oracle fires**: verified propagation candidates connecting every branch-cell pair certify the cell as one orbit — no refinement involved, at any generator order. | — |
| `Deck.deckSupply_guarded_canonizer` | 610-616 | **★★★ The guarded (blind) mixed canonizer over the propagation supply** — no carried hypotheses. | — |
| `Deck.deckSupply_selNode_canonizer` | 618-624 | **★★★ The fused (resolver-aware) canonizer over the propagation supply** — no carried hypotheses. | — |
| `Deck.appendSupply` | 628-630 | Supply concatenation: generators appended, costs summed — one supply object composing several harvests. | Definition |
| `Deck.mem_gens_appendSupply_iff` | 632-635 | Membership in a concatenated supply = membership in either part. | — |
| `Deck.gensEquivariant_appendSupply` | 637-649 | Concatenation preserves generator equivariance — the obligation splits. | — |
| `Deck.supplyEquivariant_appendSupply` | 651-654 | Concatenation preserves supply equivariance (the resolver-facing form). | — |
| `Deck.foldDeckSupply_selNode_canonizer` | 656-664 | **★★★ The fused canonizer over `foldSupply ++ deckSupply`** — one supply object covering mirror-tied folds (copy swaps) AND cyclic towers (rotations); guarded on both witness families. | — |
## ChainDescent/HolKey.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Hol.KeySeparates` | 94-108 | **The force-side firing predicate** (dual of `CellIsOrbit`): equal key values occur only on `Aut`-equivalent branches — graded per node, never claimed globally. | Definition |
| `Hol.keyV_eq_of_mem_keepMin` | 110-122 | Members of the narrowed set all attain the minimum key value. | — |
| `Hol.keepMin_pairwise_aut_of_separates` | 124-146 | **★ The force firing theorem**: a separating key keeps only pairwise `Aut`-equivalent branches — one orbit, which consume then collapses (the graded mirror of `cellIsOrbit_*`). | — |
| `Hol.relComp_closed` | 221-237 | The closure really is closed: a `rel`-step out of `relComp` stays inside (monotone-rounds pigeonhole — the convergence content F2a never needed). | — |
| `Hol.relComp_subset_of_closed` | 239-255 | Anything reachable from a member of a closed set is in it. | — |
| `Hol.mem_relComp_self` | 257-262 | Component membership is reflexive. | — |
| `Hol.mem_relComp_trans` | 264-267 | Component membership is transitive (via closedness). | — |
| `Hol.mem_relComp_symm` | 269-286 | Component membership is symmetric — for a symmetric relation. | — |
| `Hol.mem_relComp_congr` | 288-293 | **★ Copy-designator well-definedness**: any member of a component designates the same component. | — |
| `Hol.symSame` | 302-304 | Symmetrized same-cell (vertical) adjacency — weak components; `AdjMatrix` guarantees no symmetry. | Definition |
| `Hol.symCross` | 306-308 | Symmetrized cross-cell (horizontal) adjacency. | Definition |
| `Hol.symSame_symm` | 310-311 | The symmetrized vertical relation is symmetric (by construction). | — |
| `Hol.symCross_symm` | 313-314 | The symmetrized horizontal relation is symmetric (by construction). | — |
| `Hol.symSame_transport` | 316-320 | The symmetrized vertical relation transports. | — |
| `Hol.symCross_transport` | 322-326 | The symmetrized horizontal relation transports. | — |
| `Hol.partnerTo` | 330-334 | The unique fiber partner of `x` in the copy of `t` — F2a's one-sided lookup with the target copy designated by a vertex (no ids, no representatives). | Definition |
| `Hol.walkOk` | 336-340 | A valid L = 3 walk: the three copies pairwise distinct (membership tests only). | Definition |
| `Hol.holMoved` | 342-356 | The holonomy moved-count of `copy(v) → copy(t₁) → copy(t₂) → copy(v)`: vertices of `v`'s copy failing to return under the composed partner maps (missing/ambiguous counts as moved). | Definition |
| `Hol.holHas` | 358-361 | Is some valid walk's moved-count equal to `c`? — the signature's membership test. | Definition |
| `Hol.holSig` | 363-369 | **The holonomy signature**: the indicator vector over `[0, n]` of attained moved-counts — representative-free (trap #7) and canonical BY CONSTRUCTION (no sort/dedup, so equivariance is existential reindexing). | Definition |
| `Hol.holKey` | 371-375 | **★ The holonomy key (F3a)** — ranks a branch by its copy's monodromy/coset data, the thing 1-WL look-ahead cannot see; flat `n⁵` cost. Measured: splits the WL-merged twisted/untwisted union 3-vs-3 where `lookaheadKey` keeps 6. | Definition |
| `Hol.keyV_holKey` | 377-378 | The key's value projection is `holSig`. | `@[simp]` |
| `Hol.keyCost_holKey` | 380-381 | The key's cost projection is the flat `n⁵` bill. | `@[simp]` |
| `Hol.partnerTo_conj` | 400-407 | The partner lookup conjugates (`uniqueMem_transport` on the transported component memberships). | — |
| `Hol.walkOk_conj` | 409-416 | Walk validity transports (three component-membership rewrites). | — |
| `Hol.holMoved_conj` | 418-444 | The moved-count transports: `countP` fused over the filter, reindexed over `finRange` by σ, pointwise via the conjugated partner chain. | — |
| `Hol.holHas_conj` | 446-465 | The membership test transports — pure existential reindexing (what the indicator form buys). | — |
| `Hol.holSig_conj` | 467-470 | The signature is invariant under relabelling — map-congruence over `holHas_conj`. | — |
| `Hol.keyEquivariant_holKey` | 472-478 | **★★ The holonomy key is equivariant** — the whole `①` obligation of a force key, discharged. | — |
| `Hol.compIdx` | 524-526 | The component id: the least member index — INTERNAL (outputs consult only id-equality). | Definition |
| `Hol.compIdx_eq_iff` | 528-556 | **★ Id-equality tests exactly component membership** (symmetric relation) — the well-definedness letting the twin replace membership scans with `O(1)` id comparisons. | — |
| `Hol.compTbl` | 558-560 | The forced id-table (data, not a function — trap #1). | Definition |
| `Hol.compTbl_get` | 562-564 | Table reads are `compIdx` values. | — |
| `Hol.pfT` | 566-568 | Table-level partner lookup (`c` = the target copy's id). | Definition |
| `Hol.walkOkT` | 570-572 | Table-level walk validity. | Definition |
| `Hol.holMovedT` | 574-585 | Table-level holonomy moved-count. | Definition |
| `Hol.holSigFast` | 651-658 | **The runnable signature** — two forced id-tables per call, then `O(1)` reads everywhere. | Definition |
| `Hol.holSigFast_eq` | 660-665 | **The runnable signature computes exactly the reasoned-about one.** | — |
| `Hol.holKeyFast` | 667-669 | The runnable key — value-equal to `holKey`, so every theorem transfers. | Definition |
| `Hol.holKeyFast_eq` | 671-674 | The runnable key equals the spec key. | — |
| `Hol.keyEquivariant_holKeyFast` | 676-678 | `①` for the runnable key, by transfer. | — |
| `Hol.holKey_canonizer` | 682-690 | **★★★ The pure-force canonizer over the holonomy key** — sound, iso-invariant, always answers. | — |
| `Hol.holKey_foldDeck_guarded_canonizer` | 692-702 | **★★★ The F3a canonizer of record for the fold family (guarded blind object)**: force = holonomy, consume = `foldSupply ++ deckSupply`. | — |
| `Hol.holKey_foldDeck_selNode_canonizer` | 704-713 | **★★★ The fused (resolver-aware) mirror** — the selector probes every cell with the same force + supply pair. | — |
## ChainDescent/FoldFast.lean

The F2a evaluation constant: `foldSupplyFast`, the materialised-table twin of `foldSupply` — component-MEMBERSHIP rows forced once per supply call (NOT the F3a `compIdx` id-tables: those need a symmetric relation and F2a's spec closures are directed), with a function-level equality so every `foldSupply` theorem transfers by rewriting. Unblocked the n = 30 F3a composite measurement (`PerformanceTest` §10).

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Fold.compRow` | 48-52 | The Boolean membership row of `relComp rel b` — the closure computed once, read `n` times (trap #1: data, not a function). | Definition |
| `Fold.compRows` | 54-57 | All membership rows: entry `b` = the row of `relComp rel b`; `n` closures per table, once per supply call. | Definition |
| `Fold.compRows_get` | 59-61 | Table reads are exactly the spec membership tests. | — |
| `Fold.swapFunT` | 65-76 | `swapFun` reading the forced tables: `O(1)` membership gets + `uniqueFilter` partner scan with an `O(1)` predicate. | Definition |
| `Fold.swapFunT_eq` | 78-83 | The table form computes exactly the spec form (at the tables of the right relations). | — |
| `Fold.swapCandT` | 85-90 | The candidate constructor over the forced tables (involution gate unchanged). | Definition |
| `Fold.swapCandT_eq` | 92-101 | Table candidate = spec candidate, including the failure mode. | — |
| `Fold.foldSupplyFast` | 105-113 | **★ The materialised-table fold supply** — same enumeration, gates and cost bill as `foldSupply`; the two tables are forced once per call. | Definition |
| `Fold.foldSupplyFast_eq` | 115-119 | **★★ The twin IS the supply of record** — a function-level equality, so capstones/equivariance/firing all transfer by rewriting. | — |
| `Fold.gensEquivariant_foldSupplyFast` | 121-123 | `①c` for the fast form, by transfer. | — |
| `Fold.supplyEquivariant_foldSupplyFast` | 125-127 | `StallEquivariant` feed for the fast form, by transfer. | — |
| `Fold.holKey_foldDeckFast_selNode_canonizer` | 131-141 | **★★★ The F3a canonizer of record with every component in its runnable form**: force = `holKeyFast`, consume = `foldSupplyFast ++ deckSupply`, fused selector. | — |

## ChainDescent/MultipedeWitness.lean

OFF the build path (like `PerformanceTest`/`SelectWitness`; `lake build ChainDescent.MultipedeWitness`, ~2.5 min). The F2-at-scale witness on a genuinely WL-blind core: the native-Z₂ multipede (C# `BuildNativeMultipede` port) has EXHAUSTIVE pin-blindness (no pin cascades — `#guard`ed for all 12 segment pins), so on its matched double the matching supplies are dead as a matter of structure while `foldSupplyFast` consumes the copy direction refinement-free (4-fan → 2); the remaining gauge pair is the IR blind spot, attributed to force/the Smith solve (the F3b gate).

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `MultipedeWitness.mpE` | 60-70 | Segment–gadget incidence of the native-Z₂ multipede over the 6-circulant `{0,1,3}`. | Definition |
| `MultipedeWitness.mp36` | 72 | The 36-vertex multipede core (12 segment states + 24 sum-zero gadgets). | Definition |
| `MultipedeWitness.mpTypes` | 74-75 | Typed seed: segment position per segment pair; gadgets one class. | Definition |
| `MultipedeWitness.mp36Root` | 77 | Materialised root colouring of the core (`ColData`, trap #1). | Definition |
| `MultipedeWitness.dmp72` | 92-96 | The matched double: two copies + the perfect matching `i ↔ 36+i` (`Aut = Z₂`, rigid core). | Definition |
| `MultipedeWitness.dmpTypes` | 98 | The doubled typed seed. | Definition |
| `MultipedeWitness.dmp72Root` | 100 | Materialised root colouring of the double. | Definition |
## ChainDescent/ScratchTreeMeasure.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ScratchTreeMeasure.cyc` | 11-12 | — | Definition |
| `ScratchTreeMeasure.rootCol` | 14-17 | — | Definition |
| `ScratchTreeMeasure.a7` | 18 | — | Definition |
| `ScratchTreeMeasure.c7` | 19-21 | — | Definition |
| `ScratchTreeMeasure.seed7` | 22-38 | — | Definition |

## ChainDescent/TreePrune.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `TreePrune.GWord` | 67-70 | `w` is a **product of elements of `G`** (empty product = `1`). The pruning's witness type: an entry is dropped only when exhibited as `w · e` for such a `w`. | Inductive |
| `TreePrune.GWord.comp` | 72-76 | `GWord` is closed under multiplication — needed because the tree induction composes a level's word with the prefix's. | — |
| `TreePrune.isColAut_of_gword` | 78-84 | A word in **verified** generators is itself a colouring-preserving automorphism (`IsColAut.one`/`comp`). This is what lets `deepCol_aut` apply to a pruning witness. | — |
| `TreePrune.Reaches` | 86-89 | `g` moves **every** point within its `WordReach` class over `K` — i.e. `g` acts inside the orbit partition `K` proves. The property that is closed under **products**, which `WordReach` (one generator at a time) is not. | Definition |
| `TreePrune.Reaches.one` | 91-93 | The identity acts inside every orbit partition. | — |
| `TreePrune.Reaches.gen` | 95-96 | A generator acts inside the partition it generates (one `WordReach` step). | — |
| `TreePrune.Reaches.mul` | 98-101 | **`Reaches` is closed under composition** — the crux of the whole file: a pruned-away candidate is recovered as a *product*, and this is what makes that harmless. | — |
| `TreePrune.Reaches.ofGWord` | 103-107 | Every word in a generator sublist acts inside the larger list's orbit partition. | — |
| `TreePrune.wordReach_of_reaches` | 109-115 | **★ THE BRIDGE.** If every generator of `K₁` acts inside `K₂`'s orbit partition, `K₂` proves everything `K₁` does — `K₁`'s generators need not be *in* `K₂`, being **products** of `K₂`'s is enough. This is what `SameOrbits` needs and what set-equality arguments cannot supply. | — |
| `TreePrune.Entry` | 123-124 | A search-tree node: branch vertex + the sequence individualized after it. | `abbrev` |
| `TreePrune.actEntry` | 126-127 | The permutation action on an entry — **the whole entry, vertex included**. ⚠ Pruning the sequence while holding the vertex fixed is *not* licensed; `deepCol_aut` transports `v :: s` as a unit. | Definition |
| `TreePrune.actEntry_one` | 129-130 | The action is unital (the base case of the tree induction). | — |
| `TreePrune.actEntry_mul` | 132-134 | The action composes — how the tree induction chains a level's witness onto the prefix's. | — |
| `TreePrune.wordsOf` | 136-140 | All products of at most `K` generators. **Completeness is not needed for correctness**: a shorter list prunes less, never wrongly, because every drop carries its own witness. `K` is a free efficiency knob. | Definition |
| `TreePrune.gword_of_mem_wordsOf` | 142-153 | Everything `wordsOf` enumerates really is a `GWord` — the soundness of the pruning test's witness supply. | — |
| `TreePrune.reducible` | 155-157 | The pruning test: has this entry already been exhibited as a known-word image of a kept one? Decidable, and it *produces* the witness it tests for. | Definition |
| `TreePrune.reduceStep` | 159-162 | One pruning pass: keep an entry unless it is a known-word image of one already kept. | Definition |
| `TreePrune.entryReduce` | 164-165 | Prune a whole level by folding `reduceStep` from the empty accumulator. | Definition |
| `TreePrune.foldl_subset` | 167-178 | The accumulator only ever grows through the fold. | — |
| `TreePrune.foldl_subset_append` | 180-196 | The fold's result stays inside `acc ++ L` — nothing is invented. | — |
| `TreePrune.foldl_subset_cons` | 198-204 | One step of the accumulator-growth fact, extracted for reuse. | — |
| `TreePrune.foldl_covers` | 206-228 | **★ THE PRUNING IS WITNESSED.** Everything fed to `entryReduce` is a known-word image of something kept. The fold invariant that replaces the Schreier-Sims BFS the design originally anticipated. | — |
| `TreePrune.entryReduce_covers` | 230-233 | `foldl_covers` at the empty accumulator — the usable form. | — |
| `TreePrune.entryReduce_subset` | 235-239 | Pruning only removes; the kept set is a sub-collection of the input level. | — |
| `TreePrune.entryLevels` | 241-247 | **The pruned search tree, level by level.** Level `0` is the branch cell (already pruned — the `v`-side prune); level `k+1` extends each **kept** level-`k` entry by every vertex and prunes again. Descendants of a dropped node are never generated. | Definition |
| `TreePrune.entryLevels_spec` | 249-265 | Every kept entry is a genuine `(branch vertex, sequence of that exact length)` pair. | — |
| `TreePrune.exists_rep` | 267-301 | **★★★ THE TREE COVERS THE FULL ENUMERATION.** Every `(branch, sequence)` pair of the *unpruned* space is the image, under a **word in `G`**, of an entry the tree actually kept. The induction is the whole point: `(v, s ++ [x]) = w · (t.1, t.2 ++ [w⁻¹ x])`, and that child is *generated* from the kept `t`. This is nauty's tree-prune correctness, proved. | — |
| `TreePrune.prunedEntries` | 303-306 | The kept entries at depth `d` — every level up to `d`. | Definition |
| `TreePrune.mem_prunedEntries_of_level` | 308-311 | A kept level-`k` entry (`k ≤ d`) is a kept depth-`d` entry. | — |
| `TreePrune.prunedEntries_spec` | 313-317 | Kept entries are genuine branch/short-sequence pairs — so they are rows of the **full** table too. | — |
| `TreePrune.exists_rep_prunedEntries` | 319-324 | `exists_rep` packaged at depth `d`: every full-space entry reduces to a pruned one. | — |
| `TreePrune.entryData` | 328-330 | The colouring an entry reaches, materialised **once** as `ColData` (standing trap #1 — never a `… → Colouring n`). | Definition |
| `TreePrune.entryData_col` | 332-336 | The materialised colouring **is** the reasoned-about `deepCol`. | — |
| `TreePrune.mem_deepTable_of_prunedEntries` | 338-343 | A pruned entry is a genuine row of the full `deepTable` — so anything the tree finds, the full oracle also has. Direction A runs on this. | — |
| `TreePrune.treeTable` | 345-348 | The pruned table: one materialised colouring per kept entry. | Definition |
| `TreePrune.treeRef` | 350-352 | The reference entry of a pruned table: the first row that discretizes. | Definition |
| `TreePrune.treeGens` | 354-357 | The emitted generators: the seed group (the words the pruning spent) **plus** the reference matches. Emitting the seed is what makes the closure argument land inside the tree's own verified list. | Definition |
| `TreePrune.treeSupply` | 359-367 | **★ THE TREE-PRUNED ORACLE.** Grow the search tree level by level, prune each level by the seed group's orbits, match every survivor against one discrete reference, emit seed + matches. Untrusted on **both** counts — `Consume.verified` re-checks everything, so a junk seed costs pruning, never correctness. | Definition |
| `TreePrune.gens_treeSupply` | 369-371 | The supply's generator projection, by `rfl`. | — |
| `TreePrune.mem_treeGens` | 373-386 | Membership in the emitted list, unpacked into "seed element or reference match". | — |
| `TreePrune.mem_treeGens_of_seed` | 388-392 | Once the reference exists, every seed generator is emitted. | — |
| `TreePrune.mem_treeGens_of_match` | 394-399 | Once the reference exists, every reference match is emitted. | — |
| `TreePrune.treeRef_mem` | 401-402 | The reference is one of the table's own rows. | — |
| `TreePrune.discrete_treeRef` | 404-408 | The reference row is discrete (it is the `find?` predicate) — required for `matchCol` to fire at all. | — |
| `TreePrune.treeRef_isSome_of_discrete` | 410-417 | A discrete row forces the reference to exist. | — |
| `TreePrune.isColAut_of_gword_seed` | 434-435 | Every word in the seed group is an automorphism — the seed is read through `verified`, so this needs no hypothesis on the seed supply. | — |
| `TreePrune.exists_pruned_transport` | 437-450 | **★ THE COVERING, IN COLOURINGS.** Every colouring the *full* space reaches is the `w`-transport of one the **pruned tree** reaches, for `w` an automorphism. `exists_rep` plus `OrbitPrune.deepCol_aut`. | — |
| `TreePrune.exists_pruned_transport_word` | 452-464 | The same, carrying the word itself — needed to *left-multiply* the candidate in the closure step. | — |
| `TreePrune.mem_treeTable` | 466-468 | A kept entry's row is in the pruned table. | — |
| `TreePrune.exists_treeRef_of_full` | 470-483 | **The tree discretizes whenever the full table does.** A discrete full entry transports onto a pruned one and discreteness is transport-invariant — so the tree never silently loses its reference by pruning. | — |
| `TreePrune.seed_subset_verified` | 485-492 | Every seed generator is emitted **and verified** by the tree — so the closure's `u` factor lands inside the tree's own verified list, not outside it. | — |
| `TreePrune.exists_full_ref_of_mem_gens` | 496-505 | If the tree emits anything it found a discrete entry, which is a row of the full table too. | — |
| `TreePrune.verified_tree_subset_deep` | 507-517 | **Direction A.** The tree emits only automorphisms, and once *any* entry discretizes the full oracle contains **every** automorphism (`PrunedSupply.exists_image_entry`) — so this direction needs no closure at all. | — |
| `TreePrune.deep_reaches_tree` | 521-577 | **★★★ THE CLOSURE (direction B).** For a full-oracle generator `g`: the reference sits at a pruned entry `e`, the *full* entry `g · e` reduces to a pruned `t` by a word `u`, and `some g = matchCol r (g·r) = (matchCol r (deepCol t)).map (u * ·)` gives `g = u * c` with `c` **kept**. `c = u⁻¹ * g` is an automorphism (`IsColAut.inv`/`comp`) so `c` verifies; `u` is a seed word the tree also emits. Hence `g` acts inside the orbit partition the tree proves. | — |
| `TreePrune.sameOrbits_treeSupply` | 583-591 | **★★★ `treeSupply` PROVES THE SAME ORBITS AS `deepMatchSupply`** — the *entire* `①` obligation of the tree-pruned supply, and it holds for an **arbitrary untrusted seed supply**. Direction A is membership; direction B is the group closure. | — |
| `TreePrune.treeSupply_guarded_canonizer` | 593-602 | **★★★ THE TREE-PRUNED MIXED CANONIZER.** `①a`/`①b`/`①c` for the guarded composite over the orbit-pruned supply — inherited wholesale through the `SameOrbits` reduction, with **no** equivariance proof on `treeSupply` (which has none: it picks orbit representatives). | — |
| `TreePrune.treeSupply_lookahead_canonizer` | 604-611 | The concrete instance: tree-pruned supply seeded by the reference-matching supply one level shallower, with `lookaheadKey`. | — |
| `TreePrune.cellIsOrbit_treeSupply` | 613-618 | Firing transfers too — `Handled`/`CellIsOrbit`/`CellResolved` are unchanged by the pruning, which is exactly why running on `SameOrbits` rather than equivariance was the right architecture. | — |
## ChainDescent/Deck2.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deck2.contFrom` | 74-77 | Continue F2b forcing rounds from an arbitrary partial state (`propagate` = `contFrom` of the seed map); the second-seed continuation runs from the stalled state. | Definition |
| `Deck2.setSeed` | 79-81 | Add a second seed `v₁ ↦ v₂` onto a (stalled) partial assignment. | Definition |
| `Deck2.seconds` | 83-91 | The second-seed enumeration: every unassigned vertex × every still-viable candidate of the stalled state — the state's own ambiguity set, equivariantly defined (nothing chosen, trap #7); empty iff the first propagation completed. | Definition |
| `Deck2.mem_seconds_iff` | 93-109 | Membership characterization of `seconds`: unassigned (`m p.1 = none`) and currently viable (`candPred`). | — |
| `Deck2.invFun` | 113-116 | Computable inverse-by-table (first preimage in enumeration order); the `permOf` gate makes the order irrelevant. | Definition |
| `Deck2.permOf` | 118-123 | The bijectivity gate: `some ⟨f, f⁻¹⟩` iff `f` is bijective, `none` otherwise — replaces F2b's backward propagation with one table inversion. | Definition |
| `Deck2.gate_of_bijective` | 125-145 | A bijective table passes the two-sided-inverse gate (`find?` finds the unique preimage). | — |
| `Deck2.bijective_of_gate` | 147-150 | The gate implies bijectivity — together with `gate_of_bijective`, gate ⟺ `Function.Bijective`, a labelling-independent predicate. | — |
| `Deck2.permOf_eq_some_of_eq` | 152-160 | Reconstruction through the gate: a table pointwise equal to a permutation gates to exactly that permutation. | — |
| `Deck2.bijective_conj_iff` | 162-171 | Bijectivity is invariant under conjugation by a permutation — the transport engine for the gate's failure mode. | — |
| `Deck2.permOf_conj` | 173-184 | The gate transports including its failure mode: `permOf (σ ∘ f ∘ σ⁻¹) = (permOf f).map (σ * · * σ⁻¹)`. | — |
| `Deck2.deck2Fun` | 188-191 | The two-seed forced table: continue the first propagation with the second seed added, identity-fill (junk is caught by the gate + verification). | Definition |
| `Deck2.deck2Cand` | 193-197 | The second-seed candidate: gate the completed table into a `Perm`; `Consume.verified` still re-checks `IsColAut` (the supply stays untrusted). | Definition |
| `Deck2.contFrom_sound` | 201-215 | The F2b invariant `m ⊆ ρ` survives any number of forcing rounds from ANY sound starting state — soundness is per-state, not per-seed-map. | — |
| `Deck2.setSeed_sound` | 217-227 | Adding a second seed that `ρ` satisfies preserves the invariant `m ⊆ ρ`. | — |
| `Deck2.deck2Cand_eq_of_isColAut` | 229-244 | ★★ RECONSTRUCTION: a colour-automorphism extending BOTH seeds + completed continuation ⟹ the candidate IS it. The second-seed hypothesis is the ambiguity being resolved: `ρ v₁ = v₂` picks which commuting extension the continuation forces. | — |
| `Deck2.contFrom_conj` | 248-263 | Forcing-round iterates commute with relabelling from any transported state (`mconj`). | — |
| `Deck2.setSeed_conj` | 265-274 | The second-seed insertion commutes with `mconj` transport. | — |
| `Deck2.mem_seconds_conj` | 276-297 | The ambiguity set transports: membership in `seconds` on the relabelled graph is the σ-image of membership on the original — the equivariance of the second-seed enumeration. | — |
| `Deck2.deck2Fun_conj` | 299-308 | The two-seed forced table conjugates pointwise under relabelling. | — |
| `Deck2.deck2Cand_conj` | 310-319 | The candidate transports up to conjugation, including its failure mode (via `permOf_conj`). | — |
| `Deck2.secondsV` | 323-329 | Vector-state twin of `seconds` (reads the forced base state, trap #1). | Definition |
| `Deck2.secondsV_ofFn` | 331-339 | Bridge: `secondsV` on `Vector.ofFn m` is `seconds` on `m`. | — |
| `Deck2.deck2Batch` | 341-348 | The per-first-pair evaluation batch: ONE base propagation (shared, trap #2), its ambiguity set, each continuation from the shared Vector state, gated by `permOf`. | Definition |
| `Deck2.deck2Batch_eq` | 350-367 | The batch computes exactly the spec candidates over the spec enumeration (`propagateVec_eq` + `secondsV_ofFn` + `iterate_roundVecD`). | — |
| `Deck2.deck2Supply` | 371-377 | ★ THE SECOND-SEED PROPAGATION SUPPLY (F2c): branch-cell first seeds, stalled-state ambiguity entries as second seeds, gate + verify. Breaks the commuting-gauge stall (mirror composites through twisted matchings) that defeats F2b. Cost flat `|B|²·(1+n²)·n⁵`. | Definition |
| `Deck2.mem_gens_deck2Supply_iff` | 379-393 | Membership characterization of the emitted generators: a first pair from the branch cell, a second pair from the stalled state's ambiguity set, and a gated candidate. | — |
| `Deck2.gensEquivariant_deck2Supply` | 397-427 | ★★ ①c: the supply is equivariant — both enumerations transport (branch cell; `mem_seconds_conj`) and the candidate conjugates including failure (`deck2Cand_conj`). No representative is ever chosen. | — |
| `Deck2.supplyEquivariant_deck2Supply` | 429-430 | The verified-list form of equivariance (what the resolver reads). | — |
| `Deck2.wordReach_deck2Supply` | 434-448 | Graded firing, per pair: a verified second-seed candidate carrying `u₁` to `u₂` puts the pair into the verified `WordReach`. | — |
| `Deck2.cellIsOrbit_deck2Supply` | 450-459 | ★★★ THE ORACLE FIRES: every branch-cell pair connected by a verified second-seed candidate ⟹ the cell is certified one orbit — past the commuting-gauge stall, with no refinement. | — |
| `Deck2.deck2Supply_guarded_canonizer` | 463-469 | ★★★ The guarded (blind) mixed canonizer over the second-seed supply — ①a/①b/①c + unconditional polynomiality, no carried hypotheses. | — |
| `Deck2.deck2Supply_selNode_canonizer` | 471-477 | ★★★ The fused (resolver-aware) canonizer over the second-seed supply. | — |
| `Deck2.holKey_foldDeck2_selNode_canonizer` | 479-490 | ★★★ THE F2c CANONIZER OF RECORD for the fold family: force = holonomy key, consume = `foldSupply ++ deckSupply ++ deck2Supply` — the object the `U3 ⊔ T3` end-to-end acceptance runs. | — |
| `Deck2.holKey_foldDeck2Fast_selNode_canonizer` | 492-501 | The all-fast form of the F2c record (`foldSupplyFast` component) — identical by `foldSupplyFast_eq`; the form the measurements run. | — |
## ChainDescent/KernelSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.isAdj` | 77-79 | Symmetric adjacency presence test (weights compared elsewhere; rails need presence only). | Definition |
| `Kernel.twinP` | 81-84 | Twin candidacy: same colour, distinct, non-adjacent, DISJOINT neighbourhoods — the rail-pair discriminator (correctly rejects the fold family's mirror pairs, which share neighbours). | Definition |
| `Kernel.twin` | 86-88 | The unique twin via `uniqueFilter` — ambiguity means no rail, never a choice (trap #7). | Definition |
| `Kernel.rails` | 90-96 | The rail pairs (gauge wires): mutually-unique twins, listed once at the lower index — an INTERNAL labelling the ① story never depends on (see the all-or-nothing gate). | Definition |
| `Kernel.onRail` | 98-100 | Is a vertex a rail endpoint? | Definition |
| `Kernel.touches` | 104-106 | Does a vertex see either endpoint of a rail? | Definition |
| `Kernel.patOf` | 108-119 | The flip pattern a shape-matched same-cell partner realizes: bit = touched and crossed. `none` when touch shapes differ. | Definition |
| `Kernel.pats` | 121-124 | All realizable local flip patterns at a vertex (the vertex itself contributes zero — a CFI gadget's patterns are exactly its even subsets). | Definition |
| `Kernel.xorRow` | 128 | F₂ row addition. | Definition |
| `Kernel.reduceRow` | 130-131 | Reduce a row by the current pivot list. | Definition |
| `Kernel.echelon` | 133-140 | Reduced row echelon form as a pivot list — UNTRUSTED (correctness = tranche 2's `span(kernelBasis) = L`). | Definition |
| `Kernel.nullBasis` | 142-151 | A basis of the null space of the row space: one word per free column, pivots back-substituted. Untrusted; used twice (local perps, the global kernel). | Definition |
| `Kernel.restrictCols` | 153-154 | Restrict a row to a column subset (patterns → wire support). | Definition |
| `Kernel.embedCols` | 156-160 | Re-embed a restricted row into the full width with zeros elsewhere. | Definition |
| `Kernel.wiresOf` | 164-169 | The wire support of a vertex: rail indices it touches. | Definition |
| `Kernel.localRows` | 171-177 | A vertex's constraint rows = the perp of the span of its patterns, computed inside its wire support and re-embedded — the extracted parity checks (mp7: exactly the Fano line checks). | Definition |
| `Kernel.kernelBasis` | 179-182 | A Gaussian basis of the gauge space L = the null space of every vertex's constraints (mp7: the [7,3,4] simplex code, dim 3, weights 4). | Definition |
| `Kernel.railImg` | 186-191 | The rail image of a vertex under a flip word (`none` off the rails). | Definition |
| `Kernel.flipFunK` | 193-211 | The candidate table for a word: rails flip; a non-rail vertex touching a flipped rail moves to its unique same-colour partner matching the flipped adjacency (full weights, both directions); untouched vertices stay. Junk dies at the gate/verify. | Definition |
| `Kernel.kernelGens` | 215-221 | ★ The ALL-OR-NOTHING gate: emit the whole basis (as gated, verified flips) or nothing. "Whole basis verifies" ⟺ "every word of L verifies" (products of automorphisms) — a CANONICAL predicate, so the emitted GROUP is a canonical function of (adj, χ) despite the pivot-order-dependent basis: the ①c design lock; the ① theorems ride the SameOrbits reduction (tranche 2). | Definition |
| `Kernel.kernelSupply` | 223-227 | ★ THE KERNEL SUPPLY (C3a): recognition and solving untrusted, every generator re-verified; flat n⁵ bill. Measured (mp7): the root gadget cell 28 → 7 = the whole gauge in one supply call — what no propagation shape can reach at any seed count. | Definition |
## ChainDescent/KernelFlip.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.uniqueFilter_eq_some_iff` | 54-77 | `uniqueFilter` returns `some w` exactly when `w` satisfies the predicate and is the only such element — no choice is ever made. | — |
| `Kernel.uniqueFilter_transport` | 79-83 | `uniqueFilter` transports along a permutation of the domain. | — |
| `Kernel.mem_rails_iff` | 87-109 | Rail membership: mutual-unique twins listed at the lower index. | — |
| `Kernel.twinP_of_twin_eq_some` | 111-114 | A recorded twin satisfies the twin predicate. | — |
| `Kernel.rails_endpoint_eq` | 116-138 | ★ Rails are vertex-DISJOINT: two rails sharing an endpoint are equal (twin uniqueness). | — |
| `Kernel.rails_ne` | 140-146 | A rail's two endpoints are distinct. | — |
| `Kernel.onRail_iff` | 148-159 | `onRail` membership unfolded to an endpoint witness. | — |
| `Kernel.onRail_rails_iff` | 161-185 | Being on a rail is exactly having a mutual-unique twin. | — |
| `Kernel.railImg_eq_none_iff` | 189-225 | `railImg` fails exactly off the rails. | — |
| `Kernel.findSome?_rail_lookup` | 227-271 | The generic disjoint-scan value lemma: at an endpoint of a listed rail the scan returns that rail's flip value. | — |
| `Kernel.permOf_apply` | 275-281 | A gated permutation acts as the table it was gated from. | — |
| `Kernel.isAdj_comm` | 283-285 | Rail-detection adjacency is symmetric. | — |
| `Kernel.isAdj_aut` | 287-291 | Adjacency is automorphism-stable. | — |
| `Kernel.isAdj_eq_false_iff` | 293-297 | Non-adjacency unfolded to both matrix entries being zero. | — |
| `Kernel.all_finRange_perm` | 299-307 | `all` over `finRange` is invariant under precomposition with a permutation. | — |
| `Kernel.twinP_aut` | 309-326 | The twin predicate is automorphism-stable. | — |
| `Kernel.twin_aut` | 328-332 | The twin map commutes with an automorphism. | — |
| `Kernel.onRail_aut` | 334-369 | Rails are structural: an automorphism maps rail endpoints to rail endpoints. | — |
| `Kernel.rails_map_fst_nodup` | 373-395 | Rail first-components are distinct. | — |
| `Kernel.rails_nodup` | 397-398 | The rail list has no duplicates. | — |
| `Kernel.zip_entry_unique` | 400-419 | Two zip entries carrying the same rail carry the same bit. | — |
| `Kernel.zip_huniq` | 421-436 | Any zip entry sharing an endpoint with `(p, b)` *is* `(p, b)` — the uniqueness input to the scan lemmas. | — |
| `Kernel.condFun` | 440-445 | The per-rail flipped-adjacency condition inside `flipFunK` (`x` is the candidate). | Definition |
| `Kernel.satP` | 447-450 | The satisfier predicate inside `flipFunK`: same colour, off the rails, and matching flipped adjacency on every rail. | Definition |
| `Kernel.flipGuard` | 452-454 | The flip guard: the vertex touches a rail the word flips. | Definition |
| `Kernel.flipFunK_eq` | 456-466 | `flipFunK` factored through `railImg` / `flipGuard` / `satP`. | — |
| `Kernel.emitted_rail_action` | 468-492 | The emitted permutation acts on every zipped rail exactly as the word's flip. | — |
| `Kernel.touched_moves` | 494-539 | ★ Under a VERIFYING flip a vertex touching a flipped rail cannot stay fixed (twin neighbourhood-disjointness) — this rules the identity-default out of every verified table and closes the `uniqueFilter`-ambiguity hole for compound words. | — |
| `Kernel.getElem_xorRow'` | 543-546 | Indexed view of `xorRow`. | — |
| `Kernel.mem_zip_iff_getElem'` | 548-560 | Indexed view of zip membership. | — |
| `Kernel.all_zip_iff` | 562-574 | `all` over the labelled word, at the index level. | — |
| `Kernel.any_zip_iff` | 576-588 | `any` over the labelled word, at the index level. | — |
| `Kernel.condFun_mk` | 590-596 | `condFun` on an explicit pair/bit. | — |
| `Kernel.condFun_untouched` | 598-616 | Untouched-rail conditions are bit-independent. | — |
| `Kernel.flip_pt_comp` | 618-623 | The rail endpoint action composes under XOR of the two bits. | — |
| `Kernel.condFun_conj_flip` | 625-634 | The per-rail condition transports through a verified flip's endpoint action. | — |
| `Kernel.flipGuard_congr` | 638-659 | Guards agree for words agreeing on the rails a vertex touches. | — |
| `Kernel.satP_congr_touch` | 661-682 | Satisfier predicates agree for words agreeing on the rails a vertex touches. | — |
| `Kernel.satP_conj_flip` | 684-716 | ★ THE SATISFIER BIJECTION: a verified `w`-flip maps the satisfier set of `(w', v)` onto that of `(w ⊕ w', v)`, so `uniqueFilter` transports. | — |
| `Kernel.satP_self_of_guard_false` | 718-752 | With the guard off a vertex is its own satisfier — the untouched case. | — |
| `Kernel.flipFunK_xor` | 756-868 | ★★★ THE PRODUCT LEMMA: if the flips of `w` and `w'` both emit and verify then `flip (w ⊕ w') = flip w ∘ flip w'`. This is the theorem behind the all-or-nothing gate — verifying the basis propagates to every word of the span, so the emitted GROUP is canonical. | — |

## ChainDescent/KernelGauss.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.xorList` | 27-28 | XOR-fold of a Bool list. | Definition |
| `Kernel.xorList_nil` | 30 | XOR of the empty list is `false`. | `@[simp]` |
| `Kernel.xorList_cons` | 32-33 | XOR unfolds at the head. | `@[simp]` |
| `Kernel.xorList_eq_count` | 35-50 | XOR over a Bool list is the parity of its `true` count — the entry point to the counting view. | — |
| `Kernel.getD_in` | 52-54 | `getD` at an in-range index is `getElem` (the `List.getD` bridge used throughout the F₂ layer). | — |
| `Kernel.dotB` | 56-57 | The F₂ dot product: parity of the common support. | Definition |
| `Kernel.dotOn` | 59-61 | The F₂ dot product over an explicit index list — the form all support-splitting arguments use. | Definition |
| `Kernel.xorList_map_eq_countP` | 63-70 | XOR over a mapped list is a `countP` parity. | — |
| `Kernel.dotOn_eq_countP` | 72-75 | ★ The workhorse view: the index-list dot product is a `countP` parity, so all support-splitting becomes counting. | — |
| `Kernel.zipWith_and_eq_range_map` | 77-87 | A length-`m` pointwise-AND list is the range-map of its pointwise values. | — |
| `Kernel.dotB_eq_dotOn` | 89-92 | `dotB` over length-`m` operands is `dotOn` over `range m`. | — |
| `Kernel.dotB_comm` | 94-98 | The F₂ dot product is symmetric. | — |
| `Kernel.xorList_zipWith_bne` | 102-115 | XOR of a pointwise XOR is the XOR of the XORs — linearity at the list level. | — |
| `Kernel.dotB_xorRow_right` | 120-129 | `dotB` is additive in its right argument. | — |
| `Kernel.dotB_xorRow_left` | 131-134 | `dotB` is additive in its left argument. | — |
| `Kernel.zeroW` | 136-137 | The zero word of length `m`. | Definition |
| `Kernel.length_zeroW` | 139 | The zero word has length `m`. | `@[simp]` |
| `Kernel.getElem_zeroW` | 141-142 | Every bit of the zero word is `false`. | `@[simp]` |
| `Kernel.dotB_zeroW_right` | 144-149 | Everything is orthogonal to the zero word. | — |
| `Kernel.length_xorRow` | 153-154 | `xorRow` preserves length (min of the two). | — |
| `Kernel.xorRow_zeroW_left` | 156-159 | Zero is a left identity for `xorRow`. | — |
| `Kernel.xorRow_zeroW_right` | 161-164 | Zero is a right identity for `xorRow`. | — |
| `Kernel.xorRow_self_cancel` | 166-172 | `xorRow` is an involution: a word XOR itself is zero (F₂ characteristic 2). | — |
| `Kernel.xorRow_assoc` | 174-180 | `xorRow` is associative. | — |
| `Kernel.getD_xorRow` | 182-186 | The `i`-th bit of an `xorRow` is the XOR of the `i`-th bits. | — |
| `Kernel.Spans` | 190-193 | F₂ span as an inductive XOR-combination relation — the reduction's notion of "generated by the basis". | Inductive |
| `Kernel.Spans.length` | 195-199 | A spanned word has the ambient length `m`. | — |
| `Kernel.Spans.mem` | 201-204 | Every basis element is spanned by the basis. | — |
| `Kernel.Spans.xor_closed` | 206-214 | The span is closed under `xorRow` — it is an F₂ subspace. | — |
| `Kernel.Spans.trans_basis` | 216-222 | Spanning is transitive through a basis whose members are themselves spanned. | — |
| `Kernel.dotB_eq_false_of_spans` | 224-232 | Orthogonality extends over a span — `dotB`-linearity folded along the derivation. | — |
| `Kernel.parity_add` | 236-246 | Parity of a sum is the XOR of the parities. | — |
| `Kernel.countP_eq_zero_of_support` | 248-252 | A predicate false on every member counts zero. | — |
| `Kernel.countP_parity_single` | 254-267 | Parity bookkeeping over a `Nodup` index list when exactly one index is distinguished. | — |
| `Kernel.countP_parity_pair` | 269-283 | Parity bookkeeping over a `Nodup` index list when exactly two indices are distinguished — the pivot/free-column split. | — |
| `Kernel.xorRow_comm` | 287-292 | `xorRow` is commutative. | — |
| `Kernel.xorRow_cancel_right` | 294-297 | Right cancellation for `xorRow`. | — |
| `Kernel.combo` | 299-300 | The XOR-combination of a list of words. | Definition |
| `Kernel.combo_nil` | 302 | The empty combination is zero. | `@[simp]` |
| `Kernel.combo_cons` | 304-305 | `combo` unfolds as an `xorRow` at the head. | — |
| `Kernel.combo_length` | 307-314 | An XOR-combination of length-`m` words has length `m`. | — |
| `Kernel.spans_combo` | 316-323 | Any XOR-combination of basis words is spanned. | — |
| `Kernel.getD_combo` | 325-337 | The `i`-th bit of a combination is the XOR of the `i`-th bits. | — |
| `Kernel.Spans.mono` | 339-344 | Spanning is monotone in the generating list. | — |
| `Kernel.PivInv` | 348-358 | The reduced-row-echelon invariant carried through the elimination fold: pivot rows unit at their own column and zero at every other pivot column, pivot columns `Nodup`, and BOTH directions of same-row-space. | Structure |
| `Kernel.pivInv_nil` | 360-361 | The echelon invariant holds vacuously at the empty pivot list. | — |
| `Kernel.reduceRow_cons` | 363-364 | `reduceRow` unfolds one pivot step. | — |
| `Kernel.reduceRow_length` | 366-380 | `reduceRow` preserves row length. | — |
| `Kernel.reduceRow_spec` | 382-414 | The reduced row differs from the input by a combination of pivot rows (`∃ q, Spans … ∧ reduceRow P r = xorRow q r`) — the same-row-space direction. | — |
| `Kernel.reduceRow_getD_const` | 416-435 | `reduceRow` leaves columns untouched by any pivot unchanged. | — |
| `Kernel.reduceRow_pivot_zero` | 437-481 | After reduction the row is zero at every pivot column — the defining property of reduced form. | — |
| `Kernel.echStep` | 483-490 | One elimination step: reduce the incoming row against the pivots, then install it as a new pivot and back-substitute. | Definition |
| `Kernel.echelon_eq_foldl` | 492 | `echelon` is the left fold of `echStep` — the form the invariant is proved against. | — |
| `Kernel.pivInv_step` | 494-688 | ★ The heart of part I: one fold step preserves the full echelon invariant (unit / cross-zeros / `Nodup` columns / both directions of same-row-space). | — |
| `Kernel.pivInv_foldl` | 690-708 | The invariant propagates through the whole fold by induction on the row list. | — |
| `Kernel.pivInv_echelon` | 710-716 | ★ `echelon rows` satisfies `PivInv` — reduced row echelon form, certified. | — |
| `Kernel.nbWord` | 720-725 | The null-space basis word emitted for a given free column. | Definition |
| `Kernel.freeCols` | 727-729 | The non-pivot (free) columns — one emitted basis word each. | Definition |
| `Kernel.nullBasis_eq` | 731-732 | `nullBasis` is the free columns mapped through `nbWord` — the form the soundness/completeness proofs read. | — |
| `Kernel.length_nbWord` | 734-735 | An emitted basis word has the ambient length. | `@[simp]` |
| `Kernel.getD_nbWord` | 737-744 | The bits of an emitted basis word: `1` at its own free column, the pivot row's entry at a pivot column, `0` elsewhere. | — |
| `Kernel.mem_freeCols_iff` | 746-748 | Free-column membership: in range and not a pivot column. | — |
| `Kernel.freeCols_nodup` | 750-751 | The free columns are distinct. | — |
| `Kernel.find?_col_eq` | 753-764 | Pivot lookup by column returns a pivot at that column. | — |
| `Kernel.find?_col_none` | 766-772 | Pivot lookup fails exactly at non-pivot columns. | — |
| `Kernel.getD_nbWord_self` | 774-777 | A basis word is `1` at its own free column. | — |
| `Kernel.getD_nbWord_pivot` | 779-783 | A basis word at a pivot column equals the pivot row's free-column entry. | — |
| `Kernel.getD_nbWord_free` | 785-788 | A basis word is `0` at every other free column. | — |
| `Kernel.dotB_pivot_nbWord` | 792-828 | Every pivot row is orthogonal to every emitted basis word — the per-row case of soundness. | — |
| `Kernel.dotB_nullBasis` | 830-846 | ★★ SOUNDNESS: every emitted basis word is orthogonal to every input row. | — |
| `Kernel.length_mem_nullBasis` | 848-853 | Emitted basis words have the ambient length `m`. | — |
| `Kernel.spans_nullBasis` | 860-981 | ★★★ COMPLETENESS: every word orthogonal to all input rows is an XOR-combination of the emitted basis. With `dotB_nullBasis` this is `span (kernelBasis) = L`. | — |

## ChainDescent/KernelRef.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.allWords` | 44-47 | All Bool words of length `m` — a proof-side enumeration (`2^m`), never executed by the canonizer. | Definition |
| `Kernel.mem_allWords_iff` | 49-64 | The proof-side enumeration `allWords m` is exactly the words of length `m`. | — |
| `Kernel.sysRows` | 66-69 | The global constraint system the kernel basis eliminates (every vertex's local rows). | Definition |
| `Kernel.kernelBasis_eq` | 71-72 | `kernelBasis` is `nullBasis` of the global system rows (definitional). | — |
| `Kernel.length_embedCols` | 74-75 | A re-embedded word has the ambient length. | `@[simp]` |
| `Kernel.mem_sysRows_length` | 77-88 | System rows have rail-list length. | — |
| `Kernel.inL` | 92-95 | Decidable membership in the gauge space `L`: null against every system row. | Definition |
| `Kernel.kernelWords` | 97-99 | Every word of `L` — the canonical SET the reference supply flips. | Definition |
| `Kernel.kernelRefGens` | 101-107 | The set-level reference generators: flips of every `L`-word, under the same all-or-nothing gate. | Definition |
| `Kernel.kernelRefSupply` | 109-111 | **The reference supply** — proof-side only (exponential enumeration, never billed because it never enters the record object); it exists to carry equivariance for the executable kernel supply. | Definition |
| `Kernel.gens_kernelSupply` | 113-114 | The kernel supply's generators are `kernelGens` (definitional). | — |
| `Kernel.gens_kernelRefSupply` | 116-117 | The reference supply's generators are `kernelRefGens` (definitional). | — |
| `Kernel.gate_true_iff` | 151-182 | The all-or-nothing gate over a word list is exactly "every word emits and verifies". | — |
| `Kernel.KernelGate` | 184-187 | The kernel gate, in `Prop` form: every basis word emits and verifies. | Definition |
| `Kernel.RefGate` | 189-192 | The reference gate: every `L`-word emits and verifies. Equivalent to `KernelGate`, and canonical where it is not. | Definition |
| `Kernel.kernelGens_pos` | 194-198 | With the gate passing, `kernelGens` is the whole emitted basis. | — |
| `Kernel.kernelGens_neg` | 200-203 | With the gate failing, `kernelGens` is empty — all or nothing. | — |
| `Kernel.refGens_pos` | 205-209 | With the gate passing, the reference emits every `L`-word's flip. | — |
| `Kernel.refGens_neg` | 211-214 | With the gate failing, the reference emits nothing. | — |
| `Kernel.flipFunK_zeroW` | 218-252 | The zero word's flip is the identity table. | — |
| `Kernel.flip_emits_of_spans` | 254-281 | ★★ Span induction: if every basis flip emits and verifies then so does every spanned word's flip, and each such flip `Reaches` the kernel-generated group (the P3b product license). | — |
| `Kernel.basis_mem_kernelWords` | 283-292 | Basis words lie in `L` — `nullBasis` soundness read into the reference's word list. | — |
| `Kernel.spans_of_mem_kernelWords` | 294-307 | Every `L`-word is spanned by the basis — `nullBasis` completeness read into the reference's word list. | — |
| `Kernel.basis_emits_of_kernelGate` | 309-320 | The kernel gate unpacked: every basis word emits and verifies. | — |
| `Kernel.refGate_of_kernelGate` | 322-329 | ★ The canonicity content: "the whole basis verifies" ⟹ "every word of `L` verifies" — so the gate is a canonical predicate, not a pivot-order artefact. | — |
| `Kernel.kernelGate_of_refGate` | 331-334 | The converse gate implication (basis ⊆ `L`). | — |
| `Kernel.sameOrbits_kernelRef` | 338-370 | ★★★ The set-level reference and the executable kernel supply prove the SAME ORBITS: gates pass ⟹ mutual `Reaches`; gates fail ⟹ both verified lists empty. This is what ① rides on, in place of an (impossible) pointwise equivariance of the Gaussian basis. | — |
| `Kernel.verified_appendSupply_mem` | 374-388 | Membership in a concatenated supply's verified list. | — |
| `Kernel.sameOrbits_appendSupply` | 390-413 | ★★ Orbit-equality is a CONGRUENCE for `appendSupply` — a `SameOrbits`-licensed swap stays licensed inside a composite record object. | — |

## ChainDescent/KernelTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.IsoTo` | 47-51 | `σ` carries `(adj, χ)` to `(adj', χ')` — the isomorphism the whole transport stack is stated against (the `IsColAut` lemmas are its `adj' = adj` case). | Structure |
| `Kernel.isoTo_relabel` | 53-57 | `σ` is an isomorphism from `(adj, χ)` to its relabelling — the instance the equivariance obligation is stated at. | — |
| `Kernel.IsoTo.symm` | 59-70 | The inverse isomorphism. | — |
| `Kernel.isAdj_iso` | 72-76 | Adjacency transports along an isomorphism. | — |
| `Kernel.twinP_iso` | 78-95 | The twin predicate transports along an isomorphism. | — |
| `Kernel.twin_iso` | 97-101 | The twin map transports along an isomorphism. | — |
| `Kernel.sPair` | 103-104 | The pair `{a, b}` listed at its lower index — the rail list's internal endpoint-order convention. | Definition |
| `Kernel.sPair_cases` | 106-109 | `sPair` is one of the two orderings of its arguments. | — |
| `Kernel.sPair_lt` | 111-116 | `sPair` puts the lower index first. | — |
| `Kernel.sPair_comm` | 118-123 | `sPair` is symmetric in distinct arguments. | — |
| `Kernel.sPair_self` | 125-126 | `sPair` fixes an already-ordered pair. | — |
| `Kernel.railMap` | 128-129 | The rail correspondence map: transport the endpoints, then re-normalize the endpoint order. | Definition |
| `Kernel.mem_rails_sPair` | 131-137 | Mutual-unique twins give a rail, at whichever endpoint order the rail list uses. | — |
| `Kernel.mem_rails_conj` | 139-191 | ★ RAILS TRANSPORT, MEMBERWISE: the rail list ORDER is an internal labelling; what is canonical is the rail SET, and `σ` carries it onto the relabelled graph's rail set (up to endpoint order — hence `railMap`). | — |
| `Kernel.railMap_injOn` | 193-211 | `railMap σ` is injective on rails. | — |
| `Kernel.rails_perm_conj` | 213-230 | ★ The rail lists are `List.Perm` along `railMap σ` — not an equality (the order is a labelling), and a `Perm` is exactly what every count argument downstream needs. | — |
| `Kernel.rails_length_conj` | 232-236 | The two rail lists have equal length. | — |
| `Kernel.onRail_conj` | 238-269 | Being on a rail transports. | — |
| `Kernel.touches_swap` | 271-275 | `touches` is endpoint-order invariant. | — |
| `Kernel.touches_conj` | 277-287 | `touches` transports, through the `sPair` normalization. | — |
| `Kernel.lookupBit` | 297-299 | The bit a word assigns to the rail with a given endpoint (`false` off the rails). | Definition |
| `Kernel.transportWordR` | 301-304 | Transport a word between rail lists along `σ`, by endpoint lookup — `σ` permutes rail POSITIONS arbitrarily, so bits are re-read, not re-indexed. | Definition |
| `Kernel.findSome?_bit_lookup` | 306-329 | The scan-value lemma for the bit lookup (the `railImg` analogue is `findSome?_rail_lookup`). | — |
| `Kernel.zip_getElem_mem` | 331-334 | The `i`-th labelled bit is in the zip. | — |
| `Kernel.exists_zip_bit` | 336-341 | Every rail carries a bit when the word has rail-list length. | — |
| `Kernel.lookupBit_eq` | 343-349 | The endpoint lookup returns the rail's paired bit. | — |
| `Kernel.lookupBit_off` | 351-364 | The endpoint lookup is `false` off the rails. | — |
| `Kernel.map_lookupBit_self` | 366-373 | Reading every rail's bit back reproduces the word. | — |
| `Kernel.transport_perm` | 375-398 | Transport permutes the bits — it is a reindexing along the rail bijection. | — |
| `Kernel.mem_zip_transport` | 400-440 | ★★ THE CENTRAL LEMMA: the labelled word `rails.zip w` transports as a SET of labelled bits. Every `any`/`all` in the guard and satisfier conditions is a statement at exactly this level, so all of them transport. | — |
| `Kernel.transportWordR_length` | 442-444 | A transported word has target-rail-list length. | — |
| `Kernel.lookupBit_and` | 446-462 | The lookup is multiplicative in the word — the step that lets `dotB` transport. | — |
| `Kernel.dotB_transport` | 464-483 | ★ `dotB` is transport-invariant: both arguments are re-read along the same rail bijection, so the parity of the coincidence count is unchanged. | — |
| `Kernel.railImg_endpoint` | 491-504 | `railImg` at each endpoint of a listed rail. | — |
| `Kernel.railImg_conj` | 506-533 | The rail action transports (including its `none` case, off the rails). | — |
| `Kernel.condFun_swap` | 535-542 | `condFun` is endpoint-order invariant (it constrains both endpoints symmetrically). | — |
| `Kernel.condFun_conj` | 544-559 | The per-rail flipped-adjacency condition transports. | — |
| `Kernel.flipGuard_conj` | 561-579 | The flip guard transports (memberwise over the labelled word). | — |
| `Kernel.satP_conj` | 581-601 | The satisfier predicate transports (memberwise over the labelled word). | — |
| `Kernel.flipFunK_conj` | 603-621 | ★ EMISSION TRANSPORTS: the candidate table on the relabelled graph, at the transported word, is the `σ`-conjugate of the table here. | — |
| `Kernel.getD_gen` | 630-632 | `getD` at an in-range index is `getElem` (general element type). | — |
| `Kernel.getD_range_map` | 634-637 | Indexing a range-map at an in-range index applies the function. | — |
| `Kernel.getD_embedCols` | 639-643 | The bits of an embedded word, by column lookup. | — |
| `Kernel.findIdx?_nodup_self` | 645-651 | In a `Nodup` list, searching for the `k`-th element finds index `k`. | — |
| `Kernel.getD_restrictCols` | 653-657 | The `k`-th bit of a restricted word is the ambient bit at the `k`-th column. | — |
| `Kernel.embedCols_support` | 659-668 | An embedded word is supported inside its column list. | — |
| `Kernel.embed_restrict` | 670-690 | Restricting then re-embedding is the identity on words supported in the column list. | — |
| `Kernel.map_getD_range_self` | 692-697 | A list is the range-map of its own indexing. | — |
| `Kernel.countP_range_eq_countP` | 699-713 | Counting over the full range equals counting over a `Nodup` sublist that contains the whole support. | — |
| `Kernel.dotB_embed` | 715-746 | ★ THE EMBED/RESTRICT ADJUNCTION: `dotB (embedCols m cols y) u = dotB y (restrictCols cols u)` — the counting lemma that lets the per-vertex local system and the global one talk to each other. | — |
| `Kernel.mem_wiresOf_iff` | 756-767 | Wire-support membership: an in-range rail index the vertex touches. | — |
| `Kernel.wiresOf_nodup` | 769-770 | A vertex's wire indices are distinct. | — |
| `Kernel.wiresOf_lt` | 772-773 | Wire indices are in range. | — |
| `Kernel.length_mem_pats` | 775-781 | Realizable patterns have rail-list length. | — |
| `Kernel.mem_localRows` | 783-794 | A local constraint row is an embedded null-basis word at a non-rail vertex. | — |
| `Kernel.mem_localRows_mpr` | 796-803 | Embedded null-basis words at a non-rail vertex are local constraint rows. | — |
| `Kernel.mem_sysRows_iff` | 805-811 | The global system is the union of the per-vertex local systems. | — |
| `Kernel.SuppAt` | 813-815 | The word is supported in a vertex's wire set (only rails it touches carry a bit). | Definition |
| `Kernel.suppAt_iff_index` | 817-834 | Wire-support, membership form ⟺ index form. | — |
| `Kernel.Lc` | 836-840 | **`L`, basis-free**: `w` is killed by every wire-supported functional that kills the local patterns. Unlike `inL` this names no basis, so it transports memberwise — the form that makes the reference supply equivariant. | Definition |
| `Kernel.inL_iff_Lc` | 842-902 | ★ THE BRIDGE: the executable, pivot-DEPENDENT `inL` agrees with the basis-free `Lc` (killed by every wire-supported functional that kills the local patterns). It rides on part I being both sound and complete, over the embed/restrict adjunction — and it is what makes `L` transportable at all. | — |
| `Kernel.shapeP` | 911-915 | The per-rail shape condition inside `patOf`. | Definition |
| `Kernel.patBit` | 917-919 | The pattern bit `patOf` emits per rail. | Definition |
| `Kernel.patOf_eq` | 921-925 | `patOf` factored into its shape condition and its emitted bits. | — |
| `Kernel.shapeP_swap` | 927-931 | The per-rail shape condition is endpoint-order invariant. | — |
| `Kernel.patBit_swap_of_shape` | 933-938 | ★ The emitted pattern bit reads the rail's FIRST endpoint, so it is endpoint-order invariant only UNDER `patOf`'s own shape condition (single-sided touch on both sides, matching touch support) — the fact `patOf_conj` turns on. | — |
| `Kernel.shapeP_base` | 940-945 | The shape condition transports at the un-normalized pair. | — |
| `Kernel.patBit_base` | 947-952 | The pattern bit transports at the un-normalized pair. | — |
| `Kernel.shapeP_conj` | 954-960 | The shape condition transports, through the `sPair` normalization. | — |
| `Kernel.patBit_conj` | 962-971 | The pattern bit transports, through the `sPair` normalization (using the shape condition). | — |
| `Kernel.patOf_conj` | 973-1019 | ★ Local patterns transport: a pattern's image is exactly `transportWordR` of it. | — |
| `Kernel.mem_pats_conj` | 1021-1028 | The realizable pattern SET transports memberwise. | — |
| `Kernel.transportWordR_roundtrip` | 1030-1055 | Transport is invertible: `σ.symm` undoes it. | — |
| `Kernel.Lc_transport` | 1057-1090 | ★ The basis-free gauge space transports — the statement `inL` could not make, because `localRows` is pivot-dependent. | — |
| `Kernel.inL_conj` | 1098-1110 | `L`-membership transports (via the bridge and `Lc_transport`). | — |
| `Kernel.mem_kernelWords_conj` | 1112-1136 | The reference's word list transports: `kernelWords` on the relabelled graph is the transport of `kernelWords` here. | — |
| `Kernel.length_mem_kernelWords` | 1138-1140 | `L`-words have rail-list length. | — |
| `Kernel.permOf_flipFunK_conj` | 1142-1155 | Emission plus gate, conjugated — `Deck2.permOf_conj` moves the gate INCLUDING its failure mode. | — |
| `Kernel.refGate_conj` | 1157-1178 | The all-or-nothing gate is labelling-independent. | — |
| `Kernel.gensEquivariant_kernelRefSupply` | 1180-1206 | ★★★ The set-level reference supply IS equivariant: `L` transports (§4), emission transports (§3), and the gate is a statement about `L`'s flips — so the generator SET on the relabelled graph is exactly the set of `σ`-conjugates. | — |
| `Kernel.supplyEquivariant_kernelRefSupply` | 1208-1210 | The verified-list form of the reference's equivariance. | — |
| `Kernel.kernelSupply_guarded_canonizer` | 1220-1227 | ★★★ ① for the guarded (blind) mixed object at the kernel supply — via `SameOrbits`, with ZERO equivariance obligation on the executable object. | — |
| `Kernel.kernelSupply_selNode_canonizer` | 1229-1236 | ★★★ ① for the FUSED (resolver-aware) object at the kernel supply. | — |
| `Kernel.recordRefSupply` | 1238-1242 | The kernel-extended record's equivariant REFERENCE composite (proof-side only). | `abbrev` |
| `Kernel.recordSupply` | 1244-1248 | The kernel-extended record consume-side supply: `fold ++ deck ++ deck2 ++ kernel`. | `abbrev` |
| `Kernel.supplyEquivariant_recordRefSupply` | 1250-1255 | The reference composite is equivariant (each component is). | — |
| `Kernel.sameOrbits_recordSupply` | 1257-1259 | The reference composite and the record prove the same orbits — `sameOrbits_appendSupply` applied through the three concatenations. | — |
| `Kernel.holKey_foldDeck2Kernel_selNode_canonizer` | 1261-1271 | ★★★ THE C3a CANONIZER OF RECORD: force = the holonomy key, consume = `foldSupply ++ deckSupply ++ deck2Supply ++ kernelSupply`. The F₂ kernel supply is inside the record object, with ① discharged through the `SameOrbits` reduction rather than by a pointwise equivariance the Gaussian basis cannot have. | — |
| `Kernel.holKey_foldDeck2KernelFast_selNode_canonizer` | 1273-1283 | The all-fast form of the extended record — the form the measurements run, and the object `Publication.canonForm?` pins. | — |
| `Kernel.handledS_recordSupply` | 1285-1290 | ③ transfers too: the residue predicate is read off the same narrowing, so a `HandledS` certificate for the reference composite is one for the record. | — |
## ChainDescent/DeepenCrux.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.GateAt` | 72-79 | §1 The all-singletons gate outcome at a given anchor — exactly the condition `deepenGens` tests before emitting. | Definition |
| `Deepen.DeepenGateInvariant` | 83-88 | §2 **CRUX (i), OPEN.** The gate outcome is labelling-invariant. Given `DeepenTransport` (every other stage transports), this predicate is the ENTIRE residue of `deepenSupply`'s ①c. | Definition |
| `Deepen.DeepenForcedMatch` | 90-96 | §2 **CRUX (ii), OPEN.** When the gate passes, the emitted relation is the true `Aut`-orbit relation. The `→` direction is proved (`deepenGens_isColAut`); the `←` (completeness) direction is the open content. | Definition |
| `Deepen.deepenGens_isColAut` | 100-125 | §3 **Every emitted generator is a genuine colour-automorphism** — untrusted construction, verified emission. The proved `→` half of `DeepenForcedMatch`. | — |
| `Deepen.deepenGens_sound` | 127-133 | §3 The emitted orbit relation is **contained in the true one**: the supply can only under-report orbits, never over-merge (over-splitting costs a branch; over-merging would be unsound). | — |

## ChainDescent/DeepenSupply.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.classOf` | 123-125 | §1 The members of a vertex's 1-WL colour class — the footprint primitive the gates count. | Definition |
| `Deepen.coupled` | 127-131 | §1 **The coupled component**: the vertices whose PARENT cell split under the child colouring. `O(n³)` — compute once per level and thread it (trap #2). | Definition |
| `Deepen.allSingletonsK` | 133-135 | §1 The **forced-matching gate**: every sub-cell of the coupled component is a singleton, so the colour-match is a forced bijection rather than an arbitrary within-cell pick. | Definition |
| `Deepen.chooseIdK` | 137-142 | §1 The lowest child-colour id among the NON-singleton sub-cells — the iso-invariant choice of *which cell* to descend (choosing a cell is canonical; choosing a vertex in it is not). | Definition |
| `Deepen.step` | 146-148 | §2 One individualize + warm-refine step, materialised as `ColData` (trap #1: never store a `Colouring`). | Definition |
| `Deepen.deepen` | 150-176 | §2 **`DeepenAnchor`.** Descend the lowest-id non-singleton sub-cell until the footprint is all-singletons, recording the chosen cell ids; parent stays fixed at the node colouring. A single path, never a branch over representatives. | Definition |
| `Deepen.replay` | 178-188 | §2 **`ReplayDeepening`.** Follow the anchor's recorded cell-id sequence from another representative; `none` if it cannot be followed (⟹ no candidate, sound). | Definition |
| `Deepen.twistOf` | 192-203 | — | Definition |
| `Deepen.twistOf_isColAut` | 205-217 | — | — |
| `Deepen.imgFun` | 219-223 | — | Definition |
| `Deepen.vget_ofFn` | 225-227 | — | — |
| `Deepen.twistOf_eq_imgFun` | 229-238 | — | — |
| `Deepen.deepenGens` | 240-263 | §3 **The emitted generators**: for EVERY anchor of the branch cell, deepen → replay from each other representative → match footprint colours on the coupled component → `permOf` + `IsColAut` verify. ⚠ All anchors is REQUIRED, not an optimisation — a single anchor is measured to break ①c (the `G8` falsifier). | Definition |
| `Deepen.deepenSupply` | 265-267 | §3 **★ THE DEEPENING SUPPLY** (C3b tranche 1) — the BASE-symmetry constructor, reaching what propagation cannot (girth kills chaining) and what the gauge supply does not see. Cost billed flat at `n⁶`. Deliberately NOT yet in the record object: its ①c stack is tranche 2, still open. | Definition |

## ChainDescent/DeepenTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.transport_apply` | 56-60 | §1 The transported colouring agrees with the original after `σ` — the pointwise fact every other transport lemma in the deepening pipeline rests on. | — |
| `Deepen.transport_apply'` | 62-64 | §1 The same, read at an arbitrary point through `σ.symm`. | — |
| `Deepen.mem_classOf_iff` | 68-71 | §2 Membership in a 1-WL colour class is just colour equality — the unfolding consumers use. | — |
| `Deepen.classOf_nodup` | 73-74 | §2 A colour class is `Nodup` (it filters `finRange`) — the side condition every `List.Perm` argument here needs. | — |
| `Deepen.mem_classOf_transport` | 76-79 | §2 Colour-class membership transports: `u` lies in the transported class of `σ v` iff `σ.symm u` lies in the original. | — |
| `Deepen.classOf_perm_transport` | 81-90 | §2 A colour class transports **up to `List.Perm`**, not equality — `classOf` filters `finRange` in index order, which `σ` need not respect (the `rails_perm_conj` lesson). | — |
| `Deepen.classOf_length_transport` | 92-95 | §2 **Class SIZE is invariant** under relabelling — the quantity the all-singletons and non-singleton gates actually read. | — |
| `Deepen.mem_coupled_iff` | 99-103 | §3 Unfolding of the coupled component: `v` is coupled iff its parent cell carries more than one child colour. | — |
| `Deepen.parentCell_perm_transport` | 105-117 | §3 The parent cell of `v` transports up to `List.Perm`. | — |
| `Deepen.mem_coupled_transport` | 119-136 | §3 **Membership in the coupled component transports** — the footprint's support is labelling-independent. | — |
| `Deepen.allSingletonsK_transport` | 140-147 | §4 The all-singletons gate is an **invariant `Bool`**: relabelling cannot change whether the footprint is forced. | — |
| `Deepen.chooseIdK_transport` | 149-180 | §4 **★ THE LOAD-BEARING TRANSPORT LEMMA.** The chosen cell id is an **invariant `Nat`** (equal, not conjugated), so the id sequence `deepen` records is labelling-independent — this is what reduces the route-(a) crux to "which member of a fixed cell does replay pick?". | — |
| `Deepen.step_transport` | 184-191 | §5 One individualize+refine step commutes with relabelling (`indivOne_transport` + `refineEquivariant_encodeFree`). | — |

## ChainDescent/KernelBase.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Kernel.nonRails` | 112-114 | — | Definition |
| `Kernel.supports` | 116-118 | — | Definition |
| `Kernel.suppCode` | 120-125 | — | Definition |
| `Kernel.baseSize` | 127-130 | — | Definition |
| `Kernel.baseAdj` | 132-143 | — | Definition |
| `Kernel.baseCol` | 145-153 | — | Definition |
| `Kernel.liftFun` | 157-172 | — | Definition |
| `Kernel.railImgList` | 174-179 | — | Definition |
| `Kernel.liftGen` | 181-189 | — | Definition |
| `Kernel.baseStack` | 193-198 | — | Definition |
| `Kernel.baseGens` | 200-207 | — | Definition |
| `Kernel.baseSupply` | 209-213 | — | Definition |

## ChainDescent/DeepenTinhofer.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.transportColouring_comp` | 40-47 | — | — |
| `Deepen.step_aut` | 49-60 | — | — |
| `Deepen.step_isColAut` | 62-69 | — | — |
| `Deepen.step_rerelate` | 71-83 | — | — |
| `Deepen.cidCell` | 91-93 | — | Definition |
| `Deepen.mem_cidCell_iff` | 95-97 | — | — |
| `Deepen.cidCell_nodup` | 99-100 | — | — |
| `Deepen.mem_cidCell_transport` | 102-104 | — | — |
| `Deepen.cidCell_perm_transport` | 106-115 | — | — |
| `Deepen.mem_cidCell_transport_apply` | 117-120 | — | — |
| `Deepen.cidCell_length_transport` | 122-125 | — | — |
| `Deepen.indivOne_refines` | 134-142 | — | — |
| `Deepen.step_refines` | 144-150 | — | — |
| `Deepen.isColAut_parent_of_refines` | 152-158 | — | — |
| `Deepen.isColAut_fixes_singleton` | 160-165 | — | — |
| `Deepen.step_preserves_singleton` | 167-172 | — | — |
| `Deepen.step_indiv_singleton` | 174-185 | — | — |
| `Deepen.CellSingleOrbit` | 196-199 | — | Definition |
| `Deepen.RigidObstructionAt` | 201-205 | — | Definition |
| `Deepen.rigidObstruction_of_not_cellSingleOrbit` | 207-215 | — | — |
| `Deepen.TinhoferPath` | 217-230 | — | Definition |
| `Deepen.Tinhofer` | 232-236 | — | Definition |
| `Deepen.cellSingleOrbit_transport` | 238-253 | — | — |
| `Deepen.deepen_acc` | 257-282 | — | — |
| `Deepen.foldl_min_mem` | 284-305 | — | — |
| `Deepen.chooseIdK_mem` | 307-318 | — | — |
| `Deepen.joint` | 320-446 | — | — |
| `Deepen.gate_unique` | 456-469 | — | — |
| `Deepen.twistOf_of_transport_fixing` | 471-522 | — | — |
| `Deepen.permOf_apply` | 530-536 | — | — |
| `Deepen.twistOf_id_off_K` | 538-554 | — | — |
| `Deepen.mem_deepenGens_of` | 556-579 | — | — |
| `Deepen.transportColouring_isColAut` | 581-588 | — | — |
| `Deepen.eq_of_mem_of_length_le_one` | 590-598 | — | — |
| `Deepen.offCoupled_singleton` | 600-626 | — | — |
| `Deepen.exec_recovers_cell_orbits` | 628-671 | — | — |
| `Deepen.wordReach_of_mem_verified` | 675-679 | — | — |
| `Deepen.wordReach_symm` | 681-684 | — | — |
| `Deepen.isColAut_mem_branches` | 686-691 | — | — |
| `Deepen.foldl_min_isSome` | 701-709 | — | — |
| `Deepen.discrete_of_chooseIdK_none` | 711-730 | — | — |
| `Deepen.deepen_discrete` | 732-754 | — | — |
| `Deepen.deepen_isSome` | 756-808 | — | — |
| `Deepen.deepen_succeeds` | 810-822 | — | — |
| `Deepen.allSingletonsK_of_discrete` | 824-849 | — | — |
| `Deepen.gate_of_discrete` | 851-884 | — | — |
| `Deepen.exec_recovers_refgen_on_cell` | 886-909 | — | — |
| `Deepen.wordReach_imp_isColAut` | 921-931 | — | — |
| `Deepen.deepen_branch_orbit_iff_aut` | 933-944 | — | — |
| `Deepen.deepen_branchOrbit_transport` | 946-969 | — | — |
| `Deepen.deepenSupply_guarded_canonizer_direct` | 971-984 | — | — |
| `Deepen.rigidObstruction_imp_not_cellIsOrbit` | 995-1007 | — | — |
| `Deepen.not_tinhoferPath_imp_rigidObstruction` | 1009-1035 | — | — |

## ChainDescent/DeepenR1.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.DeepenRefInExec` | 87-91 | — | Definition |
| `Deepen.wordReach_deepen_of_ref` | 93-103 | — | — |
| `Deepen.sameOrbits_of_core` | 105-109 | — | — |
| `Deepen.refInExec_of_mem_deepenGens` | 111-119 | — | — |

## ChainDescent/DeepenRef.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.deepenAll` | 59-73 | — | Definition |
| `Deepen.replayAll` | 75-82 | — | Definition |
| `Deepen.deepenRefGens` | 86-98 | — | Definition |
| `Deepen.deepenRefSupply` | 100-101 | — | Definition |
| `Deepen.deepen_mem_deepenAll` | 105-134 | — | — |
| `Deepen.replay_mem_replayAll` | 136-156 | — | — |
| `Deepen.deepenGens_subset_ref` | 160-200 | — | — |
| `Deepen.wordReach_mono` | 204-209 | More generators only make word-reachability easier. (`DeepenRef` has this lemma but is parked out of `build.sh`, so it is re-proved here.) | — |
| `Deepen.verified_deepen_subset_ref` | 211-217 | — | — |
| `Deepen.wordReach_ref_of_deepen` | 219-226 | — | — |

## ChainDescent/DeepenRefTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.contains_map_apply` | 72-78 | — | — |
| `Deepen.imgFun_transport` | 80-106 | — | — |
| `Deepen.twistOf_transport` | 110-122 | — | — |

## ChainDescent/RigidSeal.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidSeal.leafColKey` | 32-40 | The augmented force key (R0a): on the discretizing branch, ranks a vertex by the complete coloured-pointed invariant `(pin-rank, χ-in-rank-order, leaf-matrix)`; else the cell-size histogram. The plain `Force.lookaheadKey` (adjacency-only) is insufficient. | Definition |
| `RigidSeal.keyV_leafColKey` | 42-48 | Unfolds `keyV leafColKey` into its discretizing / histogram branches. | `@[simp]` |
| `RigidSeal.keyCost_leafColKey` | 50-52 | `leafColKey`'s per-branch cost: one warm refinement + `n²`, charged like `lookaheadKey`. | — |
| `RigidSeal.rankInv_transport` | 56-64 | The rank-`i` vertex of a relabelled discrete colouring is `σ` of the original's — the χ-in-rank-order equivariance atom. | — |
| `RigidSeal.r0a_core` | 68-93 | R0a core: from the three key component-equalities (leaf matrix, pin-rank, χ-in-rank-order) on discretizing pins, a colour-automorphism `u ↦ w` (`σ = π_w⁻¹π_u`). | — |
| `RigidSeal.keyEquivariant_leafColKey` | 97-118 | `leafColKey` is equivariant (pin-rank via `vertexRank_transport`, χ-order via `rankInv_transport`, leaf-matrix via `leafMatrix_transport`). | — |
| `RigidSeal.colAut_of_leafColKey_eq` | 122-146 | **R0a:** equal `leafColKey` values on the discretizing regime ⟹ a colour-automorphism `u ↦ w`. | — |
| `RigidSeal.RigidResolved` | 150-154 | The rigid-seam predicate (§4): force distinguishes every non-automorphic branch pair. | Definition |
| `RigidSeal.rigidResolved_leafColKey` | 156-164 | **R0a:** `leafColKey` discharges `RigidResolved` on the discretizing regime (contrapositive of `colAut_of_leafColKey_eq`), no wall. | — |
| `RigidSeal.nodeResolved_leafColKey_of_rigid_discretizing` | 168-182 | **R0a:** a rigid discretizing branch cell ⟹ `Select.NodeResolved` (feeds `HandledS` via `answersS_of_handledS`), no wall. | — |
| `RigidSeal.SmallAutThinAt` | 204-213 | The rigid seam's form of the wall `hSmallAutThin`: `leafColKey` separates non-automorphic pairs on the non-discretizing regime. Vacuous on the discretizing regime. | Definition |
| `RigidSeal.smallAutThinAt_of_all_discretize` | 215-222 | `SmallAutThinAt` holds vacuously when every branch vertex discretizes (R0a needs no wall there). | — |
| `RigidSeal.rigidResolved_of_smallAutThin` | 224-236 | **R0b:** `RigidResolved (leafColKey)` for the whole cell modulo exactly the wall `SmallAutThinAt` (discretizing pairs discharged by R0a). | — |
| `RigidSeal.nodeResolved_leafColKey_of_rigid` | 238-250 | **R0b:** `Select.NodeResolved` on any rigid cell modulo the wall `SmallAutThinAt`. | — |
| `RigidSeal.compKey` | 268-274 | — | Definition |
| `RigidSeal.keyV_compKey` | 276-282 | — | `@[simp]` |
| `RigidSeal.keyV_compKey_disc` | 284-287 | — | — |
| `RigidSeal.keyV_compKey_not_disc` | 289-292 | — | — |
| `RigidSeal.keyV_leafColKey_disc_head` | 294-299 | — | — |
| `RigidSeal.keyEquivariant_compKey` | 301-313 | — | — |
| `RigidSeal.SolverSeparates` | 315-324 | — | Definition |
| `RigidSeal.rigidResolved_compKey` | 326-352 | — | — |
| `RigidSeal.nodeResolved_compKey_of_rigid` | 354-366 | — | — |
## ChainDescent/ForcingCircuits.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ForcingCircuits.rowspace` | 47-50 | — | Definition |
| `ForcingCircuits.Forced` | 52-62 | — | Inductive |
| `ForcingCircuits.forced_certificate` | 68-144 | — | — |
| `ForcingCircuits.certificate_of_forced_notMem` | 146-152 | — | — |
| `ForcingCircuits.certificate_mem_rowspace` | 154-164 | — | — |

## ChainDescent/ForcingModel.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ForcingModel.ForcingModel` | 46-54 | — | Structure |
| `ForcingModel.Recoverable` | 58-62 | — | Definition |
| `ForcingModel.recoverable_mem_rowspace` | 64-67 | — | — |
| `ForcingModel.recoverable_of_model` | 69-78 | — | — |
| `ForcingModel.forcing_certificate_of_model` | 80-85 | — | — |
| `ForcingModel.RecoversRowspace` | 89-93 | — | Definition |
| `ForcingModel.rowspace_eq_span_recoverable` | 95-104 | — | — |

## ChainDescent/RigidSolveF2.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidSolveF2.dotP` | 33-34 | — | Definition |
| `RigidSolveF2.dotP_zero_right` | 36-37 | — | `@[simp]` |
| `RigidSolveF2.dotP_sub` | 39-40 | — | — |
| `RigidSolveF2.dotP_add_left` | 42-43 | — | — |
| `RigidSolveF2.dotP_smul_left` | 45-48 | — | — |
| `RigidSolveF2.IsRigidF2` | 50-53 | — | Definition |
| `RigidSolveF2.unique_solution_of_rigid` | 55-64 | — | — |
| `RigidSolveF2.dotP_zero_rowspace` | 66-75 | — | — |
| `RigidSolveF2.isRigidF2_rowspace` | 77-82 | — | — |

## ChainDescent/RigidSolverInterface.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidSolver.PtSolver` | 45-46 | — | `abbrev` |
| `RigidSolver.PtIsoInvariant` | 48-51 | — | Definition |
| `RigidSolver.PtSound` | 53-59 | — | Definition |
| `RigidSolver.encodeOpt` | 63-68 | — | Definition |
| `RigidSolver.skCost` | 70-72 | — | Definition |
| `RigidSolver.skOf` | 74-75 | — | Definition |
| `RigidSolver.keyV_skOf` | 77-78 | — | `@[simp]` |
| `RigidSolver.keyEquivariant_skOf` | 82-89 | — | — |
| `RigidSolver.solverSeparates_skOf` | 93-117 | — | — |

## ChainDescent/RigidSolverSound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidSolver.ptForm` | 37-41 | — | Definition |
| `RigidSolver.colAut_of_labelledAdj_eq` | 43-63 | — | — |
| `RigidSolver.colAut_of_ptForm_eq` | 65-79 | — | — |
| `RigidSolver.emitLabel` | 83-86 | — | Definition |
| `RigidSolver.ptSound_emitLabel` | 88-103 | — | — |
| `RigidSolver.GenEquivariant` | 107-112 | — | Definition |
| `RigidSolver.ptForm_transport` | 114-123 | — | — |
| `RigidSolver.ptIsoInvariant_emitLabel` | 125-141 | — | — |
| `RigidSolver.keyEquivariant_compKey_emitLabel` | 156-162 | — | — |
| `RigidSolver.nodeResolved_compKey_emitLabel` | 164-175 | — | — |
## ChainDescent/RigidRREF.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidRREF.rrefCanon` | 35-43 | The **canonical column-ordered F₂ RREF** — `Kernel.echelon rows` reordered so its pivots appear in increasing column order `0…m-1` (a `find?`-scan). Canonical *shape* (`gen` sub-brick A); canonicity as a subspace invariant is brick B. | Definition |
| `RigidRREF.mem_echelon_of_mem_rrefCanon` | 45-56 | Every pivot of the canonical form is a pivot of `echelon rows` (the reorder loses nothing). | — |
| `RigidRREF.mem_rrefCanon_of_mem_echelon` | 58-71 | Conversely every `echelon` pivot appears in the canonical form (at its own column); needs uniform-length rows for `pivInv_echelon`'s `col_lt`/`nodup`. | — |
| `RigidRREF.mem_rrefCanon_iff` | 73-76 | The canonical form and `echelon rows` have exactly the same pivots (a reordering). | — |
| `RigidRREF.rrefCanon_nodup` | 78-85 | The canonical pivot list is duplicate-free (distinct columns scanned once). | — |
| `RigidRREF.rrefCanon_cols_nodup` | 87-95 | Its pivot **columns** are distinct — the `PivInv.nodup` field, transported. | — |
| `RigidRREF.pivInv_rrefCanon` | 97-116 | **★ Row-space preservation for the canonical form**: `rrefCanon m rows` inherits `PivInv` — a reduced echelon system with the **same row space as the input, both directions**. The foundation bricks B/C/D build on. | — |
| `RigidRREF.xorRow_left_comm` | 127-131 | `xorRow` is left-commutative on equal-length rows. | — |
| `RigidRREF.combo_perm` | 133-149 | `combo` (XOR-fold) is invariant under permutation of an equal-length row list. | — |
| `RigidRREF.spans_nodup_combo` | 151-176 | **Dedup to a Nodup subset**: every span element is the XOR of a *duplicate-free* subset of the generators (over F₂ repeats cancel). | — |
| `RigidRREF.xorList_perm` | 178-180 | `xorList` (parity of `true`s) is permutation-invariant. | — |
| `RigidRREF.xorList_all_false` | 182-188 | `xorList` of an all-`false` list is `false`. | — |
| `RigidRREF.xorList_map_single` | 190-204 | Single-support XOR parity: if `g` is `true` on exactly one member of a `Nodup` list, the XOR of `g` over it is `true`. | — |
| `RigidRREF.combo_eq_zero_of_pivots_zero` | 206-237 | **★★ Kernel triviality (the transversal property)**: a row-space vector `false` at every pivot column is the zero row — the pivot rows are linearly independent. The workhorse of RREF-canonicity (brick B) pivot-row uniqueness. | — |
| `RigidRREF.LeadInv` | 247-249 | **Leading position**: every pivot row is `false` strictly below its own pivot column (the structural fact `PivInv` lacks). | Definition |
| `RigidRREF.len_echStep` | 251-272 | `echStep` preserves uniform row length. | — |
| `RigidRREF.leadInv_echStep` | 274-316 | **★ The `echelon` fold step preserves `LeadInv`**: new pivot `false` below its column by `findIdx?`; a triggered back-reduction has `c ≥ cp.1`, so never alters below `cp.1`. | — |
| `RigidRREF.lead_foldl` | 318-330 | The joint `length` + `LeadInv` invariant, folded over the input rows. | — |
| `RigidRREF.leadInv_echelon` | 332-337 | **★★ Leading position for `echelon`**: every pivot row is `false` strictly below its pivot column. The basis for pivot-column determination (brick B-cols). | — |
| `RigidRREF.recon` | 346-348 | Reconstruct `w` from its pivot coordinates: XOR the pivot rows at columns where `w` is set. | Definition |
| `RigidRREF.recon_getD_pivot` | 350-382 | **Pivot-coordinate evaluation**: `recon` agrees with `w` at every pivot column (the coordinate map is the identity on pivot coordinates). | — |
| `RigidRREF.recon_mem_span` | 384-391 | `recon m P w` lies in the row space `span(P)`. | — |
| `RigidRREF.reconstruction` | 393-411 | **★★ The reconstruction identity**: a row-space vector equals the XOR of the pivot rows at the columns where it is set (`xorRow w (recon w)` is zero at every pivot ⟹ kernel triviality). | — |
| `RigidRREF.pivotCol_isLeading` | 413-421 | **(B-cols) forward**: every pivot column is a leading position of the row space, witnessed by its own pivot row. | — |
| `RigidRREF.leading_isPivotCol` | 423-459 | **★★ (B-cols) backward**: every leading position of the row space is a pivot column (else reconstruction writes a leading-`c` codeword as an XOR of pivot rows all `>c`, forcing `w.getD c = false`). | — |
| `RigidRREF.pivotCols_eq` | 461-477 | **★★★ (B-cols)**: two reduced-echelon systems with the same row space have the **same pivot columns** (each = the space's leading positions). The column half of RREF uniqueness. | — |
| `RigidRREF.pivotRow_eq` | 485-521 | **★★ (B-rows)**: pivot rows are determined by the row space — for a shared pivot column, `xorRow ρ₁ ρ₂` is in the span and zero at every pivot, so kernel triviality gives `ρ₁ = ρ₂`. | — |
| `RigidRREF.rrefCanon_eq_of_span_eq` | 523-559 | **★★★ (B5) RREF canonicity**: two uniform-length row lists with the same row space have equal `rrefCanon` — the executable RREF is a canonical form of the *subspace*, independent of the generating list. The crux of brick (B). | — |
## ChainDescent/RigidFrame.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidFrame.transportRow` | 35-38 | A row over the vertices of `adj` transports to `relabelAdj σ adj` by precomposition with `σ⁻¹` (the F₂/vertex-column analog of `transportColouring`). | Definition |
| `RigidFrame.frameRow` | 40-43 | **The χ-framed row**: read `r`'s F₂ entries in χ-**rank** order (columns = vertices ordered by iso-invariant rank). `leafMatrix`'s idea for one F₂ vector. | Definition |
| `RigidFrame.length_frameRow` | 45-46 | `(frameRow χ r).length = n`. | `@[simp]` |
| `RigidFrame.frameSys` | 48-50 | The χ-framed system — every extracted row read in χ-rank order. | Definition |
| `RigidFrame.frameRow_transport` | 52-61 | **★ The framed row is literally σ-invariant**: reading `r ∘ σ⁻¹` in the transported χ-rank order = reading `r` in the original, via `RigidSeal.rankInv_transport`. | — |
| `RigidFrame.frameSys_transport` | 63-70 | The whole framed system is literally σ-invariant when each row transports as `transportRow σ`. | — |
| `RigidFrame.framedRREF_transport` | 72-81 | **★★ (C) the χ-framed RREF transports**: χ-rank column order makes the framed system literally σ-invariant (NOT RREF column-equivariance, which is false), so its `rrefCanon` is σ-invariant — reduces `gen`'s `GenEquivariant` to the carried extraction-transport. | — |
| `RigidFrame.framedRREF_span_invariant` | 83-92 | The framed RREF is also (from brick B) a canonical function of the framed code — robustness to how the extraction presents its generators. | — |
## ChainDescent/RigidGen.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidGen.RefEquivariant` | 44-47 | The refinement transports: refining the σ-relabelled graph = the σ-transport of the refinement. | Definition |
| `RigidGen.genOfRef` | 49-53 | **`gen` from a refinement**: `rankPerm` of χ refined by the solve (`ref adj χ`) when discrete, else flag; ignores the pin `v`. | Definition, `noncomputable` |
| `RigidGen.rankPerm_transport` | 55-65 | `rankPerm (transportColouring σ χ) = rankPerm χ * σ⁻¹` — the `GenEquivariant` shape, from `vertexRank_transport`. | — |
| `RigidGen.genEquivariant_genOfRef` | 67-80 | **★★ (D) the labelling read is equivariant**: `GenEquivariant (genOfRef ref)` ⟸ `RefEquivariant ref` *alone* — the rigid `①`'s equivariance reduces to the refinement transporting. | — |
| `RigidGen.emit_isSome_genOfRef` | 82-88 | The emit is `some` iff the refinement is discrete — so `hemit` reduces to `ref` discretizing on the residue (carried per-family). | — |
| `RigidGen.keyEquivariant_compKey_genOfRef` | 90-95 | **★★★ (D) capstone**: the whole `compKey` `①` obligation closes on `RefEquivariant ref` alone (composed with P3-Sound). | — |
| `RigidGen.nodeResolved_compKey_genOfRef` | 97-107 | **★★★ (D) firing capstone**: `NodeResolved` on a rigid cell ⟸ `ref` discrete (⟹ `hemit`) + rigidity — soundness free. Closes the rigid force branch. | — |
## ChainDescent/GaugeAbelian.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.isSolvable_of_carrier_comm` | 36-42 | — | — |
| `GaugeComplex.dotP_add_right` | 49-51 | — | — |
| `GaugeComplex.kerF2` | 53-64 | — | Definition |
| `GaugeComplex.mem_kerF2` | 66-67 | — | `@[simp]` |
| `GaugeComplex.isRigidF2_iff_kerF2_eq_bot` | 69-74 | — | — |
| `GaugeComplex.rigid_unique_solve` | 76-87 | — | — |

## ChainDescent/GaugeBridge.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.GaugeContract` | 35-42 | — | Structure |
| `GaugeComplex.GaugeContract.Equiv` | 44-47 | — | Definition |
| `GaugeComplex.holonomy_iff_gauge` | 49-57 | — | — |
| `GaugeComplex.locallyFlat_of_gauge` | 59-63 | — | — |
| `GaugeComplex.gaugeMax` | 67-80 | — | Definition |
| `GaugeComplex.mem_gaugeMax` | 82-86 | — | `@[simp]` |
| `GaugeComplex.gaugeContractMax` | 88-110 | — | Definition |

## ChainDescent/GaugeComplex.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.refineStep_ne_iff_exists_count_ne` | 40-58 | — | — |
| `GaugeComplex.nbhdClass` | 60-66 | — | Definition |
| `GaugeComplex.count_signature_eq_card` | 68-78 | — | — |
| `GaugeComplex.refineStep_eq_iff_forall_card_eq` | 95-107 | — | — |
| `GaugeComplex.localExchange_of_refineStep_eq` | 109-118 | — | — |
| `GaugeComplex.localExchange_of_equitable` | 120-131 | — | — |
| `GaugeComplex.IsColAut` | 157-161 | — | Definition |
| `GaugeComplex.signature_eq_of_colAut` | 163-186 | — | — |
| `GaugeComplex.refineStep_eq_of_colAut` | 188-192 | — | — |
| `GaugeComplex.SameOrbit` | 194-196 | — | Definition |
| `GaugeComplex.LocallyFlat` | 198-201 | — | Definition |
| `GaugeComplex.locallyFlat_iff` | 203-218 | — | — |
| `GaugeComplex.sameOrbit_imp_locallyFlat` | 220-229 | — | — |
| `GaugeComplex.HolonomyNontrivial` | 231-236 | — | Definition |
| `GaugeComplex.holonomyNontrivial_iff_diff_orbit` | 238-245 | — | — |
| `GaugeComplex.not_sameOrbit_of_holonomyNontrivial` | 247-258 | — | — |

## ChainDescent/GaugeIsolation.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.isColAut_one` | 31-34 | — | — |
| `GaugeComplex.IsRigid` | 36-42 | — | Definition |
| `GaugeComplex.sameOrbit_iff_eq_of_rigid` | 44-52 | — | — |
| `GaugeComplex.holonomyNontrivial_iff_flat_ne_of_rigid` | 54-61 | — | — |
| `GaugeComplex.CarriesGauge` | 63-66 | — | Definition |
| `GaugeComplex.carriesGauge_iff_exists_holonomy_of_rigid` | 68-83 | — | — |

## ChainDescent/GaugeLayer.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.derivedSeries_pi_const` | 47-57 | **W2 R-c extraction L1.** The gauge's derived tower decomposes coordinatewise: `derivedSeries (ι→G₀) k = ∏ᵢ derivedSeries G₀ k` (finite `ι`), via Mathlib `commutator_pi_pi_of_finite`. = each layer a free module of rank `|gadgets|` ⟹ each `of_solvable_tower` step is a per-coordinate LINEAR problem, not a coset search. §3b. | — |
| `GaugeComplex.mem_derivedSeries_pi` | 59-64 | L1 membership form: `x ∈ derivedSeries (ι→G₀) k ↔ ∀ i, x i ∈ derivedSeries G₀ k` (the per-gadget characterization the layer solve consumes). | — |
| `GaugeComplex.map_eval_layer` | 66-72 | The k-th product-gauge layer maps onto each gadget's local layer `derivedSeries G₀ k` (restates `map_eval_derivedSeries` for the layer narrative). | — |
| `GaugeComplex.commutator_mem_derivedSeries_succ` | 76-84 | **L2 — the layer is abelian.** `a b ∈ derivedSeries G k ⟹ ⁅a,b⁆ ∈ derivedSeries G (k+1)`: `D_k` commutes modulo `D_{k+1}`, so `A_k = D_k/D_{k+1}` is abelian (what makes the per-layer solve linear). | — |
| `GaugeComplex.layerCoeff` | 86-91 | The abelian layer coefficient group `A_k = D_k/D_{k+1}` = `Abelianization ↥(derivedSeries G k)` (a `CommGroup`); the product layer is the free module `ι → A_k`. | `abbrev` |
| `GaugeComplex.derivedProj` | 93-99 | Coordinatewise projection `↥(derivedSeries (ι→G₀) k) →* ↥(derivedSeries G₀ k)`, `x ↦ x i` (lands by L1). | Definition |
| `GaugeComplex.derivedProj_surjective` | 101-104 | `derivedProj k i` is surjective (constant tuple `fun _ => g` witnesses). | — |
| `GaugeComplex.layerProj` | 106-112 | The `i`-th coordinate map on layer coefficients `A_k(ι→G₀) →* A_k(G₀)` (abelianizes `derivedProj`). | Definition |
| `GaugeComplex.layerProj_surjective` | 114-120 | **L2 — the product layer surjects coordinatewise onto each local `A_k`** — the `ι → A_k` free-module coordinate structure L3's linear solve consumes. | — |
| `GaugeComplex.dotP_smul_right` | 126-130 | The F₂ pairing is linear in the scalar on the assignment side: `dotP r (c • x) = c * dotP r x`. | — |
| `GaugeComplex.kerF2_smul_mem` | 132-138 | **L3 — the abelian gauge is `ZMod 2`-scalar-closed:** `kerF2 H` is a subspace, so the layer solve is linear. | — |
| `GaugeComplex.kerF2Submodule` | 140-151 | **L3 — `kerF2` as an F₂-subspace.** The abelian branch's gauge upgraded from `AddSubgroup` to a genuine `Submodule (ZMod 2) (ι→ZMod 2)` — the concrete `A_0 = ZMod 2` field instance of "each layer is an `A_k`-submodule of `ι → A_k`, solved by Smith/Gaussian." | Definition |
| `GaugeComplex.mem_kerF2Submodule` | 153-166 | `kerF2Submodule H` has exactly the `kerF2 H` carrier — same gauge, now recorded as linear. | `@[simp]` |

## ChainDescent/GaugeNonabelian.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.isSolvable_pi` | 46-64 | — | Instance |
| `GaugeComplex.isSolvable_recoveredGauge` | 66-70 | — | — |
| `GaugeComplex.map_eval_derivedSeries` | 72-78 | — | — |
| `GaugeComplex.isSolvable_extension` | 82-89 | — | — |
| `GaugeComplex.recoveredGauge_reduces_to_abelian` | 93-102 | — | — |
| `GaugeComplex.isSolvable_gaugeCarrier` | 104-110 | — | — |
| `GaugeComplex.isSolvable_alt3` | 114-121 | — | Instance |
| `GaugeComplex.isSolvable_perm3` | 123-128 | — | Instance |
| `GaugeComplex.perm3_not_comm` | 130-145 | — | — |

## ChainDescent/GaugeSolvable.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `GaugeComplex.of_solvable_tower` | 51-74 | — | — |
| `GaugeComplex.of_solvable_abelian_base` | 76-88 | — | — |
## ChainDescent/RigidRefine.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RigidRefine.transportVec` | 72-79 | The `ZMod 2` vertex-column transport `x ↦ x ∘ σ.symm`, as a `LinearMap` — the analog of `RigidFrame.transportRow` for F₂ codewords/assignments. | Definition |
| `RigidRefine.transportVec_apply` | 81-82 | `transportVec σ x u = x (σ.symm u)`. | `@[simp]` |
| `RigidRefine.rowspace_transport` | 84-90 | **The one new lemma of Route B′.** `(rowspace H).map (transportVec σ) = rowspace (H.image (transportVec σ))` — `span` commutes with the linear map `transportVec σ` (`Submodule.map_span`). Makes the coordinate-free forced-reader equivariant with no `Discrete χ`, no frame. | — |
| `RigidRefine.transportVec_injective` | 92-98 | `transportVec σ` is injective (precomposition by the bijection `σ.symm`). | — |
| `RigidRefine.transportVec_e` | 100-110 | `transportVec σ (e_v) = e_(σv)` (`Pi.single`) — the bridge turning `rowspace_transport` into a per-vertex fact. | — |
| `RigidRefine.e_mem_rowspace_transport` | 112-124 | **Per-vertex forcedness is σ-invariant:** `e_(σv) ∈ rowspace (H.image (transportVec σ)) ↔ e_v ∈ rowspace H` (via `rowspace_transport` + `transportVec_e` + injectivity). "Is `v` a rigid/pinned coordinate" transports, no `Discrete χ`, no frame. | — |
| `RigidRefine.forcedVal` | 128-140 | **The coordinate-free forced-value reader:** `some (x₀ v)` if `e_v ∈ rowspace H` (forced/rigid coord, canonical value), else `none` (gauge/free coord, left unrefined = consume's job). P2's forcedness read per vertex. | Definition, `noncomputable` |
| `RigidRefine.forcedVal_transport` | 142-154 | **★★ The reader is a vertex-invariant** (unconditional): `forcedVal (H.image (transportVec σ)) (transportVec σ x₀) (σ v) = forcedVal H x₀ v`. The heart of Route B′'s `①`. | — |
| `RigidRefine.RefExtractEquivariant` | 158-166 | The carried extraction-transport hypothesis: the extracted system + witness transport under σ (row set imaged by `transportVec σ`, witness by `transportVec σ`). The P2/`gForce`/`encodeFreeFast` realization = `ForcingModel.bridge`; the SOLE obligation `refineByFrame`'s `①` needs. | Definition |
| `RigidRefine.frameRead` | 168-172 | The per-vertex forced reader assembled from an extraction: `forcedVal (extract adj χ).1 (extract adj χ).2 v`. | Definition, `noncomputable` |
| `RigidRefine.frameRead_transport` | 174-183 | `frameRead` is a vertex-invariant given `RefExtractEquivariant` — `forcedVal_transport` pulled through the carried extraction transport. | — |
| `RigidRefine.encOpt` | 185-189 | Encode a forced value into the refined colour's low digit: `none ↦ 0`, `some 0 ↦ 1`, `some 1 ↦ 2` (injective ⟹ genuine refinement). | Definition |
| `RigidRefine.refineByFrame` | 191-198 | **The concrete rigid refinement `ref` (Route B′):** `3 * χ v + encOpt (frameRead …)`. Forced (rigid) coords split off by value; gauge/free coords keep χ's tie. Parameterized by the extraction. | Definition, `noncomputable` |
| `RigidRefine.refEquivariant_refineByFrame` | 200-211 | **★★★ Route B′ payoff:** `RefEquivariant (refineByFrame extract)`, **UNCONDITIONAL** (no `Discrete χ`, no frame) on the single carried obligation `RefExtractEquivariant`. Closes the concrete rigid `ref`'s whole `①`/equivariance. | — |
| `RigidRefine.keyEquivariant_compKey_refineByFrame` | 213-221 | **★★★ (D) `①` capstone, concretely:** `compKey`'s `KeyEquivariant` closes for `refineByFrame` on `RefExtractEquivariant` alone (composes `refEquivariant_refineByFrame` with `RigidGen.keyEquivariant_compKey_genOfRef`). (D) untouched. | — |
| `RigidRefine.nodeResolved_compKey_refineByFrame` | 223-234 | **★★★ (D) firing capstone, concretely:** `NodeResolved` on a rigid cell where `refineByFrame` is discrete — soundness free, `hext`-free (only `refineByFrame` discrete + rigidity). Instantiates `RigidGen.nodeResolved_compKey_genOfRef`. | — |
| `RigidRefine.refExtractEquivariant_trivial` | 236-243 | **Non-vacuity of `RefExtractEquivariant`:** the trivial extraction `(∅, 0)` satisfies it (`∅` images to `∅`, `transportVec σ 0 = 0`). The predicate is genuinely satisfiable. | — |
| `RigidRefine.RowAtEquivariant` | 252-256 | A local row-builder is equivariant: the row at `σi` on the σ-relabelled node is `transportVec σ` of the row at `i`. | Definition |
| `RigidRefine.WitEquivariant` | 258-261 | The witness assignment transports as `transportVec σ`. | Definition |
| `RigidRefine.extractOf` | 263-267 | The extraction from a local row-builder + witness: rows = `{rowAt adj χ i : i}` (as a `Finset.image`), witness = `wit adj χ`. | Definition |
| `RigidRefine.refExtractEquivariant_extractOf` | 269-291 | **★ Step A (generic):** `RowAtEquivariant rowAt` + `WitEquivariant wit` ⟹ `RefExtractEquivariant (extractOf rowAt wit)` — the row set transports by reindexing the `Finset.image` along the bijection σ (`univ.image σ = univ` + `Finset.image_image` + pointwise `RowAtEquivariant`). **The faithful per-family (CFI) extraction discharges its `①` obligation here.** | — |
| `RigidRefine.rowAdj` | 293-295 | Concrete row-builder: the F₂ adjacency row of `i` (`v ↦ adj i v mod 2`) — a genuine graph invariant. | Definition |
| `RigidRefine.witChi` | 297-299 | Concrete witness: `χ` reduced mod 2. | Definition |
| `RigidRefine.rowAtEquivariant_rowAdj` | 301-304 | `rowAdj` is `RowAtEquivariant` (adjacency + `σ.symm` cancellation). | — |
| `RigidRefine.witEquivariant_witChi` | 306-309 | `witChi` is `WitEquivariant` (χ transports pointwise). | — |
| `RigidRefine.refExtractEquivariant_adj` | 311-313 | **★ Step B:** the adjacency extraction `extractOf rowAdj witChi` transports — a concrete, non-vacuous `RefExtractEquivariant` witness. | — |
| `RigidRefine.keyEquivariant_compKey_refineByFrame_adj` | 315-323 | **★★★ Step C:** `compKey`'s `KeyEquivariant` for the concrete `refineByFrame (extractOf rowAdj witChi)` with **ZERO hypotheses** — the rigid-linear `①`/**equivariance** instantiated end-to-end. ⚠ NOT the same as solving the rigid case: `②`/discretization is separate and the single-bit reader does NOT meet it (see `hemit_of_forcedSeparates` note). | — |
| `RigidRefine.encOpt_lt_three` | 333-338 | `encOpt o < 3` (`none ↦ 0`, `some x ↦ 1 + x.val ≤ 2`) — the digit bound that splits the refined colour. | — |
| `RigidRefine.encOpt_injective` | 340-353 | `encOpt` is injective on `Option (ZMod 2)` (`0,1,2` distinct; `ZMod.val_injective`). | — |
| `RigidRefine.ForcedSeparates` | 355-361 | The reader's values separate co-cellular vertices: `χ u = χ v ∧ frameRead u = frameRead v ⟹ u = v`. ⚠ **UNSATISFIABLE for the single-bit `frameRead`** on any rigid cell with >2 vertices (one F₂ bit ⟹ ≤2 classes) — the multipede core. Reader coarseness, not faithfulness; the discretizing reader needs the structural (Recover) frame (step 6). | Definition |
| `RigidRefine.hemit_of_forcedSeparates` | 363-377 | **★ Step 5 — the `②` reduction (a correct lemma).** `Discrete (refineByFrame extract adj χ) ⟸ ForcedSeparates`, via `encOpt_injective`. Family-agnostic and sound; ⚠ but `ForcedSeparates` is not achievable by the single-bit reader on rigid multipedes (see its note) — it becomes satisfiable only for the richer structural-frame reader (step 6). | — |
| `RigidRefine.nodeResolved_compKey_refineByFrame_of_forcedSeparates` | 379-393 | **★★★ `②`/firing capstone (interface):** `NodeResolved` ⟸ `ForcedSeparates` + rigidity (soundness free, `hext`-free). Correct interface; ⚠ its `ForcedSeparates` premise is unmet by the single-bit reader on rigid cells >2 vertices — the discretizing reader (step 6, structural frame) is what satisfies it. | — |
| `RigidRefine.ReadEquivariant` | 409-414 | **Step 6 — the `②` fix interface.** A per-vertex canonical reader `read : … → Fin n → ℕ` is equivariant = a vertex-invariant (transports along σ). The structural (Recover-ordered) reader has it from structural-order transport (carried); `encOpt ∘ frameRead` has it too but is too coarse to separate. | Definition |
| `RigidRefine.refineBy` | 416-420 | Refine χ by a per-vertex canonical reader: `Nat.pair (χ v) (read adj χ v)` (injective ⟹ genuine refinement). The general form the structural frame plugs into — replaces the single-bit `refineByFrame`. | Definition |
| `RigidRefine.refEquivariant_refineBy` | 422-430 | **★ `①` (general):** `RefEquivariant (refineBy read)` from `ReadEquivariant read` alone — reader-agnostic; the structural reader inherits it. | — |
| `RigidRefine.ReadSeparates` | 432-437 | The reader separates co-cellular vertices — the `②`/discretization obligation. Carried on the structural (Recover-ordered) reader ("the ordered base pins every vertex"); NOT met by `encOpt ∘ frameRead` on rigid cells (pigeonhole). The honest restatement of `ForcedSeparates`. | Definition |
| `RigidRefine.discrete_refineBy` | 439-448 | **★ `②` (general):** `Discrete (refineBy read adj χ)` from `ReadSeparates` (via `Nat.pair` injectivity). | — |
| `RigidRefine.keyEquivariant_compKey_refineBy` | 450-454 | **★★★ `①` capstone (general):** `compKey`'s `KeyEquivariant` for `refineBy read` from `ReadEquivariant`. | — |
| `RigidRefine.nodeResolved_compKey_refineBy_of_readSeparates` | 456-467 | **★★★ `②`/firing capstone (general):** `NodeResolved` for `refineBy read` from `ReadSeparates` + rigidity. The rigid-linear seal for the structural reader rests on exactly `{ReadEquivariant, ReadSeparates}`, both carried on the recovered canonical ordered base. | — |
| `RigidRefine.readEquivariant_encOpt_frameRead` | 469-477 | The single-bit reader is a **coarse** `ReadEquivariant` instance (from `frameRead_transport`) — steps 1–5 supply a *transporting* reader — but it does NOT satisfy `ReadSeparates` on rigid cells (≤2 F₂ classes), which is why the structural (Recover) reader is needed for `②`. | — |
| `RigidRefine.frameRowBy` | 488-490 | **Step 6b.** Read a row in a **given** column order `ord` (position ↦ vertex) — the general-order, χ-rank-free frame. | Definition |
| `RigidRefine.frameSysBy` | 492-494 | The system read in the order `ord`. | Definition |
| `RigidRefine.frameRowBy_transport` | 496-504 | **★ The unlock:** `frameRowBy (σ · ord) (transportRow σ r) = frameRowBy ord r` — the general-order framed row is σ-invariant when `ord' = σ · ord`, **with no `Discrete χ`** (vs. the χ-rank frame, whose gap was `rankInv` injectivity). | — |
| `RigidRefine.frameSysBy_transport` | 506-510 | The whole system framed by `σ · ord` (rows transported) equals the system framed by `ord`. | — |
| `RigidRefine.framedRREFBy_transport` | 512-516 | **★★** the structurally-framed `rrefCanon` transports (`ord' = σ · ord`), **unconditionally** — the χ-rank-free analog of `RigidFrame.framedRREF_transport`. | — |
| `RigidRefine.colSig` | 518-520 | The column of an RREF at position `pos` — the vertex's coordinate signature across the pivot rows. | Definition |
| `RigidRefine.bitsToNat` | 522-524 | Encode a bit-list to `ℕ` (leading-`1` sentinel). | Definition |
| `RigidRefine.structRead` | 526-531 | **The structural reader:** vertex `v`'s RREF-column signature over the recovered order `ord`, encoded to `ℕ`. Parameterized by the carried `Recover` objects (order `ord`, system `Hs`). | Definition |
| `RigidRefine.OrdEquivariant` | 533-536 | The recovered order transports as `ord' = σ · ord` (iso-invariant structural order — carried on `Recover`). | Definition |
| `RigidRefine.HsEquivariant` | 538-541 | The recovered system transports as `Hs' = Hs.map (transportRow σ)` (carried on `Recover`). | Definition |
| `RigidRefine.readEquivariant_structRead` | 543-559 | **★★★ Step 6b `①` payoff:** `ReadEquivariant (structRead ord Hs)` from the carried `OrdEquivariant` + `HsEquivariant` and `framedRREFBy_transport`. **No `Discrete χ`** — the discretizing reader's equivariance, resolving the (C) gap structurally. | — |
| `RigidRefine.keyEquivariant_compKey_structRead` | 561-568 | **★★★ Step 6b `①` capstone:** `compKey`'s `KeyEquivariant` for the structural reader — closes on `OrdEquivariant` + `HsEquivariant` alone. | — |
| `RigidRefine.readSeparates_of_injective` | 570-582 | **`②`:** `ReadSeparates (structRead ord Hs) ⟸ structRead injective` — "the recovered ordered base pins every vertex" = full-rank on the rigid residue (via `IsRigidF2`). Carried; non-vacuity = the rigid solver (probe `scratchpad/probe_rigid.py`). | — |
| `RigidRefine.nodeResolved_compKey_structRead` | 584-598 | **★★★ Step 6b `②`/firing capstone:** `NodeResolved` for the structural reader from its injectivity + rigidity. With `keyEquivariant_compKey_structRead`, the rigid-linear seal for the discretizing reader rests on exactly the 3 carried `Recover` facts `{OrdEquivariant, HsEquivariant, structRead-injective}` — no `Discrete χ`, no coordinate-free coarseness. | — |
| `RigidRefine.skRead` | 618-622 | **The force key read directly off a per-vertex reader** — `read`'s value wrapped as a `Force.Key` (`[read adj χ v]`, cost `skCost`), NOT routed through `genOfRef`/`emitLabel` (whose `Discrete` gate is all-or-nothing). What lets the rigid solver fire per-pair on a mixed cell. | Definition |
| `RigidRefine.keyV_skRead` | 624-626 | The key-value projection of `skRead read` is `[read adj χ v]` (definitional). | `@[simp]` |
| `RigidRefine.keyEquivariant_skRead` | 628-634 | **Step 7 ① (per-pair key).** `KeyEquivariant (skRead read)` from `ReadEquivariant read` alone — the direct reader key (value `[read …]`, NOT via `genOfRef`) is equivariant. Feeds `keyEquivariant_compKey`. | — |
| `RigidRefine.ReadSeparatesRigid` | 636-646 | **Step 7 ② predicate = the KERNEL CHARACTERIZATION on exposed pairs.** Non-automorphic, non-discretizing, co-cellular `(u,w)` ⟹ distinct read (⟺ `e_u−e_w ∉ ker(recovered H)`). Mixed-native: says nothing about gauge/automorphic pairs (they tie, consume's job) — only the rigid decisions separate. Stated ONCE over the generic reader, not per family. | Definition |
| `RigidRefine.solverSeparates_skRead` | 648-660 | **Step 7 firing reduction (no `hemit`).** `SolverSeparates (compKey (skRead read)) ⟸ ReadSeparatesRigid` — the mirror of `RigidSolver.solverSeparates_skOf` but the direct reader key never flags, so the full-discretization completeness (`hemit`) drops out: mixed cells fire without global discreteness. | — |
| `RigidRefine.keyEquivariant_compKey_skRead` | 662-665 | **Step 7 ① capstone (generic).** `compKey (skRead read)`'s `KeyEquivariant` from `ReadEquivariant read`, via `keyEquivariant_compKey`. | — |
| `RigidRefine.nodeResolved_compKey_skRead` | 667-678 | **Step 7 ②/firing capstone (generic, MIXED-NATIVE).** `Select.NodeResolved (compKey (skRead read))` from `ReadSeparatesRigid` + rigidity, via `RigidSeal.nodeResolved_compKey_of_rigid` — **no global discreteness**. Gauge pairs stay tied (consume's `cellIsOrbit` disjunct); only rigid decisions separate. | — |
| `RigidRefine.readSeparatesRigid_of_injective` | 680-688 | **`ker=0` special case.** Global reader injectivity (the purely-rigid `IsRigidF2 ⟹ structRead` injective) ⟹ `ReadSeparatesRigid` — a non-automorphic pair is distinct (else `IsColAut.one` maps `u↦w`). Subsumes step 6b's fully-rigid firing under step 7. | — |
| `RigidRefine.skStruct` | 692-697 | **The concrete mixed-native force key** `skStruct ord Hs := skRead (structRead ord Hs)` — the structural RREF-column reader wrapped directly as a `Force.Key`, bypassing `genOfRef`. | Definition |
| `RigidRefine.keyEquivariant_compKey_skStruct` | 699-706 | **Step 7 ① capstone (structural).** `compKey (skStruct ord Hs)`'s `KeyEquivariant` from the two carried transport facts `OrdEquivariant` + `HsEquivariant` — no global discreteness, no `genOfRef`. | — |
| `RigidRefine.nodeResolved_compKey_skStruct` | 708-722 | **★ Step 7 ②/firing capstone (structural, MIXED-NATIVE).** `NodeResolved (compKey (skStruct ord Hs))` from the per-pair kernel characterization `ReadSeparatesRigid (structRead ord Hs)` + rigidity, no global discreteness — the discretizing reader firing on a MIXED cell (forced pairs separate, gauge pairs tie), which step 6b could not do. Seal now rests on `{OrdEquivariant, HsEquivariant, ReadSeparatesRigid(structRead)}`. | — |
| `RigidRefine.nodeResolved_compKey_skStruct_of_injective` | 724-736 | **Purely-rigid firing as a corollary of step 7.** Global `structRead` injectivity ⟹ `nodeResolved_compKey_skStruct`, unifying step 6b's fully-rigid case with the per-pair route via `readSeparatesRigid_of_injective`. | — |
| `RigidRefine.rrefCanon_congr_perm` | 753-760 | **`rrefCanon` is `List.Perm`-invariant on its rows** — a row permutation preserves the row space (`Spans` both ways via `Spans.mono`), so the canonical RREF is unchanged. The "row order doesn't matter" fact any concrete index-based extraction needs; via `RigidRREF.rrefCanon_eq_of_span_eq`. | — |
| `RigidRefine.finRange_map_perm` | 762-768 | Mapping an `Equiv.Perm` over `List.finRange n` permutes it (same nodup elements) — the bijective-reindex helper for `hsAdj_transport_perm`. | — |
| `RigidRefine.boolRow` | 770-771 | The concrete adjacency Bool-row of vertex `i`: `v ↦ decide (adj i v ≠ 0)`. | Definition |
| `RigidRefine.hsAdj` | 773-777 | **The concrete extracted system** — the graph's adjacency rows as an F₂ Bool system (χ-independent; the `List` analog of step 4's `rowAdj`). The `Hs` the structural reader consumes; the per-family faithful extraction (CFI rails) slots in the same way. | Definition |
| `RigidRefine.boolRow_relabel` | 779-784 | The relabelled adjacency row is the transported row at the pre-image index (`transportRow σ (boolRow adj (σ.symm i))`) — a pure reindex + column transport. | — |
| `RigidRefine.hsAdj_transport_perm` | 786-798 | **★ `hsAdj` transports up to `List.Perm`** — the σ-relabelled system is a row-permutation of the column-transported system. The honest, row-order-agnostic form of `HsEquivariant` (a real index-based extraction meets the literal list equality only up to row permutation). | — |
| `RigidRefine.length_mem_frameSysBy` | 800-805 | Every row of a `frameSysBy` output has length `n` (it maps over `finRange n`) — the uniform-length hypothesis for `rrefCanon_congr_perm`. | — |
| `RigidRefine.framedRREF_hsAdj_transport` | 807-817 | **★★ The structurally-framed RREF of the concrete system transports** (order `o ↦ σ·o`) — the `hsAdj` instance of `framedRREFBy_transport` with the row-permutation absorbed by `rrefCanon_congr_perm`. Exactly what `readEquivariant_structRead` consumes at the `Hs` step, now discharged for the concrete extraction. | — |
| `RigidRefine.readEquivariant_structRead_hsAdj` | 819-833 | **★★★ Step 8 payoff — `ReadEquivariant (structRead ord hsAdj)` from `OrdEquivariant` ALONE.** `HsEquivariant` is discharged for the concrete adjacency extraction (via span-level `framedRREF_hsAdj_transport`), so a concrete `Recover` for the structural reader now carries only the order `ord` (piece 2, the crux) + the kernel predicate (piece 3). | — |
| `RigidRefine.keyEquivariant_compKey_skStruct_hsAdj` | 835-841 | **★★★ Step 8 ① capstone** — the mixed-native force key's equivariance on the concrete extraction, modulo ONLY `OrdEquivariant`. `HsEquivariant` gone. | — |
| `RigidRefine.FramesEquivariant` | 862-866 | **Step 9A — the candidate frame set transports** (`frames (relabel σ)(transport χ) = (frames adj χ).image (σ·)`): iso-invariance of the candidate SET of column orders, not of any single frame. The object that exists on ALL inputs, unlike an equivariant Perm (which needs rigidity). | Definition |
| `RigidRefine.KeyTransport` | 868-872 | The frame key is iso-invariant: `key (relabel σ)(transport χ)(σ·o) = key adj χ o`. Free for `hsAdj` (`keyTransport_hsAdj`). | Definition |
| `RigidRefine.IsMinFrame` | 874-878 | `o` is a key-minimal candidate frame at `(adj,χ)` — the canonical column order via lex-min over the equivariant frame set (C# B2). | Definition |
| `RigidRefine.isMinFrame_transport` | 880-897 | **★ The min frame transports** (`o ↦ σ·o`): candidate set transports + key transports ⟹ a minimizer maps to a minimizer. The heart of the min-over-set engine — why it is iso-invariant where a single equivariant Perm cannot exist. | — |
| `RigidRefine.minOrd` | 899-904 | The selected canonical order — a chosen min frame (needs existence; uniqueness makes it equivariant). | Definition, `noncomputable` |
| `RigidRefine.isMinFrame_minOrd` | 906-909 | `minOrd` is a min frame (`Classical.choose_spec`). | — |
| `RigidRefine.ordEquivariant_minOrd` | 911-925 | **★★ `OrdEquivariant` for the min-frame order on a UNIQUE min** — both `minOrd (relabel σ)(transport χ)` and `σ·minOrd adj χ` are min frames there (`isMinFrame_transport`), so uniqueness forces equality. Discharges step 8's order obligation from {`FramesEquivariant`, existence, uniqueness}; uniqueness ⟺ trivial residual symmetry ⟺ the rigid regime. | — |
| `RigidRefine.frameKeyHsAdj` | 927-930 | The concrete `hsAdj` frame key: any encoding `f` of the framed canonical RREF `rrefCanon (frameSysBy o (hsAdj …))`. | Definition, `noncomputable` |
| `RigidRefine.keyTransport_hsAdj` | 932-938 | **`KeyTransport` is FREE for `hsAdj`** — for ANY encoding `f`, the key transports because the framed RREF transports (`framedRREF_hsAdj_transport`). The engine's key obligation costs nothing on the concrete extraction. | — |
| `RigidRefine.keyEquivariant_compKey_skStruct_minFrame` | 940-955 | **★★★ Step 9A capstone** — the mixed-native force key's `①` on the concrete extraction via the MIN-frame order, modulo {`FramesEquivariant`, existence, uniqueness} ONLY. The crux's `①` side resolved; what remains is the concrete frame set (§9B) and uniqueness (§9C, the rigid regime). | — |
| `RigidRefine.framesUniv` | 970-972 | The exhaustive frame set — every column order (`fun _ _ => univ`). The correct-but-exponential (`n!`) concrete `frames`; the poly/greedy structural set is a deferred ②-cost refinement into the same 9A engine. | Definition |
| `RigidRefine.framesEquivariant_univ` | 974-980 | **★ The exhaustive frame set is equivariant** — `univ.image (σ·) = univ` (left-multiplication by `σ` is a bijection of `Perm`). The simplest concrete `FramesEquivariant` witness. | — |
| `RigidRefine.exists_isMinFrame_univ` | 982-988 | **A key-minimal frame exists over `univ`** — non-empty (`1 ∈ univ`) + ℕ-valued key ⟹ `Finset.exists_min_image` gives a minimizer. Discharges the engine's existence obligation. | — |
| `RigidRefine.keyEquivariant_compKey_skStruct_univ` | 990-1002 | **★★★ Step 9B capstone** — the mixed-native force key's `①` on the concrete `hsAdj` extraction with the concrete (exhaustive) frame set, **modulo UNIQUENESS ALONE**. `FramesEquivariant` + existence discharged (`univ`); piece 2 now reduces to one rigid-regime uniqueness fact (§9C, ties = code-aut = graph-aut = trivial). | — |
| `RigidRefine.RigidFrameUnique` | 1018-1025 | **The rigid-regime frame-uniqueness predicate** — distinct column orders give distinct canonical framed RREFs. On a rigid input: two orders with the same framed RREF differ by a coordinate-permutation automorphism of the recovered code = (faithfulness) a graph colour-auto = (rigidity) the identity. **= piece-2 uniqueness AND piece-3's kernel characterization, the SAME faithfulness fact.** Carried; 9C-2 proves it from `IsRigidF2` + the faithfulness bridge. | Definition |
| `RigidRefine.eq_of_isMinFrame_hsAdj` | 1027-1038 | **★ `huniq` from `RigidFrameUnique`** — two key-minimal frames tie on the key ⟹ (injective `f`) tie on the framed RREF ⟹ (`RigidFrameUnique`) equal. Rigid-regime min-uniqueness reduced to the single faithfulness predicate. | — |
| `RigidRefine.keyEquivariant_compKey_skStruct_rigid` | 1040-1052 | **★★★ Step 9C-1 capstone** — with the concrete injective `Encodable.encode` (no `f`-injectivity carried), the whole rigid-linear `①` for the mixed-native force key over `hsAdj` rests on exactly ONE carried predicate `RigidFrameUnique` (= the rigid-regime faithfulness that 9C-2 also turns into the ② kernel predicate). | — |
| `RigidRefine.frameSysBy_eq_transport` | 1070-1080 | **9C-2 linear algebra** — framing `H` by `o` = framing the `(o'·o⁻¹)`-transported `H` by `o'` (from `frameRowBy_transport`). The geometric identity relating two column orders of one system. | — |
| `RigidRefine.spans_pivInv_iff` | 1082-1089 | The reduced-echelon rows span the same space as the input rows, both ways (`PivInv.spanned`/`covers`). | — |
| `RigidRefine.spans_eq_of_rrefCanon_eq` | 1091-1098 | **★ Converse of `rrefCanon_eq_of_span_eq`** — equal canonical RREF ⟹ equal row space (`rrefCanon` determines the subspace). | — |
| `RigidRefine.FramedCodeSym` | 1100-1102 | π is a symmetry of the `o`-framed recovered code: transporting the system by π leaves the framed row space fixed. | Definition |
| `RigidRefine.framedCodeSym_of_rrefCanon_eq` | 1104-1112 | **★★ 9C-2 PROVABLE half** — equal framed RREF ⟹ the connecting perm `o'·o⁻¹` is a framed-code symmetry (no faithfulness used). | — |
| `RigidRefine.CodeFaithful` | 1114-1119 | **CARRIED — faithfulness (the wall gap):** a framed-code symmetry IS a graph colour-automorphism = `ForcingModel.bridge`/L4, per-family resolvable (CFI/multipede, C#-tested); its failure = the non-linear residue = the wall. | Definition |
| `RigidRefine.rigidFrameUnique_of_codeFaithful` | 1121-1130 | **★★ 9C-2 assembly** — `RigidFrameUnique` from `CodeFaithful` + graph rigidity (equal RREF ⟹ code-sym ⟹ graph-auto ⟹ id ⟹ `o=o'`). | — |
| `RigidRefine.keyEquivariant_compKey_skStruct_faithful` | 1132-1144 | **★★★ 9C-2 capstone (the ANCHOR path)** — the pure-rigid `①` closed modulo {`CodeFaithful`, graph-rigidity}. ⚠ Whole-node-rigid (single `ord`); the `ker=0` anchor, superseded by §9D `readAgg` for the mixed residue. | — |
| `RigidRefine.structReadAt` | 1164-1167 | The per-frame structural read of vertex `v` under a fixed column order `o` (the building block for the aggregate). | Definition |
| `RigidRefine.structReadAt_hsAdj_transport` | 1169-1179 | The per-frame read transports (`hsAdj`): reading `σv` under frame `σ·o` on the relabelled node = reading `v` under `o` on the original. | — |
| `RigidRefine.readAgg` | 1181-1186 | **★ The MIXED-NATIVE reader** — the sorted set of per-frame reads of `v` over the equivariant frame set, encoded. No frame is chosen ⟹ no uniqueness/rigidity. Parameterized by the frame set (poly-ready). | Definition, `noncomputable` |
| `RigidRefine.readEquivariant_readAgg` | 1188-1204 | **★★★ `ReadEquivariant (readAgg frames)` UNCONDITIONALLY** — from `FramesEquivariant` ALONE (frame set transports ⟹ image Finset invariant), NO uniqueness/rigidity. The route around whole-node rigidity: `①` holds on EVERY input, mixed included. | — |
| `RigidRefine.keyEquivariant_compKey_readAgg` | 1206-1213 | **★★★ 9D `①` capstone (general, MIXED-NATIVE)** — `compKey (skRead (readAgg frames))`'s `KeyEquivariant` from `FramesEquivariant` alone, no rigidity, any equivariant frame set. | — |
| `RigidRefine.nodeResolved_compKey_readAgg` | 1215-1225 | **★★★ 9D `②`/firing capstone** — `NodeResolved` from the per-pair `ReadSeparatesRigid (readAgg frames)` + exposed-pair rigidity (no global discreteness, no whole-node rigidity). | — |
| `RigidRefine.keyEquivariant_compKey_readAgg_univ` | 1227-1233 | **★★★ 9D concrete** — the mixed-native `①` closed with **ZERO carried hypotheses** over `framesUniv` (exponential-but-correct; poly frame set drops in unchanged). Contrast the rigid-anchor `keyEquivariant_compKey_skStruct_faithful`. | — |
| `RigidRefine.aggSet` | 1250-1253 | The set of per-frame signatures of vertex `v` (the semantic content of `readAgg` before sort/encode). | Definition, `noncomputable` |
| `RigidRefine.readAgg_eq_encode_sort` | 1255-1258 | `readAgg` is `encode` of the sorted `aggSet` (definitional). | — |
| `RigidRefine.aggSet_eq_of_readAgg_eq` | 1260-1269 | **`readAgg` distinguishes vertices exactly when their signature SETS differ** — `encode ∘ sort` is injective on `Finset ℕ` (`encode` injective + `sort_toFinset`). | — |
| `RigidRefine.readAgg_eq_of_aut` | 1271-1280 | **★ Gauge pairs TIE (correctness).** An automorphic pair (`σ` colour-aut, `σu=w`) gets EQUAL `readAgg`, from `ReadEquivariant` at `σ`. The aggregate reader separates ONLY genuine decisions — no over-separation of gauge/orbit pairs. | — |
| `RigidRefine.AggFaithful` | 1282-1289 | **CARRIED — aggregate faithfulness (the wall, MIXED-NATIVE form):** equal signature sets ⟹ **automorphic** (`∃ colour-aut σ, σu=w`), NOT identity (the 9C-2 form). Admitting non-trivial `σ` is what lets the mixed residue's gauge coexist with rigid decisions. Per-family resolvable; failure = the non-linear residue. | Definition |
| `RigidRefine.readSeparatesRigid_readAgg` | 1291-1299 | **★★ `ReadSeparatesRigid (readAgg)` from `AggFaithful`** — a non-automorphic, non-discretizing, co-cellular pair separates: equal `readAgg` ⟹ equal signature sets ⟹ (`AggFaithful`) automorphic, contradicting non-automorphy. No node/cell rigidity. | — |
| `RigidRefine.nodeResolved_compKey_readAgg_faithful` | 1301-1314 | **★★★ Step 9D-② capstone — MIXED-NATIVE firing from `AggFaithful` alone.** With `keyEquivariant_compKey_readAgg` (`①`, zero carried), the whole rigid-linear seal for the mixed reader rests on exactly `{FramesEquivariant, AggFaithful}` — frame-set transport (structural) + aggregate faithfulness (the shared wall). | — |
| `RigidRefine.FramesEquivariantB` | 1341-1346 | The base-frame set transports via the base-frame action `act` (not free left-mult on `Perm`) — for a base-quotient `B`, `act σ` is trivial on gauge `σ`, dodging the free-action `≥2^β` bound. | Definition |
| `RigidRefine.ReadAtEquivariant` | 1348-1353 | Each per-frame read is a vertex-invariant (`baseRead (act σ b)(relabel σ)(transport χ)(σ v) = baseRead b adj χ v`) — the base-quotient analog of `structReadAt_hsAdj_transport`. | Definition |
| `RigidRefine.readAggB` | 1355-1360 | **The de-classed aggregate reader** — sorted, encoded SET of a vertex's per-frame reads over the base-frame set (`B`, not full orders). | Definition, `noncomputable` |
| `RigidRefine.readEquivariant_readAggB` | 1362-1377 | **★★★ `ReadEquivariant (readAggB …)` UNCONDITIONALLY** from `FramesEquivariantB` + `ReadAtEquivariant` alone (no rigidity) — the frame set + each read transport ⟹ image `Finset` invariant. The `①` of the de-classed reader, poly frame set included. | — |
| `RigidRefine.keyEquivariant_compKey_readAggB` | 1379-1386 | **★★★ `①` capstone (de-classed)** — `compKey (skRead (readAggB …))`'s `KeyEquivariant` from the base-frame equivariance alone. | — |
| `RigidRefine.aggSetB` | 1390-1396 | The set of per-frame reads of `v` — the semantic content of `readAggB` before sort/encode. | Definition, `noncomputable` |
| `RigidRefine.readAggB_eq_encode_sort` | 1397-1403 | `readAggB = encode (aggSetB.sort)` (definitional). | — |
| `RigidRefine.aggSetB_eq_of_readAggB_eq` | 1404-1413 | `readAggB` distinguishes vertices exactly when their per-frame read SETS differ (`encode ∘ sort` injective). | — |
| `RigidRefine.readAggB_eq_of_aut` | 1415-1425 | **★ Gauge pairs TIE** (correctness) — an automorphic pair gets EQUAL `readAggB`, from `ReadEquivariant` at `σ`. Leaves gauge/orbit pairs to consume. | — |
| `RigidRefine.AggFaithfulB` | 1427-1437 | **CARRIED — base-quotient aggregate faithfulness (the wall, mixed-native):** co-cellular vertices with the same per-frame read SET are AUTOMORPHIC. Per-family resolvable (P3); failure = non-linear residue. | Definition |
| `RigidRefine.readSeparatesRigid_readAggB` | 1438-1448 | **★★ `ReadSeparatesRigid (readAggB …)` from `AggFaithfulB`** — a non-automorphic, non-discretizing, co-cellular pair gets distinct `readAggB`. No node/cell rigidity. | — |
| `RigidRefine.nodeResolved_compKey_readAggB_faithful` | 1449-1460 | **★★★ `②`/firing capstone (de-classed, mixed-native)** — `NodeResolved` from `AggFaithfulB` + exposed pairs non-automorphic. Whole de-classed seal = `{FramesEquivariantB, ReadAtEquivariant, AggFaithfulB}`. | — |
| `RigidRefine.framesEquivariantB_singleton` | 1462-1468 | **★ Singleton frame families are `FramesEquivariantB`** when `act` fixes the base point — the concrete escape from the free-action `2^β` bound (`|frames|=1`, poly). | — |
| `RigidRefine.pinAct` | 1478-1481 | The pinning action `p ↦ p.image (transportVec σ)` — fixes `∅` (and gauge-recovered base pinnings), so NON-free ⟹ a poly `FramesEquivariantB` set exists. | Definition |
| `RigidRefine.baseReadPin` | 1483-1488 | The base-pinned forced read — vertex `v`'s forced value under (extracted system ∪ pinning `p`), encoded. Reuses `forcedVal` — ORDER-FREE, no `rrefCanon` in the `①` handle. | Definition, `noncomputable` |
| `RigidRefine.readAtEquivariant_baseReadPin` | 1490-1498 | **★★ The pinned read is a vertex-invariant** — `ReadAtEquivariant (baseReadPin extract) pinAct ⟸ RefExtractEquivariant`, via `forcedVal_transport` + `image_union`. | — |
| `RigidRefine.keyEquivariant_compKey_readAggB_pin` | 1500-1511 | **★★★ The concrete de-classed `①`, POLY (singleton pinning family), ZERO carried beyond the extraction** — the base-quotient analog of `readAgg_univ` but `|frames|=1` not `n!`. The TYPE ESCAPE realized (richness = bigger pinning family = P2). | — |
## ChainDescent/DeepenCertified.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.CertifiedOrbit` | 65-72 | — | Definition |
| `Deepen.cellSingleOrbit_of_certifiedOrbit` | 74-80 | — | — |
| `Deepen.certifiedOrbit_of_cellIsOrbit` | 82-89 | — | — |
| `Deepen.CertifiedPath` | 93-107 | — | Definition |
| `Deepen.tinhoferPath_of_certifiedPath` | 109-135 | — | — |
| `Deepen.Certified` | 137-139 | — | Definition |
| `Deepen.tinhofer_of_certified` | 141-145 | — | — |
| `Deepen.deepenSupply_guarded_canonizer_of_certified` | 147-157 | — | — |
| `Deepen.classOf_eq_cidCell` | 171-172 | — | — |
| `Deepen.cidCell_length_eq_cellOf_card` | 174-180 | — | — |
| `Deepen.mem_nonSingletonColours_iff` | 228-242 | — | — |
| `Deepen.chooseIdK_eq_targetColour` | 244-298 | — | — |
| `Deepen.certifiedOrbit_of_cellIsOrbit_chooseIdK` | 300-308 | — | — |
| `Deepen.branchOrbit_iff_aut_of_certified` | 317-324 | — | — |
| `Deepen.consume_fail_gives_real_decision` | 326-338 | — | — |
| `Deepen.rigidObstructionAt_branch_of_certified` | 340-349 | — | — |
| `Deepen.relabelAdj_mul` | 363-365 | — | — |
| `Deepen.cellSingleOrbit_transport_iso` | 367-379 | — | — |
| `Deepen.chooseIdK_finRange_transport` | 381-386 | — | — |
| `Deepen.tinhoferPath_transport` | 388-462 | — | — |
| `Deepen.tinhofer_transport` | 464-477 | — | — |
| `Deepen.relabelAdj_one` | 486 | — | — |
| `Deepen.transportColouring_one` | 488-489 | — | — |
| `Deepen.tinhofer_transport_iff` | 491-497 | — | — |
| `Deepen.wordReach_nil_iff` | 499-505 | — | — |
| `Deepen.deepenSupplyGuarded` | 506-512 | — | Definition, `noncomputable` |
| `Deepen.verified_guarded_of_tinhofer` | 514-517 | — | — |
| `Deepen.verified_guarded_of_not` | 519-522 | — | — |
| `Deepen.deepen_branchOrbit_transport_guarded` | 524-553 | — | — |
| `Deepen.deepenSupplyGuarded_canonizer` | 555-567 | — | — |

## ChainDescent/DeepenExact.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.warmRefineR_lt` | 54-61 | B0 Warm refinement produces RANKS, so every colour is `< n`. | — |
| `Deepen.step_col_lt` | 63-65 | B0 One step's colours are `< n`. | — |
| `Deepen.leafOf_lt` | 67-85 | B0 The leaf's colours are `< n`. | — |
| `Deepen.leafOf_discrete` | 87-117 | B0 The greedy leaf is DISCRETE once the fuel covers the colour deficit — same `Descend.ncol` measure as `deepen_succeeds`. | — |
| `Deepen.leafOf_discrete_n` | 119-121 | B0 At fuel `n` the greedy leaf is discrete. This is what makes the read COMPLETE. | — |
| `Deepen.filter_eq_singleton_of_discrete` | 125-131 | B0a A discrete colouring's class is a singleton. | — |
| `Deepen.readAt_discrete` | 133-137 | B0a At a discrete colouring the adjacency read is a single entry. | — |
| `Deepen.readColAt_discrete` | 139-142 | B0a At a discrete colouring the parent read is a single value. | — |
| `Deepen.readKey_components` | 146-155 | B0b Key equality gives componentwise equality (`readKey` is two `map`s). | — |
| `Deepen.colEquiv` | 164-169 | B1a A discrete colouring with colours `< n` is a permutation. | Definition, `noncomputable` |
| `Deepen.colEquiv_val` | 171-172 | B1a Its value is the colour. | — |
| `Deepen.matchPerm` | 174-177 | B1a The permutation matching two discrete colourings colour-for-colour. | Definition, `noncomputable` |
| `Deepen.matchPerm_col` | 179-186 | B1a `matchPerm` matches the colours. | — |
| `Deepen.isColAut_of_readKey_eq` | 188-251 | ★★ B1 THE COMPLETENESS DIRECTION, UNCONDITIONAL. Two discrete leaves with equal reads are related by a colour-automorphism carrying `u` to `w`. No `Tinhofer`: this is completeness of the ENCODING. The odd values of `indivOne χ u` sit exactly at `u`, which is what forces `ρ u = w`; halving gives `χ ∘ ρ = χ`. This is the FIRING direction, and it needs no guard. | — |
| `Deepen.tinhoferPath_of_tinhofer` | 259-261 | The guard is open at every branch rep of an `Tinhofer` node. | — |
| `Deepen.orbKey_ne_of_no_aut` | 263-278 | B3 `orbKey` SEPARATES any pair no colour-automorphism links. | — |
| `Deepen.forceBy_orbKey_narrows` | 280-294 | ★★★ B3a At an `Tinhofer` node with a `RigidObstructionAt`, `forceBy orbKey` STRICTLY NARROWS. No contradiction with `forceBy_no_narrowing_on_orbit`: the obstruction is precisely the statement that the cell is NOT a single orbit. | — |
| `Deepen.orbKey_eq_iff_orbit` | 296-313 | ★★★ B2 At an `Tinhofer` node `orbKey`'s FIBRES ARE THE ORBITS, both directions. `⟸` is the ceiling (`Force.keyV_aut_invariant`, free from `keyEquivariant_orbKey`), so the key is constant on each orbit and force can never cut INSIDE one — this is also the consistency check against `forceBy_no_narrowing_on_orbit`. | — |
| `Deepen.forcedSet_single_orbit` | 315-327 | ★★★ D2 Force narrows the branch cell to a SINGLE ORBIT — the exact input `Composite.forceThenConsume_singleton_of_cellIsOrbit` wants. | — |
| `Deepen.exists_targetColour` | 329-335 | Every non-discrete colouring has a branch colour. | — |
| `Deepen.consume_fail_force_fires` | 337-356 | ★★★ D1 THE HOOK, CLOSED. A CONSUME FAILURE MAKES FORCE FIRE at a descent-reachable node. Strongest available form: a measured witness (CFI over a random cubic base, m=8) has consume failing at a node whose branch cell is a SINGLE ORBIT, where `forceBy_no_narrowing_on_orbit` forbids force from firing — so relocating to a reachable node is the target, not a weakening. | — |

## ChainDescent/DeepenGuard.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.wordReach_isColAut` | 69-78 | `WordReach` over any list of verified automorphisms yields an automorphism — `DeepenTinhofer`'s version is `deepenSupply`-specific; this is the general one. | — |
| `Deepen.wordReach_isColAut_verified` | 80-83 | The same for a supply's `verified` list. | — |
| `Deepen.cellSingleOrbit_of_cellIsOrbit` | 85-92 | SOUND `CellIsOrbit S` for ANY supply gives the branch cell's `CellSingleOrbit` — `DeepenCertified`'s T1 with `deepenSupply` generalised away. | — |
| `Deepen.wordReach_transport` | 99-111 | `WordReach` transports under `SupplyEquivariant S`. | — |
| `Deepen.cellIsOrbit_transport` | 113-120 | ★ The lemma the poly-guard design was missing: `CellIsOrbit S` transports when `S` does. | — |
| `Deepen.CertPath` | 129-138 | The POLY guard: at every level, `S`'s verified generators act transitively on the cell the level individualizes. `TinhoferPath`'s recursion with the OBSERVABLE `CellIsOrbit S` in place of the unobservable `CellSingleOrbit`. | Definition |
| `Deepen.CertifiedG` | 140-142 | Every anchor's path is certified — the poly analogue of `Tinhofer`. | Definition |
| `Deepen.tinhoferPath_of_certPath` | 144-169 | ★★ SOUND: the poly guard implies the real one. | — |
| `Deepen.tinhofer_of_certifiedG` | 171-173 | ★★ `CertifiedG S ⟹ Tinhofer`. | — |
| `Deepen.certPath_transport` | 181-254 | ★★ INVARIANT: the poly guard transports, given `SupplyEquivariant S`. Same pick-absorption induction as `tinhoferPath_transport`, with soundness supplying the stabiliser element. | — |
| `Deepen.certPath_step_transport_iff` | 256-271 | The poly guard at a vertex, both directions. | — |
| `Deepen.certPath_none` | 279-282 | `CertPath` equation lemma (no cell chosen). Reduce `CertPath` ONLY through these — unfolding in place then `cases`-ing on `chooseIdK` descends into its internal `foldl` (the recorded `deepen` match-reduction trap). | — |
| `Deepen.certPath_nil` | 284-288 | `CertPath` equation lemma (chosen cell empty). | — |
| `Deepen.certPath_cons` | 290-296 | `CertPath` equation lemma (chosen cell non-empty) — the recursive case that feeds the decidability instance. | — |
| `Deepen.instDecidableCertPath` | 298-319 | ★★ `CertPath` IS DECIDABLE — structural recursion on the fuel, each level one `Consume.decidableCellIsOrbit` test (the orbit BFS), no search over `Equiv.Perm (Fin n)`. This REPLACED the `Classical.dec` placeholder and is what makes `orbKeyG` computable. ⚠ `orbKey` is not repairable this way: its `TinhoferPath` guard is the automorphism-partition problem (GI-complete). | Instance |
| `Deepen.stepCost` | 329-338 | ★ **The `step` bill** — one warm refinement, `n³` | Definition. Closed a real hole 2026-08-06: `certPathCost` billed **nothing** for the `step` its own recursion performs ⟹ `costConst` 53 → 57 |
| `Deepen.certPathCost` | 340-349 | The guard's OWN cost, billed along its own recursion: per level one `CellIsOrbit` reachability test plus **one call to `S`**, at the colouring that level actually visits. The key previously declared a flat `n⁴` that priced the read and nothing of the guard. | Definition |
| `Deepen.certPathCost_le` | 351-383 | The guard costs `fuel` levels of (reachability + one supply call), parametric in the supply's own bound `c₂` — the `SupplyCost` pattern, so a real bound rather than a restatement of a declared constant. | — |
| `Deepen.orbKeyG` | 387-394 | ★★★ THE POLY-GUARDED KEY. Identical to `orbKey` except the `if` tests the OBSERVABLE `CertPath S`. | Definition |
| `Deepen.keyV_orbKeyG` | 396-400 | The guarded key's value projection, unfolded. | `@[simp]` |
| `Deepen.keyCost_orbKeyG_le` | 402-410 | ★★ THE KEY'S BILL: `keyCost (orbKeyG S) ≤ n⁴ + n·(n⁴ + c₂)`. Parametric in the supply's cost bound, so an exponential `supplyCost` now yields an exponential `keyCost` — `②` at this key is falsifiable, which the flat constant could not express. | — |
| `Deepen.keyEquivariant_orbKeyG` | 412-427 | ★★★ `①` FOR THE POLY-GUARDED KEY, from `SupplyEquivariant S` alone. ⚠ Note `CertPath S ⟹ TinhoferPath` and never the converse, so `orbKeyG S` DEFERS more often than `orbKey` — a firing loss, not a soundness loss. | — |
| `Deepen.orbKeyG_ne_of_no_aut` | 434-447 | The guarded key separates a non-automorphic pair (`isColAut_of_readKey_eq` is guard-agnostic, so this transferred verbatim). | — |
| `Deepen.forceBy_orbKeyG_narrows` | 449-460 | ★★★ FORCE FIRES UNDER THE POLY GUARD. Same as `forceBy_orbKey_narrows` with `CertifiedG S` (poly, observable) in place of `Tinhofer` (an `n!` search). | — |
| `Deepen.consume_fail_force_fires_guarded` | 462-479 | ★★ The poly-guarded hook. The LOCALIZATION half is unchanged (it never depended on a guard); what the poly guard costs is that FIRING needs the guard open, hence `CertifiedG S ψ` as a hypothesis. The unconditional statement stays `consume_fail_force_fires`, over `orbKey`. | — |
| `Deepen.orbKeyG_eq_orbKey_of_certPath` | 481-486 | Wherever the poly guard is open the two keys are EQUAL — `orbKeyG S` is a restriction of `orbKey`, not a different function. | — |
| `Deepen.keyEquivariant_orbKeyG_deck2` | 494-496 | Non-vacuity: the parametric design instantiated at `deck2Supply`. | — |
| `Deepen.keyEquivariant_orbKeyG_deck` | 498-500 | Non-vacuity: instantiated at `deckSupply`. | — |
| `Deepen.force_canonizer_orbKeyG_deck2` | 502-512 | ★★★ THE POLY-GUARDED FORCE CANONIZER — `①a`/`①b`/`①c` plus totality for the `deck2`-guarded key, with NO hypothesis at all. | — |

| `Deepen.mem_verified_appendSupply_left` | 537-541 | A verified generator of `S₁` is a verified generator of `S₁ ++ S₂`. | — |
| `Deepen.mem_verified_appendSupply_right` | 543-547 | A verified generator of `S₂` is a verified generator of `S₁ ++ S₂`. | — |
| `Deepen.cellIsOrbit_append_left` | 549-551 | `CellIsOrbit` grows under `appendSupply` (left). | — |
| `Deepen.cellIsOrbit_append_right` | 553-555 | `CellIsOrbit` grows under `appendSupply` (right). | — |
| `Deepen.certPath_append_left` | 557-576 | ★ THE GUARD ONLY GROWS: anything `S₁` certifies, `S₁ ++ S₂` certifies. Proved through the §5 equation lemmas, never by unfolding `CertPath` in place. ⚠ Monotonicity, NOT strictness — that the union is *strictly* stronger is measured (`PerformanceTest` §18), not proved. | — |
| `Deepen.certPath_append_right` | 578-595 | The same, from the right summand. | — |
| `Deepen.certifiedG_append_left` | 597-599 | `CertifiedG` grows under `appendSupply` (left) — the node-level form. | — |
| `Deepen.certifiedG_append_right` | 601-603 | `CertifiedG` grows under `appendSupply` (right). | — |
| `Deepen.guardSupply` | 611-614 | ★★ THE UNION GUARD: `foldSupplyFast ++ deckSupply ++ deck2Supply ++ matchSupply`. ⚠ `kernelSupply` is deliberately EXCLUDED — it is provably not `GensEquivariant` (pivot-order-dependent basis, trap #7), so it cannot sit in a guard whose job is keeping the `if` relabelling-stable; it remains available to FIRE, which needs no invariance. | Definition |
| `Deepen.gensEquivariant_guardSupply` | 616-621 | The union is `GensEquivariant`, from the existing `Deck.gensEquivariant_appendSupply` closure. | — |
| `Deepen.supplyEquivariant_guardSupply` | 623-624 | Hence `SupplyEquivariant` — the only thing `keyEquivariant_orbKeyG` asks for. | — |
| `Deepen.keyEquivariant_orbKeyG_guard` | 626-629 | ★★★ `①` FOR THE UNION-GUARDED KEY — no hypothesis, exactly as for the single-supply guards. | — |
| `Deepen.force_canonizer_orbKeyG_guard` | 631-639 | ★★★ THE UNION-GUARDED FORCE CANONIZER — `①a`/`①b`/`①c` + totality, no hypothesis. The strongest executable force key in the record: poly guard, poly read, billed cost. | — |
| `Deepen.certifiedG_guard_of_foldFast` | 643-645 | Firing dominance: whatever `foldSupplyFast` certifies, the union certifies. | — |
| `Deepen.certifiedG_guard_of_deck` | 647-649 | Firing dominance over `deckSupply`. | — |
| `Deepen.certifiedG_guard_of_deck2` | 651-653 | Firing dominance over `deck2Supply`. | — |
| `Deepen.certifiedG_guard_of_match` | 655-657 | Firing dominance over `Consume.matchSupply`. | — |
| `Deepen.cellIsOrbit_congr` | 680-684 | §9 Orbit-equal supplies certify the same cells — `CellIsOrbit` reads its supply only through `WordReach` on `verified`, which is exactly what `SameOrbits` equates. | — |
| `Deepen.certPath_congr` | 686-705 | ★★ §9 **The guard is a function of the supply's ORBITS, not of its generators.** The path's shape (`chooseIdK`, the cell filter, `step`) never mentions `S`, so the whole recursion is congruent. Proved through the §5 equation lemmas, never by unfolding `CertPath` in place. | — |
| `Deepen.certifiedG_congr` | 707-710 | §9 The node-level form: orbit-equal supplies certify the same nodes. | — |
| `Deepen.keyV_orbKeyG_congr` | 712-718 | §9 Orbit-equal supplies give the same key VALUE. Only the cost differs (`certPathCost` calls `S` itself), which carries no `①` obligation. | — |
| `Deepen.keyEquivariant_orbKeyG_of_sameOrbits` | 720-727 | ★★★ §9 `①` FOR A NON-EQUIVARIANT GUARD SUPPLY — the `SameOrbits` reduction at the key, mirroring `OrbitPrune`'s at the resolver. ⚠⚠ The generic half only: the sole supply worth admitting this way is `deepenSupply`, and `SameOrbits deepenSupply Ref` IS **R1**, the crux the parked `DeepenRef`/`DeepenR1` apparatus was built for. The lever is not independent of that retired route. | — |
## ChainDescent/DeepenKey.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.Refines` | 64-65 | A colouring at least as fine as another (same fine colour ⟹ same coarse colour). | Definition |
| `Deepen.Refines.trans` | 67-68 | `Refines` is transitive. | — |
| `Deepen.step_col_eq` | 70-75 | `(step adj χ v).col` is `warmRefineR` of `indivOne χ v`. | — |
| `Deepen.refines_step` | 77-82 | The warm-refined individualization refines what it was applied to (from `refineSplits_encodeFreeFast`). | — |
| `Deepen.refines_indivOne` | 84-93 | Individualization refines the colouring it splits. | — |
| `Deepen.refines_transport` | 95-99 | `Refines` transports. | — |
| `Deepen.transport_eq_of_isColAut_refines` | 101-110 | ★ A colour-automorphism of a FINE colouring fixes every COARSER one. This is what carries the parent colouring through the accumulated isomorphism in `leafOf_transport_of_tinhoferPath` — without it the key can only compare UNCOLOURED individualized graphs, which is not enough for 'same orbit'. | — |
| `Deepen.leafOf` | 118-127 | The state deepen's greedy path reaches from `cur` in ≤ `fuel` levels. Mirrors `TinhoferPath`'s recursion exactly so the two line up level for level. | Definition |
| `Deepen.leafOf_zero` | 135 | ⚠ Reduce `leafOf` ONLY through these three equation lemmas — unfolding then `cases`-ing on `chooseIdK` descends into its internal `foldl` (the recorded `deepen` match-reduction trap). | — |
| `Deepen.leafOf_succ_none` | 137-139 | Equation lemma: the descent stops when `chooseIdK` returns `none`. | — |
| `Deepen.leafOf_succ_nil` | 141-145 | Equation lemma: the (impossible) empty-cell case. | — |
| `Deepen.leafOf_succ_cons` | 147-152 | Equation lemma: one level, picking the lowest-index member. | — |
| `Deepen.leafOf_transport_of_tinhoferPath` | 160-255 | ★★ A2, the technical core. Under `TinhoferPath` the two LEAVES are related by an accumulated isomorphism `ρ`, and `ρ` acts on any colouring the state refines exactly as `σ` does. This is `tinhoferPath_transport` with its accumulator `τ * σ` KEPT rather than discarded. | — |
| `Deepen.filter_col_transport` | 263-275 | A1 Colour classes transport by `σ`. | — |
| `Deepen.readAt` | 277-280 | Total adjacency between the `c`-class and the `d`-class. | Definition |
| `Deepen.readColAt` | 282-284 | Total parent colour over the `c`-class. | Definition |
| `Deepen.readAt_transport` | 286-294 | A1 The adjacency read transports. | — |
| `Deepen.readColAt_transport` | 296-302 | A1 The parent-colour read transports. | — |
| `Deepen.readAtIdx` | 304-309 | The adjacency read at a FLATTENED index `k = c * n + d`. Flattening (not a nested `flatMap`) is deliberate: it makes `readKey` two plain `List.map`s, so `List.append_inj` + `List.map_inj_left` recover the components — what `readKey_components` needs. | Definition |
| `Deepen.readKey` | 311-315 | The invariant read: adjacency between every ordered pair of colour classes, then the parent colour of every class. At a DISCRETE colouring each class is a singleton, so this is the full relabelled adjacency plus the relabelled parent colouring — the object the probes call `cert`. | Definition |
| `Deepen.readAtIdx_transport` | 317-320 | A1 The flattened adjacency read transports. | — |
| `Deepen.readKey_transport` | 322-328 | A1 The whole read transports. | — |
| `Deepen.tinhoferPath_step_transport_iff` | 332-348 | A3 The guard is relabelling-invariant, both directions (forward `tinhoferPath_transport` at σ, backward at σ⁻¹). | — |
| `Deepen.instDecidableTinhoferPath` | 352-359 | `Tinhofer` IS decidable (`IsColAut` has an instance, `Equiv.Perm (Fin n)` is a `Fintype`) — but by an `n!` search, so this registers `Classical.dec` rather than pretend that is a cost model. One instance so `orbKey` and `keyV_orbKey` share the term and the projection is `rfl`. | Instance, `noncomputable` |
| `Deepen.orbKey` | 361-370 | ★★★ THE KEY. deepen's greedy descent from `v` run to its leaf and read invariantly, GUARDED by `TinhoferPath` — which is exactly the condition making that index-picked descent labelling-independent. Off the guard the key is constant, so force simply does not act. | Definition, `noncomputable` |
| `Deepen.keyV_orbKey` | 372-376 | The key's value projection, unfolded. | `@[simp]` |
| `Deepen.keyEquivariant_orbKey` | 378-396 | ★★★ A4 `①` FOR THE FORCE ROUTE, NO HYPOTHESIS. The guard transports (`tinhoferPath_step_transport_iff`) and the value transports along the isomorphism `leafOf_transport_of_tinhoferPath` supplies. `KeyEquivariant` is force's SOLE `①` obligation, so `Force.force_canonizer` / `Composite.composite_canonizer` apply with nothing left to discharge. | — |

## ChainDescent/DeepenLocated.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.DescentReach` | 60-66 | C1 Reachable by PROPER descent steps (individualize a vertex with a same-colour partner, then warm-refine). The partner clause is load-bearing: it makes every step strictly raise `ncol`. | Inductive |
| `Deepen.DescentReach.trans` | 68-72 | C1 `DescentReach` composes. | — |
| `Deepen.ncol_lt_step_of_partner` | 74-86 | C1a One proper descent step strictly raises the colour count — the termination measure `deepen_succeeds` uses, isolated for reuse. | — |
| `Deepen.ncol_le_of_descentReach` | 88-93 | C1a Reachability never lowers the colour count. | — |
| `Deepen.partner_of_chooseIdK` | 95-117 | C1b A `chooseIdK` level's pick has a same-colour partner (its cell has ≥ 2 members). | — |
| `Deepen.not_tinhoferPath_located` | 125-163 | ★★ C2/L2 A non-`TinhoferPath` state exposes a rigid obstruction at the BRANCH CELL of a REACHABLE colouring. Strengthens `not_tinhoferPath_imp_rigidObstruction`, whose `∃ χc cid` names no reachable node and no branch cell — force fires at a node, so it cannot act on the weaker form. | — |
| `Deepen.not_tinhofer_deepest_aux` | 173-209 | C3 Fuelled form of `not_tinhofer_deepest`; `k` bounds the remaining colour deficit `n - ncol χ`. | — |
| `Deepen.not_tinhofer_deepest` | 211-227 | ★★★ C3/L3 THE HOOK POINT. `¬Tinhofer adj χ` ⟹ the descent reaches `ψ` that is SIMULTANEOUSLY `Tinhofer` (consume exact below, which an orbit-separating equivariant key needs) and carries a `RigidObstructionAt` at its own branch cell (so force's ceiling does not block firing). Non-vacuity measured: 100 inhabitants over 7 families. | — |
| `Deepen.consume_fail_real_decision_of_tinhofer` | 229-240 | The `Tinhofer` form of `consume_fail_gives_real_decision`; `DeepenCertified` states it over the strictly stronger `Certified`, but `deepen_branch_orbit_iff_aut` already takes `Tinhofer`. | — |
| `Deepen.rigidObstructionAt_branch_of_tinhofer` | 242-248 | The `Tinhofer` form of `rigidObstructionAt_branch_of_certified`. | — |
| `Deepen.consume_fail_locates` | 250-263 | ★★★ Every consume failure is LOCATED: either a rigid decision in THIS branch cell (node `Tinhofer`), or one at a reachable node carrying both hypotheses. Neither disjunct is an unanchored existential. | — |
## ChainDescent/KeyComplete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `KeyComplete.KeySeparatesAt` | 90-95 | At this node the force key separates every branch pair that no colour-automorphism links. Contrapositive: equal keys inside the branch cell ⟹ same orbit. | Definition |
| `KeyComplete.KeySeparatesAll` | 97-104 | The global form — the carried obligation. ⚠ Named `…All`, not `KeySeparates`: F3a's earlier `Hol.KeySeparates` (`HolKey.lean` §1) owns that identifier for the PER-NODE predicate. | Definition |
| `KeyComplete.keySeparatesAt_iff_hol` | 126-134 | ★ §1a THE BRIDGE — `KeySeparatesAt` is `Hol.KeySeparates` written contrapositively. Makes the F3a duplication visible: `forcedSet_single_orbit_of_keySeparatesAt` re-proves `Hol.keepMin_pairwise_aut_of_separates` (`Composite.forcedSet` IS `keepMin … (branches χ)`). What is NOT duplicated is `ForcePick.forceThenPick` — F3a routes its conclusion back through consume, i.e. through a COMPUTED certificate. | — |
| `KeyComplete.forcedSet_single_orbit_of_keySeparatesAt` | 142-156 | ★★★ THE EXHAUSTIVENESS COROLLARY — under `KeySeparatesAt` the key's argmin over the branch cell is a single `IsColAut`-orbit, so discarding all but one survivor is sound WITHOUT a certificate. Uses no property of the key beyond the hypothesis: no equivariance, no guard, no supply. | — |
| `KeyComplete.forceThenConsume_singleton_of_forcedWordReach` | 158-169 | The composite's firing lemma generalized from `CellIsOrbit` (about the WHOLE cell — false at a mixed node) to pairwise `WordReach` on the FORCED SET. The brick `Composite.forceThenConsume_singleton_of_cellIsOrbit` was missing. | — |
| `KeyComplete.keySeparatesAt_orbKey_of_tinhofer` | 177-180 | Non-vacuity: `orbKey` separates every non-automorphic branch pair at an `Tinhofer` node. ⚠ Carries the guard — off it `orbKey` is constant, so this is NOT the global `KeySeparates`. | — |
| `KeyComplete.keySeparatesAt_orbKeyG_of_certifiedG` | 182-185 | Non-vacuity for the poly-guarded key, on its own guard (`CertifiedG S`). | — |
| `KeyComplete.forceThenConsume_singleton_of_tinhofer` | 194-202 | ★★★ THE MIXED FIRING THEOREM — at an `Tinhofer` node the composite narrows the branch cell to EXACTLY ONE branch. Force half = the corollary above; consume half = `Deepen.deepen_branch_orbit_iff_aut` (landed 2026-07-23). NOT reachable via `Cost.CellResolved`: at a mixed node neither of its disjuncts holds. | — |
| `KeyComplete.nodeResolved_of_tinhofer` | 204-214 | ★★ `Select.NodeResolved` at every `Tinhofer` node — the predicate `②`/`③` actually consume. `Deepen.consume_fail_force_fires` gives only STRICT narrowing, which nothing downstream reads; this gives `≤ 1`. | — |
| `KeyComplete.rawKey` | 237-242 | The UNGUARDED read (`orbKey` with the `if` removed). NOT `KeyEquivariant` — `leafOf` breaks ties by vertex index — so unusable as a force key; it exists to make the `KeySeparates` / `KeyEquivariant` decomposition a theorem. | Definition |
| `KeyComplete.keyV_rawKey` | 244-247 | Value projection of `rawKey` (`rfl`). | `@[simp]` |
| `KeyComplete.keySeparatesAll_rawKey` | 249-261 | ★★ `KeySeparatesAll` HOLDS GLOBALLY for the raw read at `n⁴`, no hypothesis — from the unconditional `isColAut_of_readKey_eq`. ⟹ separation alone is CHEAP and is NOT the wall; the GI-hard object is `KeySeparatesAll ∧ KeyEquivariant`, and the guard on `orbKey`/`orbKeyG` purchases EQUIVARIANCE, not separation. | — |
| `KeyComplete.forcedSet_single_orbit_rawKey` | 263-269 | The exhaustiveness corollary at a key that satisfies its hypothesis unconditionally: `rawKey`'s forced set is a single `IsColAut`-orbit. | — |
| `KeyComplete.step_col_eq_refineV` | 279-282 | `Deepen.step` IS `refineV encodeFreeFast ∘ indivOne` — the identification the `Reaches` bridge needs. | — |
| `KeyComplete.reaches_of_descentReach` | 284-298 | ★ THE BRIDGE: everything `DescentReach` walks to, the descent `Reaches`. `Descend.Reaches.step` and `DescentReach.cons` carry exactly the same side condition, so this is near-definitional — but without it the node `DeepenLocated`'s relocation produces is not formally one the canonizer visits, and `HandledS` quantifies over `Reaches`. | — |
| `KeyComplete.consume_fail_locates_resolved` | 300-319 | ★★ A consume failure locates a REACHED node that the fused resolver RESOLVES, carrying a genuine rigid decision. `DeepenExact.consume_fail_force_fires` with both weaknesses removed: the node is one the canonizer visits (the bridge above) and the conclusion is `NodeResolved` (`≤ 1`), not strict narrowing — which nothing downstream consumed. | — |
| `KeyComplete.handledS_of_reached_tinhofer` | 321-329 | `Select.HandledS` on the all-`Tinhofer` reached class — the FIRST population of the sel-aware capability predicate (remaining-work §1T records zero families). Hypothesis is per-node over `Reaches`, not the global `∀ adj χ` of `deepenSupply_guarded_canonizer_direct`. | — |
## ChainDescent/ForcePick.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `ForcePick.forceThenPick` | 72-79 | ★ THE RESOLVER — force, then keep ONE survivor (`take 1`). No supply, no verification, no orbit BFS: the discarded survivors are pairwise automorphic under `KeySeparatesAt`, and that automorphism is never computed. Cost is exactly `forceBy`'s. | Definition |
| `ForcePick.narrow_forceThenPick` | 81-83 | The narrowing is the first element of the forced set (definitional). | — |
| `ForcePick.forceThenPick_cost` | 85-87 | The pick itself is free — the bill is `forceBy`'s, one key evaluation per branch (definitional). | — |
| `ForcePick.narrow_length_le_one` | 95-98 | The narrowing has at most one element, structurally (`take 1`). | — |
| `ForcePick.resolvedAll_forceThenPick` | 100-103 | ★★ `Cost.ResolvedAll` with NO hypothesis — the descent is a single path on every input. `Stall.guard` buys this by FLAGGING the nodes it cannot resolve; this buys it by RESOLVING them, at the price of `KeySeparates` on `①`. | — |
| `ForcePick.narrowProper_forceThenPick` | 111-120 | ★★ THE FLAG NEVER FIRES, with no hypothesis: force never empties a non-discrete cell (`Composite.forcedSet_ne_nil`) and `take 1` of a nonempty list is a singleton. This resolver has no stall channel, so `③`'s residue is empty for it and everything is pushed onto `①`'s `KeySeparates`. | — |
| `ForcePick.coveringOfAt_forceThenPick` | 129-166 | ★★ THE ONE NEW PROOF — the covering, from `KeySeparates` alone. Every survivor is automorphic to the picked one (`KeyComplete.forcedSet_single_orbit_of_keySeparatesAt`), hence carries the same branch value (`Consume.branchVal_eq_of_isColAut` = `descend_transport` at that automorphism), so the two mapped value lists have the same MEMBERSHIP — all `aggregate` reads. This is the third contract route (`CoveringOfAt`) at the intermediate witness no instance had used. | — |
| `ForcePick.narrowTransport_forceThenPick` | 168-174 | ★★★ THE CONTRACT, from `{KeyEquivariant, KeySeparates}`: equivariance makes the forced set an equivariant intermediate, separation makes the singleton pick cover it. | — |
| `ForcePick.forcePick_canonizer` | 178-189 | ★★★ `①` + TOTALITY. The totality half carries NO hypothesis — this object cannot flag. | — |
| `ForcePick.forcePick_canonizer_fast` | 191-199 | The runnable version (`encodeFreeFast`). | — |
| `ForcePick.forceThenPick_cost_le` | 206-217 | The per-node bill: `n` key evaluations plus `n²`, and nothing else — no supply call, no verification, no BFS. | — |
| `ForcePick.descentCost_forceThenPick_le` | 219-227 | ★★ `②` EXPLICIT, WITH NO FIRING HYPOTHESIS — the fan-out bound is structural, so the only input is a `keyCost` bound. | — |
| `ForcePick.forcePick_record` | 239-254 | ★★★ THE RECORD STATEMENT — `①a`/`①b`/`①c`, "the flag never fires", and an explicit polynomial `②`, in one theorem. Read the hypothesis list as the project's target stated once: **an equivariant, separating, poly force key is a complete polynomial canonizer.** ⚠ Nothing here claims such a key exists — `keySeparatesAll_rawKey` gives separation + poly without equivariance, `keyEquivariant_orbKey` gives equivariance without separation; the wall is having both. | — |
| `ForcePick.colOf` | 277-278 | The discrete colouring induced by a permutation, `x ↦ (π x).val`. Values `< n` by construction — exactly `isColAut_of_readKey_eq`'s hypotheses. | Definition |
| `ForcePick.colOf_discrete` | 280-281 | `colOf π` is discrete (π is injective). | — |
| `ForcePick.colOf_lt` | 283 | `colOf π`'s values are `< n`. | — |
| `ForcePick.colOf_transport` | 285-290 | The reindexing identity: transporting `colOf (π * σ)` by `σ` gives `colOf π`. This is what makes `π ↦ π * σ` the bijection the equivariance proof runs on. | — |
| `ForcePick.readKey_colOf_transport` | 292-297 | One term of the aggregate transports, with its index shifted by `σ` (`indivOne_transport` + `colOf_transport` + `readKey_transport`). | — |
| `ForcePick.readSet` | 299-302 | §8 The anchor's index set: every read of `v`'s individualization against every permutation colouring. Exponential by design — and crucially its index TYPE mentions neither `adj` nor `χ`, which is the whole design point. | Definition, `noncomputable` |
| `ForcePick.readSet_transport` | 304-317 | ★ §8 THE WHOLE INDEX SET IS INVARIANT — the bijection `π ↦ π * σ` matches the two families term for term. `readEquivariant_readAgg`'s proof shape, with the frame set replaced by one the relabelling cannot move. Because the two Finsets are EQUAL, `kmin?` needs no permutation-invariance lemma. | — |
| `ForcePick.readSet_nonempty` | 319-321 | The index set is nonempty (witness: the identity permutation), so the minimum is attained. | — |
| `ForcePick.readMin` | 323-326 | ★★ §8 THE NON-VACUITY ANCHOR — the lex-least read over all permutation colourings. `noncomputable` and exponential BY DESIGN, exactly as `orbKey` is; the bill says so out loud. ⚠ Brute force restated, NOT progress on the wall. | Definition, `noncomputable` |
| `ForcePick.keyV_readMin` | 328-329 | Value projection of `readMin` (`rfl`). | `@[simp]` |
| `ForcePick.keyCost_readMin` | 331-332 | `readMin`'s bill: `n! · n⁴`, exponential and visible — `②` rejects it, `①` does not. | `@[simp]` |
| `ForcePick.keyEquivariant_readMin` | 334-337 | ★★ §8 `KeyEquivariant` for the anchor, from the index-set invariance alone. | — |
| `ForcePick.exists_perm_keyV_readMin` | 339-352 | The minimum is attained: the key's value IS one of the reads (`kmin?_mem` + `Finset.mem_toList`). | — |
| `ForcePick.keySeparatesAll_readMin` | 354-365 | ★★★ §8 `KeySeparatesAll` UNCONDITIONALLY — equal minima are equal reads of two discrete `< n` colourings, which is exactly `isColAut_of_readKey_eq`'s hypothesis set. No guard, no faithfulness assumption, no rigidity. ⚠ Strictly better as an anchor than `keyEquivariant_compKey_readAgg_univ`, whose separation is the CARRIED `AggFaithful`. | — |
| `ForcePick.forcePick_readMin` | 367-380 | ★★★ §8 `forcePick_record`'s HYPOTHESIS SET IS INHABITED — an unconditional `①` + totality + (exponential) `②` canonizer. Pays the vacuity debt of §7 (the `ConfinementCitations.hflag` shape, machine-checked uninhabited, must not recur). | — |
| `ForcePick.forcePick_open_clause_is_poly` | 382-395 | ★ §8 THE REDUCTION, stated once: given the anchor, a POLYNOMIAL `keyCost` on any key with the same two `①` properties is all that separates the project from a complete polynomial canonizer. The open clause is exactly `poly keyCost` — not equivariance, not separation. | — |
## ChainDescent/RecordCost.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RecordCost.length_flatMap_le` | 52-60 | §1 A `flatMap` whose blocks are uniformly bounded — the counting workhorse for all four supplies' candidate lists. | — |
| `RecordCost.supplyCost_appendSupply` | 62-64 | §1 `appendSupply` SUMS THE COSTS — definitional, and the reason composing the four bounds is free. Its absence is why the record had no `②`: there was nothing to compose. | `@[simp]` |
| `RecordCost.gens_appendSupply_length` | 66-70 | §1 …and concatenates the candidate lists. | `@[simp]` |
| `RecordCost.supplyCost_foldSupplyFast_le` | 79-82 | §2a F2a's work: `|B|²·n⁵ ≤ n⁷`. | — |
| `RecordCost.gens_foldSupplyFast_length_le` | 84-88 | §2a F2a hands back `≤ n²` candidates. | — |
| `RecordCost.supplyCost_deckSupply_le` | 90-93 | §2a F2b's work: the same all-pairs shape, `≤ n⁷`. | — |
| `RecordCost.gens_deckSupply_length_le` | 95-99 | §2a F2b hands back `≤ n²` candidates. | — |
| `RecordCost.length_secondsV_le` | 106-115 | §2b `secondsV` is a `flatMap` over `finRange n` whose blocks are filters of `finRange n` ⟹ `≤ n²` seeds. One of the two facts that were missing rather than hard. | — |
| `RecordCost.length_deck2Batch_le` | 117-119 | §2b Hence a second-seed batch has `≤ n²` members (`filterMap` never grows a list). | — |
| `RecordCost.supplyCost_deck2Supply_le` | 121-125 | §2b F2c's work: `|B|²·(1+n²)·n⁵`. | — |
| `RecordCost.gens_deck2Supply_length_le` | 127-134 | §2b F2c hands back `≤ n⁴` candidates (the extra factor over 2a is the seed list). | — |
| `RecordCost.length_nullBasis_le` | 141-144 | §2c `nullBasis m rows` emits ONE WORD PER FREE COLUMN, so its length is `≤ m`. The second fact that was missing rather than hard. | — |
| `RecordCost.length_rails_le` | 146-148 | §2c Rails are a `filterMap` of `finRange n`, so `≤ n` of them. | — |
| `RecordCost.supplyCost_kernelSupply_le` | 150-151 | §2c C3a bills a flat `n⁵` by definition. | — |
| `RecordCost.gens_kernelSupply_length_le` | 153-160 | §2c Hence `|kernelGens| ≤ |kernelBasis| ≤ |rails| ≤ n` — the F₂ kernel supply hands back at most `n` generators. | — |
| `RecordCost.keyCost_holKeyFast_le` | 169-170 | §2d The force key of record bills a flat `n⁵`. Honest here (unlike the pre-2026-07-27 `orbKeyG`): `holSig` really is one `n⁵` sweep and delegates nothing. | — |
| `RecordCost.recordSupplyFast` | 174-178 | §3 The record consume-side supply, in the exact shape `Publication.canonForm?` uses. | `abbrev` |
| `RecordCost.recordSupplyBound` | 180-184 | §3 The record's per-node WORK budget: the four closed forms, summed. | Definition |
| `RecordCost.recordGensBound` | 186-188 | §3 The record's CANDIDATE-COUNT budget. | Definition |
| `RecordCost.supplyCost_record_le` | 190-195 | §3 The composite work bound, through `supplyCost_appendSupply`. | — |
| `RecordCost.gens_record_length_le` | 197-202 | §3 The composite candidate-count bound. | — |
| `RecordCost.descentCostS_selNode_record_le` | 210-222 | ★★★ §4 `②` END-TO-END FOR THE CANONIZER OF RECORD — an explicit polynomial `descentCostS` for `selNode holKeyFast (foldFast++deck++deck2++kernel)` on EVERY input, with NO hypotheses (fan-out `≤ 1` is `selNode_children_length_le_one`, structural). Before this the object with `②` proved (`lookaheadKey`+`prunedSupply`) was not the object of record. | — |
| `RecordCost.record_canonizer_with_cost` | 224-240 | ★★★ §4 THE RECORD CAPSTONE — `①` (`Kernel.holKey_foldDeck2KernelFast_selNode_canonizer`) and `②` in one place. ▶ Remaining before `Publication.cost` can stop being `opaque`: reshape this bound into the `costConst * n ^ costDeg` MONOMIAL the statement there pins. | — |
## ChainDescent/RecordKey.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RecordKey.pairKey` | 55-57 | ★ THE LEX PRODUCT of two force keys — values concatenate, costs add. ⚠ NOT the length-prefixed `(len a :: a) ++ …` encoding originally scoped: prefixing orders the first component by SHORTLEX, which `lexLeList` is not, so it would silently re-order `holKeyFast`'s own narrowing. Plain concatenation is correct under `ConstLen` (§2). | Definition |
| `RecordKey.keyV_pairKey` | 59-60 | Value projection of the product (`rfl`). | `@[simp]` |
| `RecordKey.keyCost_pairKey` | 62-63 | Cost projection of the product (`rfl`) — the two bills add. | `@[simp]` |
| `RecordKey.keyEquivariant_pairKey` | 65-69 | ★★ `①` FOR THE PRODUCT, UNCONDITIONAL — force's sole obligation is componentwise, so combining two equivariant keys needs no side condition. | — |
| `RecordKey.keyCost_pairKey_le` | 71-74 | The product's bill from the components'. | — |
| `RecordKey.keyV_pairKey_of_right_nil` | 76-79 | Where the second key defers (constant `[]`), the product IS the first key — so a shut guard costs nothing but the evaluation. | — |
| `RecordKey.ConstLen` | 86-89 | §2 The side condition that makes concatenation a genuine lex product: the key's value has the same length at every vertex of a node. Without it a shorter first component wins on length and the second is consulted at the wrong time. | Definition |
| `RecordKey.keyV_pairKey_inj` | 91-96 | §2 The product's value determines BOTH components (`List.append_inj` at the `ConstLen` length equality). | — |
| `RecordKey.keySeparatesAt_pairKey_left` | 98-101 | §2 The product separates whatever the FIRST component separates. | — |
| `RecordKey.keySeparatesAt_pairKey_right` | 103-107 | §2 …and whatever the SECOND does. Together these are the firing gain of a product over either component alone: the separated set is the union, never smaller. | — |
| `RecordKey.keySeparatesAll_pairKey_left` | 109-111 | §2 The global form, left. | — |
| `RecordKey.keySeparatesAll_pairKey_right` | 113-115 | §2 The global form, right. | — |
| `RecordKey.lexLeList_append_left` | 123-146 | §3 With equal-length prefixes, `lexLeList` on the concatenations refines `lexLeList` on the prefixes — the engine of the no-strength-loss theorem, and exactly where `ConstLen` does its work. | — |
| `RecordKey.keepMin_pairKey_subset` | 148-156 | ★★ §3 NO STRENGTH LOSS — the product's argmin sits inside the first key's, so a tiebreak can only SHRINK the narrowing, never widen it. The key-level analogue of `Select.canonFormS?_selNode_dominates`. ⚠ That it ever *does* shrink is a measurement, not a theorem (`Regression` §18: `G8` 8 → 2). | — |
| `RecordKey.constLen_holKeyFast` | 164-167 | §4 `holKeyFast` is `ConstLen`: `holSigFast` is a `map` over `List.range (n + 1)`. | — |
| `RecordKey.recordKey` | 169-171 | ★★ THE RECORD'S FORCE KEY — the holonomy key, tie-broken by the union-guarded orbit key. `holKeyFast` goes first so §3 preserves its ranking. | `abbrev` |
| `RecordKey.keyEquivariant_recordKey` | 173-175 | ★★★ `①`'s whole force-side obligation for the composed key, with no hypothesis. | — |
| `RecordKey.keepMin_recordKey_subset` | 177-181 | The tiebreak is never a regression: the holonomy key's narrowing is preserved. | — |
| `RecordKey.keySeparatesAt_recordKey_of_certifiedG` | 183-189 | The firing gain, stated: wherever `guardSupply`'s guard is open and the orbit key separates, so does the record key — even where the holonomy key ties. | — |
| `RecordKey.recordKey_canonizer` | 191-207 | ★★★ `①` FOR THE RECORD OBJECT AT THE COMPOSED KEY. Same supply, same refiner, same capstone: `Select.selNode_canonizer_of_sameOrbits` is KEY-GENERIC, so the swap costs exactly the `KeyEquivariant` proof above. | — |
| `RecordKey.guardSupplyBound` | 216-219 | §4a `guardSupply`'s work budget — three members bounded in `RecordCost`, `matchSupply` in `SupplyCost`. | Definition |
| `RecordKey.supplyCost_guardSupply_le` | 221-227 | §4a The union guard's own `supplyCost` bound. Needed because `orbKeyG`'s bill is parametric in its guard supply's (`keyCost_orbKeyG_le`). | — |
| `RecordKey.recordKeyBound` | 229-233 | §4a The composed key's per-evaluation bill: the holonomy sweep plus the guarded read AND its guard. | Definition |
| `RecordKey.keyCost_recordKey_le` | 235-238 | §4a The composed key's cost bound. | — |
| `RecordKey.descentCostS_selNode_recordKey_le` | 240-254 | ★★★ §4a `②` END-TO-END AT THE COMPOSED KEY — the same explicit-polynomial shape as `RecordCost.descentCostS_selNode_record_le`, with the key bound now carrying the guard's own work. No hypotheses. | — |
| `RecordKey.recordKey_canonizer_with_cost` | 256-270 | ★★★ THE UPGRADED RECORD CAPSTONE — `①` + `②` at the composed key. This is the object `Publication.canonForm?` should name; the remaining step there is reshaping the `②` bound into the `costConst * n ^ costDeg` monomial its statement pins. | — |
| `RecordKey.costConst` | 295-303 | The pinned cost constant **53** — the coefficient sum of §4a's `②` bound polynomial, computed (`recordKeyBound_expand`), not guessed. `Publication.costConst` is this. | Definition |
| `RecordKey.costDeg` | 305-306 | The pinned cost degree **13** — the degree of §4a's `②` bound polynomial. `Publication.costDeg` is this. | Definition |
| `RecordKey.pow_le_succ_pow` | 308-312 | §5 Every monomial below the pinned degree is dominated by the pinned one, `n ^ k ≤ (n+1) ^ costDeg` for `k ≤ costDeg` — by monotonicity alone, with no `1 ≤ n` side condition. This is why the published bound is pinned at `n + 1`. | — |
| `RecordKey.recordKeyBound_expand` | 314-324 | §5 §4a's `②` bound, expanded to `n^13 + n^12 + 3n^11 + … + n + 1` and checked by `ring` — which is what makes `costConst = 57` / `costDeg = 13` computed facts about the object rather than chosen numerals. ⚠ 53 → 57 on 2026-08-06 when `Deepen.stepCost` entered the bill (`+n⁵ + 2n⁶ + n⁷`). | — |
| `RecordKey.descentCostS_selNode_recordKey_monomial` | 326-345 | ★★★ §5 **`②` in the publication shape:** the canonizer of record, at the composed force key, runs within `costConst * (n+1) ^ costDeg` on **every** input — no hypotheses, no flag disjunct. Discharges `Showcase.canon_poly_or_flag` on its left disjunct. ⚠ `(n+1)`, not `n`: `descendS` bills 1 for a leaf, so at `n = 0` the object costs 1 and answers while `c * 0 ^ d = 0`. | — |
| `RecordKey.recordKey_canonizer_monomial` | 347-359 | §5 **The publication capstone:** `①` (`recordKey_canonizer`) and `②`-as-a-monomial together, at exactly the object `Publication.canonForm?` names. | — |
## ChainDescent/CaoFibring.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CaoFibring.isColAut_one` | 59-60 | The identity is a colour-automorphism. (`IsColAut adj χ` is a group — §1; the fibring argument composes and inverts.) | — |
| `CaoFibring.isColAut_mul` | 74-80 | Colour-automorphisms are closed under composition. | — |
| `CaoFibring.isColAut_inv` | 82-90 | Colour-automorphisms are closed under inverse. | — |
| `CaoFibring.SameOrbital` | 94-96 | Two ordered pairs lie in one **orbital** (2-orbit) of `IsColAut adj χ`. This is the object the CAO-propagation question is really about (doc §1). | Definition |
| `CaoFibring.SameStabOrbit` | 98-103 | Two vertices lie in one orbit of the **point stabilizer** of `v` — the partition individualizing `v` imposes on every other cell. | Definition |
| `CaoFibring.sameOrbital_refl` | 105-106 | `SameOrbital` is reflexive. | — |
| `CaoFibring.sameOrbital_symm` | 108-113 | `SameOrbital` is symmetric. | — |
| `CaoFibring.sameOrbital_trans` | 115-121 | `SameOrbital` is transitive. | — |
| `CaoFibring.sameStabOrbit_refl` | 123-124 | `SameStabOrbit` is reflexive. | — |
| `CaoFibring.sameStabOrbit_symm` | 126-132 | `SameStabOrbit` is symmetric. | — |
| `CaoFibring.sameStabOrbit_trans` | 134-140 | `SameStabOrbit` is transitive. | — |
| `CaoFibring.sameStabOrbit_iff_sameOrbital_row` | 142-145 | On `v`'s row the two notions coincide: the `K_v`-orbits on a cell are exactly the fibres of the orbital classification over `v`. Definitional, and the statement Step 2 consumes. | — |
| `CaoFibring.exists_row_transport` | 149-156 | ★ **Every orbital meets `v`'s row** — the surjectivity half of the fibring lemma, and **the only place transitivity on `v`'s cell (`CellSingleOrbit`) is used**. | — |
| `CaoFibring.sameStabOrbit_of_transports` | 158-162 | The row transport is well defined up to the stabilizer: two transports of one pair into `v`'s row differ by an element of `K_v`. | — |
| `CaoFibring.sameOrbital_iff_sameStabOrbit_of_transport` | 164-180 | ★★ **THE FIBRING LEMMA** (doc §12.1). The row transport is a **complete invariant** of the orbital class; with `exists_row_transport` this is the bijection `{K-orbitals in D × C} ≃ {K_v-orbits on C}`. Needs no hypothesis — `CellSingleOrbit` is used only for existence of transports. | — |
| `CaoFibring.PairInvariant` | 187-189 | An `IsColAut`-invariant colouring of ordered pairs — what any 2-WL closure supplies. | Definition |
| `CaoFibring.pairInvariant_eq_of_sameOrbital` | 191-197 | **Soundness:** an invariant pair colouring is constant on orbitals, so its classes are *unions* of orbitals. This is why refinement can never split an orbit. | — |
| `CaoFibring.levelSet_iff_stabOrbit_of_separates` | 199-213 | ★★ **STEP 2** (doc §12.2). If an invariant pair colouring merely *separates the orbitals in `v`'s row*, the vertex colouring it induces there has level sets **exactly** the `K_v`-orbits. ⟹ CAO-propagation reduces to orbital separation with no remainder; the hypothesis `hsep` is the open crux (doc §12.3). | — |
## ChainDescent/CaoRound.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CaoRound.PairInvariantAt` | 50-57 | A pair colouring invariant under the **stabilizer of `v`** — the group that acts once `v` is individualized, and the one `CaoFibring.SameStabOrbit` quantifies over. Strictly weaker than `PairInvariant`, and it is what the real closure satisfies. | Definition |
| `CaoRound.pairInvariantAt_of_pairInvariant` | 59-61 | Full `IsColAut`-invariance implies invariance at any base point. | — |
| `CaoRound.pairInvariantAt_eq_of_sameStabOrbit` | 63-71 | **Soundness at the pointed group:** an invariant pair colouring is constant along `v`'s row on orbits of the `v`-stabilizer. | — |
| `CaoRound.levelSet_iff_stabOrbit_of_separatesAt` | 73-83 | ★★ **STEP 2 AT THE HYPOTHESIS THE REAL OBJECT SATISFIES** (doc §12.2). Supersedes `CaoFibring.levelSet_iff_stabOrbit_of_separates` for applications: that version needs invariance under all of `IsColAut adj χ`, which the individualized closure does **not** have. | — |
| `CaoRound.sig` | 90-92 | The multiset of **triangle types** `(f a x, f x b)` over intermediate points `x` — one refinement round's entire content, and the object `probe_cao_cause.py` extracts witnesses from. | Definition |
| `CaoRound.roundBy` | 94-97 | One 2-dimensional refinement round, re-encoded by `enc` so the colour type is stable under iteration (the rank-renumbering every implementation does). | Definition |
| `CaoRound.iterRoundBy` | 99-103 | `k` refinement rounds. | Definition |
| `CaoRound.sig_congr` | 114-126 | ★ **The heart of invariance-preservation:** a `σ` under which `f` is invariant may be absorbed into the intermediate point, because it permutes the universe. | — |
| `CaoRound.pairInvariantAt_roundBy` | 128-134 | A refinement round preserves pointed invariance. | — |
| `CaoRound.pairInvariantAt_iterRoundBy` | 136-141 | **Any number of rounds preserves it** — hence the whole closure is invariant. | — |
| `CaoRound.pairInvariant_roundBy` | 143-149 | The unpointed version, for the closure taken *before* individualization. | — |
| `CaoRound.ext0` | 153-156 | The individualized initial colouring: the old colour plus the two flags marking `v`. This is where — and the **only** where — the extension's new information enters. | Definition |
| `CaoRound.pairInvariantAt_ext0` | 158-169 | Individualizing `v` keeps the colouring invariant under the **stabilizer** of `v`; the flags are exactly what a `σ` fixing `v` preserves. | — |
| `CaoRound.step2_closure` | 171-184 | ★★ **THE CAPSTONE — Step 2 applies to the real object.** From any invariant root colouring, individualize `v` and take **any** number of rounds: if the result separates the orbitals in `v`'s row, its level sets there are exactly the `K_v`-orbits. Only `hsep` (doc §12.3) is left. | — |
| `CaoRound.Coherent` | 188-192 | **Coherence in the form that states the barrier**: the colouring is a *fixpoint* of the round — equal-coloured pairs have equal triangle-type multisets. | Definition |
| `CaoRound.round1_barrier` | 224-242 | ★★ **THE ROUND-1 BARRIER** (doc §12.3, prose until now). At a coherent `X`, individualizing `v` and taking **one** round does not separate two pairs of `v`'s row that `X` already identified — the base point learns nothing directly. ⟹ any proof of the crux needs ≥ 2 rounds; no local argument at `v` can work. | — |
| `CaoRound.witness_ne_base` | 244-259 | ★ **The marking is provably non-local.** If a round *does* separate `(v,u)` from `(v,w)` while they share a colour, the difference lives in the intermediate points `x ≠ v` — the base point's own term is identical on both sides. This is the theorem behind M3's measured cause chains. | — |
| `CaoRound.Transposable` | 274-277 | The **transpose axiom** of a coherent configuration: the colour of `(b,a)` is a function of the colour of `(a,b)`. Measured to hold for every root closure in the evidence base (5/5, `probe_cao_round2.py`). | Definition |
| `CaoRound.zAug` | 279-282 | The **`v`-augmented colouring** — each pair tagged with its triangle type through the base point. This is the round-1 information of the extension made explicit; measured to be *exactly* the round-1 partition on 5/5 objects. | Definition |
| `CaoRound.sig_zAug_row_eq` | 284-310 | ★★ **THE ROUND-2 BARRIER (core).** At a coherent, transpose-closed `X` the `v`-augmented signature still does not separate two pairs of `v`'s row that `X` identified — on the row the augmentation adds nothing independent (`X x v = T (X v x)`), so the whole signature is the image of the round-**0** signature under one fixed map. | — |
| `CaoRound.sig_factor` | 312-320 | A colouring factoring through `zAug` has its signature the `Ψ`-image of `zAug`'s. | — |
| `CaoRound.round2_barrier` | 322-333 | ★★ **THE ROUND-2 BARRIER.** Any colouring factoring through the triangle-type-through-`v` data — what one round of the individualized configuration produces — **still** fails to separate `v`'s row. With `round1_barrier`: **separation cannot occur before round 3**, the uniform depth M3 measured 11/11. | — |
| `CaoRound.DiagSep` | 346-349 | The **diagonal axiom** at `v` (`X a v = X v v ⟹ a = v`, and the mirror), in the two forms used. Its *only* role is recovering the base-point flags from `zAug`. | Definition |
| `CaoRound.sig_ext0_congr` | 384-401 | ★★ **THE ROUND-1 SIGNATURE IS DETERMINED BY `zAug`.** The `x = v` term is `(X a v, X v b)` outright and the far part is `sig X a b` minus that term, hence coherence-determined. This is the mathematical content of `round2_barrier`'s hypothesis `hg`. | — |
| `CaoRound.roundBy_ext0_congr` | 403-414 | The whole round-1 **colour** (not just its signature) is determined by `zAug`. | — |
| `CaoRound.exists_factor_roundBy_ext0` | 416-430 | ★★ **`hg` DISCHARGED** — the round-1 colour of the individualized configuration is genuinely a *function* of the `v`-augmented colouring. | — |
| `CaoRound.round2_barrier_real` | 432-440 | ★★★ **THE ROUND-2 BARRIER, UNCONDITIONAL.** No factorization hypothesis: from `{Coherent, Transposable, DiagSep}` — literally the CC axioms — two rounds of the individualized configuration do not separate `v`'s row. With `round1_barrier`: **separation cannot occur before round 3**, explaining the uniform depth M3 measured 11/11. | — |
| `CaoRound.triCount` | 478-481 | The **triangle count** — how many intermediate points realize the triangle type `q` at `(a,b)`. This is the object doc §12.5a's sharpened R1 is about, and what the crux reduces to. | Definition |
| `CaoRound.triCount_eq_card` | 483-488 | `triCount` as a `Finset` cardinality — the count in the form the measurements compute. | — |
| `CaoRound.roundBy_eq_of_sig_eq` | 490-495 | A round cannot separate what the signature does not (no hypothesis on the re-encoding). | — |
| `CaoRound.roundBy_ne_iff_sig_ne` | 497-507 | ★ **THE CONDITIONAL CONVERSE.** For a faithful (injective) re-encoding, a round separates two pairs of equal colour **exactly when** their signatures differ. | — |
| `CaoRound.sig_ne_iff_exists_triCount_ne` | 509-520 | Signatures differ **iff** some triangle type has a different count — the concrete inequality form. | — |
| `CaoRound.round2_row_colour_eq` | 522-532 | The colour-level form of the barriers: through round 2 the row colours themselves agree, not merely their signatures. | — |
| `CaoRound.round3_separates_iff_triCount_ne` | 534-552 | ★★★ **THE CRUX, REDUCED TO ONE INEQUALITY.** Round 3 separates `v`'s row **iff** some triangle type of the round-2 colouring has a different count at `(v,u)` than at `(v,w)`. Rounds, the row and the closure are discharged; what remains is one inequality between finite explicit counts. ⚠ The *unconditional* 'separation must occur at round 3' is strictly stronger than the crux and cannot follow from the barriers (doc §12.3). | — |
## ChainDescent/TwinFamily.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `TwinFamily.Simple` | 85-89 | The simple-graph setting: `adj` symmetric and loopless. Both are consumed by `isColAut_swap_of_twin` — symmetry to move the twin condition to the other coordinate, looplessness for the diagonal. | Definition |
| `TwinFamily.Twin` | 91-96 | **Modular twins**: identical adjacency to every *other* vertex. Constrains neither `adj u w` nor the diagonal, so it covers false twins (`N(u)=N(w)`) and true twins (`N[u]=N[w]`) alike. | Definition |
| `TwinFamily.isColAut_swap_of_twin` | 107-123 | ★ **THE WITNESS.** Transposing a same-coloured twin pair is a colour-preserving automorphism. Adjacency half reuses `isAut_swap_of_twin`; the colouring half is new (the transposition moves only two vertices, which already share a colour). | — |
| `TwinFamily.TwinCells` | 129-131 | The invariant: every pair the colouring merges is a modular twin pair. This is the whole content of the family. | Definition |
| `TwinFamily.twinCells_step` | 146-155 | ★ **THE INVARIANT IS INHERITED — no graph-specific reasoning.** `Deepen.step = refineV encodeFreeFast ∘ indivOne` and both halves only split, so a pair merged downstream was already merged upstream. This is what collapses the per-family obligation to the root. | — |
| `TwinFamily.cellSingleOrbit_of_twinCells` | 157-164 | Under the invariant EVERY cell is a single orbit — the selector-independent statement the step-0 probe measured, strictly stronger than what `TinhoferPath` asks. | — |
| `TwinFamily.tinhoferPath_of_twinCells` | 141-160 | `TinhoferPath` at every fuel, by induction: the level`s `CellSingleOrbit` from the invariant, the recursive call still under the invariant by `twinCells_step`. | — |
| `TwinFamily.tinhofer_of_twinCells` | 162-166 | `Deepen.Tinhofer` from the invariant — each anchor`s first step lands under the invariant. | — |
| `TwinFamily.SchurianAt` | 172-175 | **`SchurianAt`** — every cell of `χ` is a single orbit of the colour-stabilizer, i.e. 1-WL's partition at `χ` *is* the orbit partition. | Definition |
| `TwinFamily.schurianAt_iff_no_rigidObstruction` | 177-190 | ★ **`SchurianAt` IS the absence of rigid obstructions** (de Morgan, both directions). The reading to quote: the class is *"contains no rigid obstruction"* — the exact complement of the rigid resolver's domain, which is what lets it later be weakened to *"no rigid obstruction the rigid resolver does not already handle"* with nothing below re-proved. | — |
| `TwinFamily.StepClosed` | 192-198 | **A class of colourings closed under the descent's own step** — *peeling a layer keeps you in the class*. The structural property that makes a per-family discharge finite; it is exactly why the Tinhofer reading is tractable and the CFI reading is not. | Definition |
| `TwinFamily.tinhoferPath_of_stepClosed` | 200-221 | `TinhoferPath` at every fuel for ANY step-closed obstruction-free class: the level`s `CellSingleOrbit` is the class`s Schurianity, the recursive call stays in the class by step-closure. | — |
| `TwinFamily.tinhofer_of_stepClosed` | 223-227 | `Deepen.Tinhofer` for any colouring in a step-closed obstruction-free class. | — |
| `TwinFamily.rootCol` | 231-233 | The descent's root colouring — `refineV encodeFreeFast` applied to the constant colouring. | Definition |
| `TwinFamily.mem_of_reaches` | 235-245 | A step-closed class holding at the root holds at EVERY reached node — `Descend.Reaches`?s step and `Deepen.step` are the same operation. So a family only ever has to earn the root. | — |
| `TwinFamily.handledS_of_noRigidObstruction` | 247-258 | ★★★ **THE SOCKET, stated on "no rigid obstruction" rather than on twins.** Step-closed + holds at root + carries no rigid obstruction ⟹ `Select.HandledS`. ▶ To enlarge the handled region, supply a wider class — nothing below this theorem changes. | — |
| `TwinFamily.stepClosed_twinCells` | 262-264 | Twin-merging is step-closed. | — |
| `TwinFamily.schurianAt_of_twinCells` | 266-269 | A twin-merging colouring is Schurian. | — |
| `TwinFamily.RootTwins` | 271-274 | **The per-family obligation, stated once**: every pair the ROOT colouring merges is a twin pair. Everything below the root is free. | Definition |
| `TwinFamily.twinCells_of_reaches` | 276-279 | Every reached colouring merges only twin pairs — `RootTwins` propagated along `Reaches` by the step-closure of `TwinCells`. | — |
| `TwinFamily.handledS_of_rootTwins` | 281-284 | ★★★ **THE GENERIC SOCKET.** `Simple ∧ RootTwins ⟹ Select.HandledS orbKey deepenSupply`. Family-agnostic: any family that earns the root condition plugs in here with no re-proof. | — |
| `TwinFamily.IsCompleteMultipartite` | 304-306 | The complete multipartite graph induced by a part assignment: adjacent iff in different parts. | Definition |
| `TwinFamily.psize` | 308-310 | The number of vertices in a given part. | Definition |
| `TwinFamily.DistinctPartSizes` | 312-315 | **The family's defining hypothesis**: distinct parts have distinct sizes. Stated through vertices, so it only ever constrains *inhabited* parts. | Definition |
| `TwinFamily.simple_of_multipartite` | 317-325 | A complete multipartite graph is symmetric and loopless. | — |
| `TwinFamily.degSum_eq_of_rootCol_eq` | 329-356 | Equal root colour ⟹ equal degree. Peels the warm round to a single round (`Refine.iterate_splits`), whose fibres are the `sigKey` fibres; at the constant colouring the signature carries exactly the multiset of incident edge-values. | — |
| `TwinFamily.degSum_multipartite` | 360-375 | In a complete multipartite graph a vertex is adjacent to exactly the vertices outside its part. | — |
| `TwinFamily.rootTwins_of_multipartite` | 388-402 | ★★ **THE FAMILY INSTANCE.** With pairwise distinct part sizes, equal root colour forces equal degree, hence equal part size, hence the *same part* — and same-part vertices are modular twins. | — |
| `TwinFamily.handledS_of_multipartite` | 404-408 | ★★★ **THE NAMED FAMILY IS `HandledS`** — the wind-down's W1 target: a family, not a hypothesis. Routed through `handledS_of_rootTwins`, so the multipartite content is only `simple_of_multipartite` + `rootTwins_of_multipartite`. | — |
| `TwinFamily.mpAdj` | 417-420 | Constructor for the complete multipartite graph on a part assignment — makes the family visibly inhabited at every `n`. | Definition |
| `TwinFamily.isCompleteMultipartite_mpAdj` | 422-423 | `mpAdj part` is complete multipartite on `part`, by `rfl`. | — |
| `TwinFamily.rootCol_eq_of_twin` | 425-446 | ★★ **THE NON-VACUITY LEMMA.** A twin pair survives refinement: the transposition is an automorphism fixing the constant colouring and the refiner is equivariant (①b), so an equivariant refiner cannot separate a pair some automorphism swaps. | — |
| `TwinFamily.not_discrete_rootCol_mpAdj` | 448-457 | A complete multipartite graph with a part of size ≥ 2 has a **non-discrete** root — the non-vacuity gate, so the family is not the `handled_of_root_discrete` ring in disguise. | — |
| `TwinFamily.part123` | 466-467 | Parts of sizes 1, 2, 3 on six vertices — the concrete witness `K₁,₂,₃`. | Definition |
| `TwinFamily.distinctPartSizes_part123` | 469-471 | The sizes 1, 2, 3 are pairwise distinct (`decide`). | — |
| `TwinFamily.handledS_part123` | 473-476 | ★ **THE CONCRETE INSTANCE** — a specific 6-vertex graph that is `HandledS`. | — |
| `TwinFamily.not_discrete_part123` | 478-480 | … and whose root is not discrete, so the witness is genuinely non-vacuous. Probe-measured at 30 reached nodes / 18 non-discrete / 3 levels / `spans = 0`. | — |
| `TwinFamily.answersS_of_multipartite` | 495-501 | ★★★ **THE FAMILY ANSWERS** — the fused descent terminates with an answer, never flags, on the whole family. ⚠ NOT "canonized": the canonical-form half `①` needs `SupplyEquivariant`, which `deepenSupply` lacks (pre-existing boundary, see the module doc-block §7). | — |
| `TwinFamily.answersS_part123` | 503-509 | The concrete 6-vertex witness answers. | — |

| `TwinFamily.decidableTwin` | 523-524 | `Twin` is decidable (a finite check), so the twin supply is computable. | Instance |
| `TwinFamily.twinSupply` | 526-531 | **The twin supply**: every transposition of a twin pair inside the branch cell. Computable, and a structural function of `(adj, χ)`. Cost is the honest enumeration bill. | Definition |
| `TwinFamily.mem_gens_twinSupply_iff` | 533-546 | Membership characterization of the twin supply's candidate list: exactly the transpositions `Equiv.swap u w` of twin pairs drawn from the branch cell. | — |
| `TwinFamily.cellIsOrbit_twinSupply` | 548-564 | ★★ **THE FIRING THEOREM.** Under `TwinCells` the branch cell is a single orbit of the *verified* twin transpositions — reached in ONE `WordReach` step, since the connecting permutation is itself a generator. | — |
| `TwinFamily.handled_of_rootTwins` | 566-570 | ★★★ The **blind** `Residue.Handled` predicate, **for every key** — strictly stronger than `Select.HandledS`, and with no `orbKey`/`deepenSupply` anywhere. | — |
| `TwinFamily.handled_of_multipartite` | 572-576 | The named family at the blind `Residue.Handled` predicate. | — |
| `TwinFamily.answers_of_multipartite` | 578-584 | ★★★ The **guarded** canonizer ANSWERS on the family at a *computable* key and supply. `Residue.answers_of_handled` needs only `Handled`, no equivariance. | — |
| `TwinFamily.twin_relabel` | 594-604 | `Twin` transports: on the relabelled graph the twin pairs are exactly the σ-images. | — |
| `TwinFamily.gensEquivariant_twinSupply` | 606-622 | `GensEquivariant` for the twin supply — branch-cell membership and `Twin` both transport (`twin_relabel`, `branches_transport_perm`), so the emitted generator set conjugates. This is what discharges `StallEquivariant`, hence `①`. | — |
| `TwinFamily.supplyEquivariant_twinSupply` | 624-626 | `SupplyEquivariant` for the twin supply, via `supplyEquivariant_of_gensEquivariant`. This is what discharges `StallEquivariant`, hence `①`. | — |
| `TwinFamily.canonizer_twinSupply` | 628-638 | ★★★ **`①` FOR THE TWIN-SUPPLY CANONIZER** — `IsCanonicalFormOpt`: sound + iso-invariant, hence complete. A statement about the *function*, independent of any family. | — |
| `TwinFamily.canonized_of_multipartite` | 640-653 | ★★★ **THE PUBLICATION-SHAPED STATEMENT, BOTH HALVES**: `①` (sound + iso-invariant + complete) AND *answers, never flags*, on every complete multipartite graph with distinct part sizes — at `Hol.holKeyFast` + `twinSupply`, guard in place, so single-path too. | — |
| `TwinFamily.canonized_part123` | 655-660 | The concrete `K₁,₂,₃` witness, canonized. | — |
| `TwinFamily.supplyCost_twinSupply_le` | 669-673 | The twin supply's work bill: `|B|² · n² ≤ n⁴`, by replacing `(branches χ).length` with `n`. | — |
| `TwinFamily.gens_twinSupply_length_le` | 675-680 | The twin supply's candidate count: `≤ n²` (a `flatMap` of `filterMap`s over the branch cell). | — |
| `TwinFamily.answers_poly_of_multipartite` | 682-698 | ★★★ **`②` FOR THE TWIN OBJECT** — the family *answers* AND its `descentCost` is bounded by an explicit polynomial, at `Hol.holKeyFast` + `twinSupply`. With `canonizer_twinSupply` (`①`) this is the **only place in the project where `①`, `②` and *answers* hold together on a named family**. | — |
| `TwinFamily.IndivReach` | 727-733 | **The individualization closure** — every colouring reachable from the refined root by individualizing a vertex and refining, under ANY sequence of choices. ★ Step-closure is definitional, so feeding it to the socket costs nothing and raises no CAO-propagation obligation. | Inductive |
| `TwinFamily.stepClosed_indivReach` | 735-736 | The individualization closure is step-closed, by construction. | — |
| `TwinFamily.TinhoferGraph` | 738-742 | **The literature`s Tinhofer condition in the project`s vocabulary**: at every individualization-reachable colouring every cell is a single orbit — i.e. no rigid obstruction anywhere, under any selector. ⚠ Deliberately NOT computable: a classifier, not part of the algorithm (deciding it is ≥ GI on vertex-transitive graphs, AKRV Thm 22). | Definition |
| `TwinFamily.handledS_of_tinhoferGraph` | 744-748 | ★★★ **THE BRIDGE.** A Tinhofer graph is `Select.HandledS` — the descent progresses at every step. One theorem covering every family known to be Tinhofer, by citation of membership rather than per-family Lean. | — |
| `TwinFamily.answersS_of_tinhoferGraph` | 750-755 | ★★ A Tinhofer graph ANSWERS — the fused descent never flags on it. | — |
| `TwinFamily.not_tinhoferGraph_of_flagS` | 757-766 | ★★★ **THE SHOWCASE STATEMENT — the flag is evidence about the INPUT.** If the canonizer flags, the graph is provably not Tinhofer: `③`'s shape against a named literature class rather than an opaque atom, and the contrapositive that the classifier's non-computability makes the useful direction. ⛔ Stated at the `noncomputable` `orbKey`; `not_tinhoferGraph_of_flag` (§10) is the executable form. | — |
| `TwinFamily.twinCells_of_indivReach` | 773-778 | Every individualization-reachable colouring of a root-twin graph merges only twin pairs. | — |
| `TwinFamily.tinhoferGraph_of_rootTwins` | 780-783 | **Witness 1** — the twin family is Tinhofer. This is the witness that actually exercises the resolvers. | — |
| `TwinFamily.tinhoferGraph_of_multipartite` | 785-787 | The complete multipartite family (distinct part sizes) is Tinhofer. | — |
| `TwinFamily.discrete_of_indivReach` | 789-798 | Individualization-reachable colourings of a 1-WL-discretizing graph stay discrete. | — |
| `TwinFamily.tinhoferGraph_of_root_discrete` | 800-819 | Witness 2 — every 1-WL-discretizing graph is Tinhofer (a discrete colouring's cells are singletons, so the identity witnesses `SchurianAt`). ⚠⚠ **VACUOUS FOR THE RESOLVERS**: no reached non-discrete node, so refinement alone finishes and neither resolver is consulted. Breadth of the *answering* claim only — do not quote the Babai–Erdős–Selkow measure claim without this caveat. | — |
| `TwinFamily.cellIsOrbit_deepenSupply_of_schurianAt` | 853-863 | ★★ **THE FIRING LEMMA FOR §10.** At a node that is Schurian *and* `Deepen.Tinhofer`, the deepening supply certifies the whole branch cell: `SchurianAt` supplies the automorphism, `Deepen.deepen_branch_orbit_iff_aut` supplies the *certificate*. | — |
| `TwinFamily.noStall_of_schurianAt` | 865-873 | ★★★ **THE NODE-LOCAL STATEMENT — *a Tinhofer residue does not stall*.** Speaks about ONE reached node rather than the graph from the root, so a resolver that peels a layer and lands here inherits it directly — the composable shape W2's scope correction asks for. Holds for **every** key (force is not consulted). | — |
| `TwinFamily.handled_deepenSupply_of_noRigidObstruction` | 875-883 | The socket again, landing on the **blind** `Residue.Handled` at `deepenSupply` instead of the sel-aware `HandledS` at `(orbKey, deepenSupply)`. | — |
| `TwinFamily.handled_of_tinhoferGraph` | 885-888 | ★★★ **A TINHOFER GRAPH IS `Residue.Handled` — the blind predicate, for EVERY key.** Strictly stronger than §9's `handledS_of_tinhoferGraph`, and with nothing `noncomputable`. | — |
| `TwinFamily.answers_of_tinhoferGraph` | 890-894 | ★★★ A Tinhofer graph is **answered at an EXECUTABLE object** (contrast §9, whose `orbKey` is `noncomputable`). | — |
| `TwinFamily.not_tinhoferGraph_of_flag` | 896-902 | ★★★ **THE SHOWCASE, REPAIRED** — if the canonizer flags, the input is provably **not Tinhofer**, at an object that RUNS. This is the publishable form of `not_tinhoferGraph_of_flagS`. | — |
| `TwinFamily.supplyCost_deepenSupply_le` | 909-910 | `deepenSupply`'s work bill — `le_rfl`, since it charges a **declared flat `n⁶`**. ⚠ Declared, not derived (an honest over-estimate of `≤ n` reps × `≤ n` levels × a warm refinement `n³`, plus `≤ n` verifications at `n²`). | — |
| `TwinFamily.gens_deepenSupply_length_le` | 912-925 | `deepenSupply`'s candidate count: `≤ n²`, the same `flatMap`-of-`filterMap` shape as the four record supplies. | — |
| `TwinFamily.answers_poly_of_tinhoferGraph` | 927-940 | ★★★ **ANSWERS *AND* AN EXPLICIT POLYNOMIAL BUDGET ON EVERY TINHOFER GRAPH** — the `②` half of the publication claim at the executable object. ⚠ **`①` remains OPEN** there: it needs `SupplyEquivariant deepenSupply` (via `StallEquivariant`), i.e. the parked **R1** crux — so the claim is *answers*, **not** *canonizes*. | — |
| `TwinFamily.answers_poly_part123` | 942-954 | The concrete `K₁,₂,₃` witness through the repaired bridge — non-vacuous because its root is **not** discrete (`not_discrete_part123`), so the resolvers genuinely run. | — |
## Examples.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `canonForm?` | 25-31 | — | Definition |
| `ofEdges` | 33-35 | — | Definition |
| `rows?` | 37-40 | — | Definition |
| `sameGraph?` | 68-74 | — | Definition |
## ChainDescent/RestrictedTransport.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RestrictedTransport.reaches_transport` | 75-94 | The reached set of the relabelled graph is the transported reached set. Needed because the covering argument is applied at **both** `adj` and `relabelAdj σ adj`. | — |
| `RestrictedTransport.RelabelClosed` | 98-101 | A class of graphs closed under relabelling — the minimum for "iso-invariant **on** the class" to mean anything. | Definition |
| `RestrictedTransport.TransportOn` | 103-107 | ★ `Descend.TransportAt` relativized on **both** axes: graphs in `C`, and the colourings the descent actually reaches. ⚠ The colouring axis is load-bearing — at an unreachable `χ` a cell need not be an orbit even in a Tinhofer graph. | Definition |
| `RestrictedTransport.NarrowTransportOn` | 109-118 | `Descend.NarrowTransport` relativized the same way — the per-node obligation on the class. | Definition |
| `RestrictedTransport.descend_transport_on` | 120-141 | ★★ **THE RELATIVIZED TRANSPORT INDUCTION** — the mirror of `Descend.descend_transport`. The recursion never leaves `adj`, so the graph axis threads through untouched and only the reached-colouring side condition is new. | — |
| `RestrictedTransport.isoInvariantOn` | 143-155 | ★★ **ISO-INVARIANCE ON THE CLASS** — the relativized `Descend.isoInvariantOpt_canonForm?`. The root colouring is `Reaches.root`, so no side condition escapes to the caller. | — |
| `RestrictedTransport.eq_of_graphIso_on` | 159-167 | Isomorphic inputs get the same answer — `CanonSpec.eq_of_graphIso` on the class. Only the **left** input need be in `C`. | — |
| `RestrictedTransport.complete_on` | 169-184 | ★★★ **COMPLETENESS ON THE CLASS (`①b`)** — equal outputs ⟺ isomorphic. Soundness is unconditional, so only the `→` direction consumes the restricted invariance. | — |
| `RestrictedTransport.flag_iso_invariant_on` | 186-191 | `①c` on the class — flagging is a property of the isomorphism class. | — |
| `RestrictedTransport.branchVal_transport_on` | 198-209 | `Descend.branchVal_transport` with the relativized IH; the reached-child side condition is `Reaches.step`, discharged from `v` sitting in the branch cell. | — |
| `RestrictedTransport.branchVal_eq_of_isColAut_on` | 211-221 | `Consume.branchVal_eq_of_isColAut` with the relativized IH: an automorphism makes two branches value-equal. | — |
| `RestrictedTransport.coveringOfAt_forceThenPick_on` | 223-263 | `ForcePick.coveringOfAt_forceThenPick` relativized — the singleton pick covers the forced set, because under `KeySeparatesAt` every survivor is automorphic to the one kept. | — |
| `RestrictedTransport.narrowTransportOn_forceThenPick` | 265-283 | ★★★ **THE CONTRACT ON THE CLASS.** `KeyEquivariant` makes the forced set an equivariant intermediate; relativized separation makes the singleton pick cover it — at `adj` *and* at `relabelAdj σ adj`, which is where `RelabelClosed` and `reaches_transport` are consumed. | — |
| `RestrictedTransport.keySeparatesAt_of_schurianAt` | 291-299 | ★ **THE "NO WRONG STEP TO TAKE" LEMMA.** At a Schurian node every branch pair *is* linked by an automorphism, so `KeySeparatesAt`'s antecedent is false and it holds **vacuously, for every key**. ⚠⚠ This is **not** the vacuity `ForcePick`'s header bans: there it is satisfied because a guarded key *deferred* while genuine separation was still required; here there is nothing to separate, so the singleton pick discards only automorphic duplicates. Same syntax, opposite semantics. | — |
| `RestrictedTransport.indivReach_transport` | 307-321 | `IndivReach` transports along a relabelling — root by refiner equivariance, step by `Deepen.step_transport`. | — |
| `RestrictedTransport.schurianAt_transport` | 323-326 | `SchurianAt` transports, via the cross-graph `Deepen.cellSingleOrbit_transport_iso`. | — |
| `RestrictedTransport.relabelClosed_tinhoferGraph` | 328-336 | `TwinFamily.TinhoferGraph` is closed under relabelling — pull the colouring back along `σ⁻¹`, apply the hypothesis, push forward. | — |
| `RestrictedTransport.indivReach_of_reaches` | 338-342 | The bridge from `Descend.Reaches` (what the spine quantifies over) to `TwinFamily.IndivReach` (what `TinhoferGraph` speaks about). | — |
| `RestrictedTransport.narrowTransportOn_tinhofer` | 346-352 | The contract at `TinhoferGraph`, for **any** equivariant key. | — |
| `RestrictedTransport.isoInvariant_on_tinhofer` | 354-360 | ★★★ **`①` ON THE TINHOFER CLASS** — iso-invariance, hence (with unconditional soundness) a complete isomorphism invariant, for any computable equivariant key. | — |
| `RestrictedTransport.canonizes_on_tinhofer` | 362-387 | ★★★ **THE HEADLINE — A TINHOFER GRAPH IS CANONIZED**: sound (unconditional) ∧ complete on the class ∧ **never flags** (no hypothesis — `forceThenPick` has no stall channel). Upgrades `TwinFamily.answers_of_tinhoferGraph` from *answers* to *canonizes*, using **no supply**: `deepenSupply` and its declared flat `n⁶` charge are gone. | — |
| `RestrictedTransport.descentCost_on_tinhofer` | 389-396 | ★★★ **`②`** — explicit polynomial `descentCost` on **every** input, no hypotheses. Only the key is billed, since there is no supply. | — |
| `RestrictedTransport.canonizes_on_tinhofer_holKeyFast` | 398-412 | The whole package at a **computable, equivariant** key (`Hol.holKeyFast`) — the publication statement. | — |
| `RestrictedTransport.SigRegular` | 437-443 | **Signature-regular**: the multiset of incident values is the same at every vertex (ordinary regularity for a `0/1` matrix). Stated as the multiset directly because that is exactly what the refiner's `signature` reads — which also makes it `decide`-able on a concrete graph. | Definition |
| `RestrictedTransport.refineRound_const_of_sigRegular` | 445-464 | One refinement round keeps a constant colouring constant: the signature at `v` is the incident-value multiset pushed through `y ↦ (k, y, unknown)`, so regularity is exactly what is needed. | — |
| `RestrictedTransport.rootCol_const_of_sigRegular` | 466-486 | ★ **THE ROOT CELL IS EVERYTHING** on a signature-regular graph. ⚠ Needed because `rootCol` does **not** kernel-reduce — `decide` on `rootCol kc 0 = rootCol kc 3` gets stuck (trap #3); the regularity route sidesteps evaluation. Stated pairwise so it does not need `Fin n` inhabited. | — |
| `RestrictedTransport.triAt` | 490-494 | Ordered pairs of adjacent neighbours of `v` — `2 ×` the triangles through `v`. Only invariance and two computed values matter, so the constant is irrelevant. | Definition |
| `RestrictedTransport.triAt_of_relabel_eq` | 496-506 | ★ **`triAt` IS `Aut`-INVARIANT** — the bijection is `σ` on both coordinates (`Finset.card_equiv` at `Equiv.prodCongr σ σ`). | — |
| `RestrictedTransport.kcEdges` | 510-511 | Edge list of `K₃ ⊔ C₄`: the triangle `0-1-2` and the 4-cycle `3-4-5-6-3`. | Definition |
| `RestrictedTransport.kcAdj` | 513-515 | **The non-Tinhofer witness graph** `K₃ ⊔ C₄` — 2-regular, `Aut = S₃ × D₄` with two orbits. Re-used from `probe_w1_cographs.py`'s minimal cograph falsifier. | Definition |
| `RestrictedTransport.sigRegular_kcAdj` | 517-519 | `K₃ ⊔ C₄` is signature-regular (`decide`; cheap — no descent object appears). | — |
| `RestrictedTransport.triAt_kcAdj_zero` | 521 | Vertex `0` (in the `K₃`) lies on a triangle: `triAt = 2`. | — |
| `RestrictedTransport.triAt_kcAdj_three` | 523 | Vertex `3` (in the `C₄`) lies on none: `triAt = 0`. | — |
| `RestrictedTransport.not_tinhoferGraph_kcAdj` | 525-537 | ★★★ **THE CLASS IS PROPER — `K₃ ⊔ C₄` IS NOT TINHOFER.** 2-regular ⟹ the refined root is one cell containing `0` and `3`; but `0` lies on a triangle and `3` does not, so no automorphism carries one to the other. The root already fails `SchurianAt`, and is individualization-reachable by definition. | — |
| `RestrictedTransport.tinhoferGraph_nonvacuous` | 539-549 | ★★★ **BOTH HALVES OF NON-VACUITY** — the shape `Publication.unhandledResidue_nonvacuous` asks for, against the **structural** residue predicate `¬ TinhoferGraph` (a property of the graph, never "the algorithm flagged"): the class is **inhabited** (multipartite) and **proper** (`K₃ ⊔ C₄`). | — |
| `RestrictedTransport.certPath_deepenSupply_of_tinhoferGraph` | 573-593 | On a Tinhofer graph, deepen certifies its own canonical path from every individualization-reachable colouring. ⚠⚠ The hypothesis is `TinhoferGraph` (the **closure** class) and **cannot be weakened to path-local `Deepen.Tinhofer`**: each `CertPath` level demands `CellIsOrbit deepenSupply` — every pair of the cell — while `exec_recovers_refgen_on_cell` supplies one pair per anchor path, so the level needs `Tinhofer` at *that* colouring, which a single path does not give. | — |
| `RestrictedTransport.certifiedG_deepenSupply_of_tinhoferGraph` | 595-599 | ★★ **THE COMPUTABLE CERTIFICATE FIRES EVERYWHERE ON A TINHOFER GRAPH** — `Deepen.CertifiedG Deepen.deepenSupply` (an orbit BFS over deepen's own verified generators) is open at every reachable node. This is the **firing** half of a computable-guard supply. ⚠ It does **not** give `①`: that needs the converse — the guard being open at `(σ adj, σ χ)` whenever open at `(adj, χ)` — which is R1's content. | — |
## ChainDescent/DeepenComplete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.GoodAnchor` | 99-103 | **The per-anchor condition** — `x`'s own canonical deepening individualizes only single-orbit cells. This is the hypothesis `exec_recovers_cell_orbits` actually consumes; the global `Tinhofer` is only its universal closure over the branch cell. | Definition |
| `Deepen.tinhofer_iff_forall_goodAnchor` | 105-108 | `Tinhofer` **is** "every branch-cell anchor is good", by `Iff.rfl` — recorded so the per-anchor form below is visibly the same statement weakened, not a different one. | — |
| `Deepen.exec_recovers_refgen_at` | 115-135 | ★★ **A GOOD ANCHOR RECOVERS ITS WHOLE ORBIT.** `exec_recovers_refgen_on_cell` with the global `Tinhofer adj χ` replaced by `GoodAnchor adj χ x`: deepen connects `x` to `ρ x` for **every** colour-automorphism `ρ`, with no condition on any other anchor. Free — the wrapper only ever used `hAmen x hx`. | — |
| `Deepen.branch_orbit_iff_aut_at` | 137-143 | The branch-orbit characterization **at one good anchor**: soundness (`wordReach_imp_isColAut`) is unconditional; completeness at `u` needs only `u`'s own deepening path. | — |
| `Deepen.OrbitComplete` | 151-156 | ★ **THE TARGET** — *"deepen succeeds whenever success is possible"*: its verified generators realise the whole `IsColAut`-orbit relation on the branch cell. The open half of `deepen_branch_orbit_iff_aut`; the failsafe half holds on every input already. | Definition |
| `Deepen.orbitComplete_of_tinhofer` | 158-162 | `Tinhofer ⟹ OrbitComplete`. ⚠ Not the only sufficient condition — `orbitComplete_of_good_or_trivial` (§5) is strictly weaker and covers the measured all-singleton-orbit case, where there is no good anchor at all. | — |
| `Deepen.branch_orbit_iff_aut_of_orbitComplete` | 164-170 | Under `OrbitComplete` the relation **is** the `IsColAut`-orbit relation — the hypothesis-free form of `deepen_branch_orbit_iff_aut`. | — |
| `Deepen.branchOrbit_transport_of_orbitComplete` | 178-200 | deepen's branch-orbit relation **transports** under global `OrbitComplete`: both sides equal the orbit relation, which conjugates (`isColAut_conj_iff`). Mirrors `deepen_branchOrbit_transport` with `Tinhofer` swapped out. | — |
| `Deepen.deepenSupply_canonizer_of_orbitComplete` | 202-213 | ★★★ **`①c` FOR THE RAW `deepenSupply` FROM `OrbitComplete` ALONE** — no guard, no reference supply, nothing `noncomputable`. This is the shape `R1` was asking for, with the whole obligation concentrated in one predicate. | — |
| `Deepen.OrbitTrivial` | 228-230 | `u` is **`Aut`-rigid** at `χ`: no colour-automorphism moves it, so its orbit in the branch cell is `{u}`. | Definition |
| `Deepen.orbitComplete_of_good_or_trivial` | 232-242 | ★★ **`OrbitComplete` FROM "EVERY ANCHOR GOOD **OR** RIGID"** — strictly weaker than `Tinhofer`, because at a rigid vertex `ρ u = u` and the obligation is `refl`, so the anchor need not be good. Not vacuous: it is exactly the measured `rand multipede V=12 W=8`, which has 0/4 good anchors and is nevertheless exact (all four orbits singletons). | — |
| `Deepen.orbitComplete_of_rigid_cell` | 244-248 | A branch cell all of whose members are `Aut`-rigid is `OrbitComplete` **with no goodness at all** — deepen may certify nothing and still be complete, because there is nothing to certify. | — |
| `Deepen.goodAnchor_transport` | 258-267 | ★ **GOODNESS IS AN ORBIT PROPERTY** — a colour-automorphism carries a good anchor to a good anchor. `tinhoferPath_transport` specialised from a relabelling (which moves the graph) to an automorphism (which does not). Hence §5's hypothesis is decided once per orbit: an orbit is entirely good, entirely bad, or a fixed point. **Confirmed empirically** — `probe_union_need.py` finds no mixed orbit on 13 witnesses. | — |
| `Deepen.not_goodAnchor_transport` | 269-272 | Contrapositive of `goodAnchor_transport` — badness is an orbit property too; the form a probe reads. | — |
## ChainDescent/DeepenTransportOn.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `DeepenTransportOn.NarrowFnEquivariantOn` | 73-76 | `Descend.NarrowFnEquivariant` relativized to (relabelling-closed class) × (reached colourings). | Definition |
| `DeepenTransportOn.CoveringOfAtOn` | 78-86 | `Descend.CoveringOfAt` relativized the same way — the fuel-graded covering, on the class. | Definition |
| `DeepenTransportOn.narrowTransportOn_of_coveringOfAtOn` | 88-106 | ★★ **THE RELATIVIZED SANDWICH** — mirror of `Descend.narrowTransport_of_coveringOfAt`. New consumptions: `RelabelClosed` (σ·adj still in the class) and `reaches_transport` (σ·χ still reached). Also new is `hNsub`: the intermediate must sit inside the branch cell, since the relativized `branchVal_transport_on` needs the child to be reached. | — |
| `DeepenTransportOn.StallEquivariantOn` | 114-117 | `Stall.StallEquivariant` relativized — the flag must fire on both sides together, but only at graphs in the class and colourings the descent reaches. | Definition |
| `DeepenTransportOn.stallEquivariantOn_forceThenConsume` | 119-147 | ★ **THE FLAG IS EQUIVARIANT ON THE CLASS** given branch-orbit transport there. The narrowing reads the supply only through `Consume.rep` on `forcedSet ⊆ branches`, and `rep` there depends only on the branch-orbit relation. Pointwise in `(σ, adj, χ)`, so restricting the hypothesis restricts the conclusion with the proof unchanged. | — |
| `DeepenTransportOn.narrowFnEquivariantOn_guardedRef` | 151-163 | `Residue.narrowFnEquivariant_guardedRef` on the class — the reference is the forced set emptied at a stall, so it transports as soon as the stall predicate does. | — |
| `DeepenTransportOn.guardedRef_subset` | 165-171 | The guarded reference lives inside the branch cell — discharges `hNsub` for the sandwich. | — |
| `DeepenTransportOn.coveringOfAtOn_guarded` | 180-215 | ★ **THE COVERING HALF, UNCONDITIONAL IN THE SUPPLY.** `Residue.coveringOfAt_guarded` with `branchVal_eq_of_isColAut_on`: `Consume` verifies every candidate, so a discarded branch is automorphic to the kept one and they have equal descent values. A broken oracle costs branches, never `①`. (The value lemma is stated for forced-set members rather than all of `Fin n`, since the relativized form needs its vertex in the branch cell; both call sites are at forced-set members.) | — |
| `DeepenTransportOn.narrowTransportOn_guarded` | 217-224 | ★★ **THE CONTRACT ON THE CLASS** for the guarded mixed resolver — the sandwich applied at the guarded reference. | — |
| `DeepenTransportOn.branchOrbit_transport_on` | 228-256 | deepen’s branch-orbit relation transports **on the class** — the relativized `DeepenComplete.branchOrbit_transport_of_orbitComplete`. Both sides equal the `IsColAut`-orbit relation, which conjugates; `OrbitComplete` is consumed at `(adj, χ)` and at `(σ adj, σ χ)`, the latter available from `RelabelClosed` + `reaches_transport`. | — |
| `DeepenTransportOn.narrowTransportOn_deepen` | 258-266 | ★★★ **THE CONTRACT AT `deepenSupply`** on any relabelling-closed class whose reached colourings are `OrbitComplete`. | — |
| `DeepenTransportOn.canonizes_on_orbitComplete` | 268-300 | ★★★ **`①` ON A CLASS FOR THE DEEPEN OBJECT** — sound (unconditional) ∧ complete on the class ∧ the flag is iso-invariant on the class. ⚠ **Not totality**: `OrbitComplete` recovers the orbits, it does not make the cell one orbit, so a cell with `k ≥ 2` orbits narrows to `k` branches and the guard flags — which is exactly what `③` reads. ▶ To widen the class, supply a wider `C`: all that is asked is `RelabelClosed` plus `OrbitComplete` at every reached colouring. | — |
| `DeepenTransportOn.orbitComplete_of_tinhoferGraph` | 310-315 | A Tinhofer graph is `OrbitComplete` at every reached colouring — `indivReach_of_reaches` → `tinhofer_of_stepClosed` → `orbitComplete_of_tinhofer`. | — |
| `DeepenTransportOn.canonizes_on_tinhofer_deepen` | 317-337 | ★★★ **`①` ON THE TINHOFER CLASS AT THE DEEPEN OBJECT** — the companion to `RestrictedTransport.canonizes_on_tinhofer`: same class, but at the object that carries the honest flag and `③`, rather than at the never-flagging `forceThenPick`. | — |
| `DeepenTransportOn.descentCost_deepen_le` | 360-368 | `②` at the deepen object: an explicit polynomial `descentCost` on **every** input, no hypotheses — the guard makes the descent a single path by construction (`SupplyCost.descentCost_guard_mixed_le`). | — |
| `DeepenTransportOn.deepen_object_package` | 370-397 | ★★★ **THE WHOLE PACKAGE AT ONE EXECUTABLE OBJECT** (the wind-down’s option **v**): `①a` sound unconditionally, `①b` complete **on the Tinhofer class**, `②` an explicit polynomial on every input unconditionally, `③` flag ⟹ the input is not Tinhofer. Nothing `noncomputable`. ⚠ The honest reading of `①b`/`①c`: completeness is claimed for pairs whose **left** input is Tinhofer; off the class the object is sound but two non-isomorphic non-Tinhofer graphs are not proved to get different forms. | — |
## ChainDescent/DeepenGuardComplete.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.tinhoferPath_none` | 76-79 | `TinhoferPath` equation lemma: no cell selected ⟹ `True` | — |
| `Deepen.tinhoferPath_cons` | 81-87 | `TinhoferPath` equation lemma: cell `cid`, pick `w` | — |
| `Deepen.cidCell_ne_nil` | 89-99 | A selected cell is a cons (`chooseIdK` names only size-≥2 cells) | — |
| `Deepen.chooseIdK_none_of_discrete` | 107-117 | `Discrete χ ⟹ chooseIdK = none` | — |
| `Deepen.tinhoferPath_fuel_lift` | 119-146 | ★ **Fuel adequacy** — once `n ≤ fuel + ncol`, `TinhoferPath` at that fuel holds at **every** fuel | — |
| `Deepen.tinhoferPath_spread` | 153-166 | ★★ A `TinhoferPath` **spreads across a single-orbit cell** — one member's path is every member's | — |
| `Deepen.tinhofer_of_tinhoferPath` | 170-193 | ★★★ **Path-local ⟹ all-anchors**: `TinhoferPath` at `cur` gives `Tinhofer adj cur.col` | — |
| `Deepen.cellIsOrbit_deepenSupply_of_tinhofer` | 197-208 | `Tinhofer` + `CellSingleOrbit` ⟹ `CellIsOrbit deepenSupply` | — |
| `Deepen.certPath_of_tinhoferPath` | 212-236 | ★★★ `TinhoferPath ⟹ CertPath deepenSupply` | — |
| `Deepen.certifiedG_of_tinhofer` | 238-241 | ★★★ **The poly guard is COMPLETE** — open wherever `Tinhofer` holds | — |
| `Deepen.tinhofer_iff_certifiedG` | 243-246 | ★★★ **`Tinhofer adj χ ↔ CertifiedG deepenSupply adj χ`** — the guard *is* `Tinhofer` | — |
| `Deepen.certifiedG_transport` | 254-257 | ★★★ The guard **transports** — with **no `SupplyEquivariant`** | — |
| `Deepen.certifiedG_transport_iff` | 259-263 | The guard's verdict is relabelling-**invariant**, both directions | — |
| `Deepen.instDecidableCertifiedG` | 267-269 | `CertifiedG` is decidable | Instance |
| `Deepen.deepenSupplyCert` | 271-275 | ★★★ **The EXECUTABLE guarded deepen supply** | Definition |
| `Deepen.deepenSupplyCert_eq_guarded` | 277-282 | `deepenSupplyCert = deepenSupplyGuarded` | — |
| `Deepen.deepenSupplyCert_canonizer` | 284-293 | ★★★ **`①` at a COMPUTABLE object, NO hypothesis** | — |
| `Deepen.not_tinhofer_of_deepenSupplyCert_defers` | 295-305 | `③`-shaped: the executable supply defers ⟹ `¬ Tinhofer` | — |
| `Deepen.goodAnchor_iff_certPath` | 326-330 | — | — |
| `Deepen.instDecidableGoodAnchor` | 332-334 | — | Instance |
| `Deepen.IsolatedBy` | 336-340 | — | Definition |
| `Deepen.instDecidableIsolatedBy` | 342-344 | — | Instance |
| `Deepen.orbitTrivial_of_isolatedBy` | 346-355 | — | — |
| `Deepen.GoodOrIsolated` | 357-362 | — | Definition |
| `Deepen.instDecidableGoodOrIsolated` | 364-367 | — | Instance |
| `Deepen.orbitComplete_of_goodOrIsolated` | 369-376 | — | — |
| `Deepen.goodOrIsolated_of_certifiedG` | 378-383 | — | — |
| `Deepen.InvEquivariant` | 458-462 | A vertex invariant is **relabelling-equivariant** | Definition |
| `Deepen.autInvariant_of_invEquivariant` | 464-470 | Equivariance **implies** §8's `Aut`-invariance | — |
| `Deepen.goodAnchor_relabel` | 472-478 | ★ `GoodAnchor` transports across a relabelling — **unconditionally** | — |
| `Deepen.isolatedBy_transport` | 480-489 | ★ `IsolatedBy` transports **iff `inv` does** | — |
| `Deepen.goodOrIsolated_transport` | 491-499 | ★★★ **The secondary guard IS relabelling-equivariant** | — |
| `Deepen.goodOrIsolated_transport_iff` | 501-509 | The verdict is invariant, both directions | — |
| `Deepen.deepenSupplyGI` | 513-516 | The secondary-guarded deepen supply | Definition |
| `Deepen.verified_GI_of_open` | 518-522 | Guard open ⟹ the supply is raw deepen | — |
| `Deepen.verified_GI_of_shut` | 524-528 | Guard shut ⟹ no generators | — |
| `Deepen.deepen_branchOrbit_transport_GI` | 530-561 | ★★ The branch-orbit relation transports | — |
| `Deepen.deepenSupplyGI_canonizer` | 563-572 | ★★★ `①` for the secondary guard, no hypothesis but `InvEquivariant inv` | — |
| `Deepen.stepSum` | 581-584 | Colour-rank total after individualizing `u` | Definition |
| `Deepen.sum_transportColouring` | 586-589 | Transport permutes positions, not values ⟹ same sum | — |
| `Deepen.invEquivariant_stepSum` | 591-596 | `InvEquivariant` is **inhabited** | — |
| `Deepen.deepenSupplyGI_stepSum_canonizer` | 598-604 | ★★★ A concrete computable canonizer at the secondary guard, **no hypothesis** | — |
## ChainDescent/RecordDeepen.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RecordDeepen.cellResolved_append_right` | 69-72 | — | — |
| `RecordDeepen.handled_append_right` | 74-77 | — | — |
| `RecordDeepen.tinhofer_of_reaches` | 85-89 | — | — |
| `RecordDeepen.certifiedG_of_tinhoferGraph` | 91-95 | — | — |
| `RecordDeepen.verified_deepenSupplyCert_of_certifiedG` | 99-104 | — | — |
| `RecordDeepen.handled_deepenSupplyCert_of_tinhoferGraph` | 111-122 | — | — |
| `RecordDeepen.recordSupplyDeepen` | 126-128 | — | Definition |
| `RecordDeepen.handled_recordSupplyDeepen_of_tinhoferGraph` | 130-134 | — | — |
| `RecordDeepen.handledS_recordSupplyDeepen_of_tinhoferGraph` | 136-140 | — | — |
| `RecordDeepen.answersS_recordSupplyDeepen_of_tinhoferGraph` | 142-148 | — | — |
| `RecordDeepen.not_tinhoferGraph_of_flag_recordDeepen` | 150-158 | — | — |
## ChainDescent/DeepenPair.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.pairStep` | 106-109 | ★ **The depth-2 step** = `step ∘ step`; **IS** the user's twin refinement (`TWIN = BOTH`, proved both ways + 168/168 measured) | Definition; deliberately two `step`s so the whole interface is inherited |
| `Deepen.pairStep_transport` | 113-121 | ★ Equivariance — `step_transport`, twice | Blast radius **zero**; contrast the 13-module interface swap a 2-WL step needs |
| `Deepen.pairStep_isColAut` | 123-128 | ★ `Aut`-stability, for spreading arguments | — |
| `Deepen.ncol_lt_pairStep_of_partners` | 130-142 | ★ Progress: `ncol` rises **twice** per pair step | ⟹ fuel adequacy gets *easier*, not harder |
| `Deepen.pairStep_refines` | 144-149 | Monotonicity — a `pairStep` cell is a subset of the `step` cell | The point of the proposal: finer cells ⟹ `CellSingleOrbit` easier |
| `Deepen.pairStep_refines_step` | 151-155 | The second individualization never coarsens | — |
## ChainDescent/DeepenCell.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Deepen.deepenGensOn` | 78-96 | ★ **The deepening harvest anchored at an ARBITRARY vertex list** — `deepenGens` with `Descend.branches χ` abstracted to a parameter. All hoisting (trap #2) and the `Vector` materialisation (trap #1) preserved. | Definition; the object design `B` is built on |
| `Deepen.deepenGens_eq_deepenGensOn` | 98-101 | The executable supply IS the branch-cell instance — `rfl`, so the two can never drift. | `rfl` |
| `Deepen.deepenGensOn_isColAut` | 108-133 | **Soundness at any anchor list**: every emitted generator is a genuine `IsColAut`. `DeepenCrux.deepenGens_isColAut`'s proof used the anchor list nowhere. | Unconditional |
| `Deepen.mem_deepenGensOn_of` | 140-161 | Forward membership at any anchor list — `DeepenTinhofer.mem_deepenGens_of` with `hr1`/`hrj` weakened from `branches χ` to `cell`. | They only ever fed `List.mem_map.mpr` |
| `Deepen.exists_gen_deepenGensOn` | 169-199 | ★★ **THE CELL-ANCHORED RECOVERY THEOREM** — an automorphism carrying `r₁ ↦ rⱼ` inside `cell`, plus a Schurian path for `r₁`, ⟹ the harvest anchored at `cell` EMITS a generator doing the same. Conclusion is generator-existence, hence supply-agnostic. | `exec_recovers_cell_orbits` with its one branch-cell dependency redirected |
| `Deepen.exists_gen_of_goodAnchor` | 208-222 | ★★★ **THE PER-CELL RECOVERY** — `DeepenComplete.exec_recovers_refgen_at` at an arbitrary same-coloured list. `χ x = χ (ρ x)` is free from `IsColAut`, so nothing about the TARGET cell is needed. | Why the branch cell was never load-bearing |
| `Deepen.deepenSupplyAt` | 226-230 | The deepening supply anchored at the cell of colour `c`. | Definition; same declared flat `n⁶` — `Σ_c m_c² ≤ n²` |
| `Deepen.gens_deepenSupplyAt` | 232-233 | Its generators are the cell-anchored harvest. | `rfl` |
| `Deepen.wordReach_imp_isColAut_any` | 235-245 | Soundness at any verified list, supply-generic (`DeepenTinhofer.wordReach_imp_isColAut` is stated at `deepenSupply`). | — |
| `Deepen.GoodCell` | 247-255 | ★★ **THE PER-CELL GUARD** — every anchor of the cell has a Schurian deepening path. | Definition; decidable + **unconditionally** invariant, both inherited |
| `Deepen.instDecidableGoodCell` | 257-259 | Decidable, via `DeepenGuardComplete.goodAnchor_iff_certPath`. | Instance |
| `Deepen.goodCell_transport` | 261-270 | ★★★ **THE GUARD'S VERDICT TRANSPORTS — UNCONDITIONALLY.** Cells correspond (`cellList_transport_perm`) and goodness transports outright (`goodAnchor_relabel`). ⟹ **no per-cell analogue of `tinhofer_iff_certifiedG` is needed** — the recorded risk dissolved. | The ONLY invariance the design needs |
| `Deepen.goodCell_transport_iff` | 272-278 | Both directions. | — |
| `Deepen.OrbitCompleteAt` | 280-284 | **Orbit completeness AT A CELL** — the per-cell analogue of `OrbitComplete`, and what `cellNarrow`'s length at colour `c` actually needs. | Definition |
| `Deepen.orbitCompleteAt_of_goodCell` | 286-300 | ★★★ **THE GUARD DELIVERS ORBIT COMPLETENESS AT ITS OWN CELL.** | — |
| `Deepen.cellOrbit_iff_aut_of_orbitCompleteAt` | 302-308 | Under the guard the emitted relation on the cell **is** the `IsColAut`-orbit relation: `⊆` unconditional, `⊇` the guard's. | — |
| `Deepen.goodCellCost` | 329-332 | ★ **`W-a`: the guard's own bill** — `≤ n` anchors × one `CertPath` walk of `≤ n` levels (reachability `n⁴` + `stepCost` + one `deepenSupply` call). | Definition |
| `Deepen.deepenCellCost` | 334-336 | The cell-anchored supply's total bill: the harvest's declared flat `n⁶` **plus** the guard. Expands to `n⁸ + 2n⁶ + n⁵`. | Definition |
| `Deepen.goodCellCost_bounds_guard` | 338-354 | ★★ **`W-a`: THE DECLARED GUARD CHARGE DOMINATES THE GUARD'S COST MODEL** — `Σ_{r ∈ cell} certPathCost deepenSupply adj n (step adj χ r) ≤ goodCellCost n`. Billed, not declared: `certPathCost_le` is instantiated at `deepenSupply`'s own bound, so an exponential supply would break it. | Closes the recorded `n⁶`-declared vs `n⁸`-real hole |
| `Deepen.deepenCellSupply` | 356-361 | **The guarded cell-anchored supply** — deepen's generators where the cell's anchors are all good, `[]` where not. Computable. | Definition |
| `Deepen.supplyCost_deepenCellSupply` | 363-367 | The bill is unconditional — the guard runs whether or not it opens, so both branches charge `deepenCellCost n`. | `@[simp]` |
| `Deepen.gens_deepenCellSupply_of_open` | 369-372 | Open ⟹ the generators are the cell-anchored harvest. | — |
| `Deepen.gens_deepenCellSupply_of_shut` | 374-376 | Shut ⟹ no generators. | — |
| `Deepen.verified_deepenCellSupply_of_open` | 378-383 | Open ⟹ the guarded supply IS the cell-anchored one. | — |
| `Deepen.verified_deepenCellSupply_of_shut` | 385-388 | Shut ⟹ `[]`, hence count `= |cell|` on BOTH sides automatically. | Why only the verdict must transport |
| `Deepen.cellOrbit_transport_deepenCellSupply` | 390-423 | ★★★ **THE PER-CELL ORBIT RELATION TRANSPORTS** — open: the relation equals the intrinsic orbit relation, which conjugates; shut: both `[]`, and the guard shuts on both sides together. **No `SupplyEquivariant`, no reference supply, no completeness of deepen.** | This IS `Select.CellOrbitTransport` |
| `Deepen.deepenCellSupplyC` | 431-432 | The cell-indexed deepening supply: each cell judged by descents anchored in itself. | Definition |
| `Deepen.cellOrbitTransport_deepenCellSupplyC` | 434-436 | It satisfies `Select.CellOrbitTransport`. | — |
| `Deepen.deepenCell_canonizer` | 438-449 | ★★★ **`①` FOR THE CELL-INDEXED FUSED OBJECT AT THE GUARDED CELL-ANCHORED SUPPLY** — sound ∧ complete ∧ flag-iso-invariant, no hypothesis beyond the key's. The statement the node-global object provably cannot have (`scratchpad/probe_offbranch2/3.py`). | **The capstone of design `B`** |
| `Deepen.verified_append_deepenCell_of_shut` | 461-466 | Shut ⟹ the append reduces to the left factor. | — |
| `Deepen.cellOrbit_append_iff_aut_of_goodCell` | 468-479 | ★★ On the OPEN side the APPENDED relation **is** the orbit relation on the cell — `⊆` by soundness, `⊇` by the guard. **No property of the left factor is used.** | Why appending is free on the open side |
| `Deepen.cellOrbitTransport_append` | 481-507 | ★★ **THE APPEND CARRIES `CellOrbitTransport`**, given only that the left factor's own relation transports where the guard is shut. | Hypothesis shaped for the `kernelSupply`/`SameOrbits` route (W-d′) |
| `Deepen.cellOrbitTransport_append_of_supplyEquivariant` | 509-516 | The instance for an equivariant left factor — covers `foldSupplyFast ++ deckSupply ++ deck2Supply`. | ⚠ `kernelSupply` is provably NOT `GensEquivariant` |
| `Deepen.deepenCell_append_canonizer` | 518-525 | ★★★ **`①` AT THE APPENDED CELL-INDEXED OBJECT.** | — |

## ChainDescent/SelectCell.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Select.CellSupply` | 61-63 | **A cell-indexed supply**: one supply per cell colour. A `Nat`-indexed family, NOT a new structure — which is why every existing lemma applies verbatim at `S c`. | `abbrev` |
| `Select.ofSupply` | 65-66 | Every cell-agnostic supply lifts, ignoring the cell. `selNode`'s object is this special case. | Definition |
| `Select.cellNarrowC` | 68-72 | **The per-cell narrowing against the cell's OWN generators.** | Definition; `= cellNarrow key (S c) adj χ c` by `rfl` |
| `Select.cellNarrowC_eq` | 74-75 | The `rfl` bridge that makes `SelectNode`'s per-cell lemmas apply unchanged. | `rfl` |
| `Select.cellNarrowC_ofSupply` | 77-78 | At `ofSupply` it is the node-global narrowing. | `rfl` |
| `Select.selColourC` | 80-83 | **The selected colour** — unchanged in SHAPE from `selColour` (least non-singleton colour whose cell narrows to `≤ 1`); only the evidence each cell is judged on has changed. | Definition |
| `Select.selColourC_ofSupply` | 85-86 | At `ofSupply` it is `selColour`. | `rfl` |
| `Select.selColourC_spec` | 88-93 | The committed colour is non-singleton and its cell narrowed. | — |
| `Select.selProbeCostC` | 95-102 | The per-cell probe bill: each cell pays for its own supply evaluation and orbit BFS. | Definition; `Σ_c m_c² ≤ n²` ⟹ inside the flat charge already billed |
| `Select.selNodeC` | 104-113 | ★ **THE CELL-INDEXED FUSED NODE RESOLVER** — same decision procedure as `selNode`, each cell judged by its own generators. `[]` = the true mutual stall. | Definition; just another `NodeRes n`, so `Select.lean`'s spine applies verbatim |
| `Select.selNodeC_children_none` | 115-117 | Stall ⟹ no children. | — |
| `Select.selNodeC_children_some` | 119-123 | Committed ⟹ one child per kept representative. | — |
| `Select.nodeProper_selNodeC` | 125-136 | `NodeProper` for the cell-indexed instance — inherited from `SelectNode` at `S c`. | — |
| `Select.CellOrbitTransport` | 143-150 | ★★★ **THE HYPOTHESIS THAT REPLACES `SupplyEquivariant`** — the emitted orbit relation transports at pairs INSIDE each cell. Strictly weaker: it says nothing about WHICH generators are emitted. | Definition; satisfied by a guarded pair-anchored supply with no equivariance at all |
| `Select.cellOrbitTransport_ofSupply` | 152-157 | **Nothing regresses**: a cell-agnostic equivariant supply satisfies it. | — |
| `Select.wordReach_transport_of_sameOrbits` | 159-170 | ★★ **The `SameOrbits` route to a transporting relation** — the shape `Deepen.cellOrbitTransport_append` asks of its left factor, and the only route open to a supply that is not `GensEquivariant`. `kernelSupply`, hence the whole record supply, enters here. | The generic step behind `W-d′` |
| `Select.cellOrbitTransport_ofSupply_of_sameOrbits` | 172-176 | The cell-agnostic instance, for symmetry with `cellOrbitTransport_ofSupply`. | — |
| `Select.cellNarrowC_length_transport` | 178-209 | ★★ **THE PER-CELL ORBIT COUNT TRANSPORTS** — `cellNarrow_length_transport` with `SupplyEquivariant` swapped for `CellOrbitTransport`; the `keepMin` members it is applied to are inside the cell (`keepMin_subset`), which is why the weaker form suffices. | — |
| `Select.selColourC_transport` | 211-223 | ★ **THE CHOSEN COLOUR TRANSPORTS AS A VALUE** — cell ORDER is invariant (colour values are), each cell's VERDICT is invariant by `CellOrbitTransport`. | The architecture's own reading, machine-checked |
| `Select.nodeTransport_selNodeC` | 231-277 | The node contract for the cell-indexed instance. After the colour is committed everything is supply-free (`aggregate_cellNarrow_eq` at `S c`), matched by `KeyEquivariant` alone. | **The only thing that had to be re-proved** |
| `Select.selNodeC_canonizer` | 279-288 | ★★★ **THE CELL-INDEXED FUSED CANONIZER** — `①a`/`①b`/`①c` from `KeyEquivariant` + `CellOrbitTransport`. **No `SupplyEquivariant` anywhere**, which is what lets a pair-anchored supply enter the fused object at all. | — |
| `Select.selNodeC_canonizer_ofSupply` | 290-297 | Conservativity: at a cell-agnostic equivariant supply it reproduces `selNode_canonizer`. | — |
| `Select.selColourC_none` | 313-326 | The flag fires only at a true mutual stall: NO non-singleton cell narrows to `≤ 1` **on its own generators**. | Mirror of `selColour_none` |
| `Select.selNodeC_children_length_le_one` | 328-336 | **Fan-out `≤ 1` by construction** — a cell is committed to only after it narrowed to `≤ 1`, so the descent is a single path of `≤ n+1` nodes. No hypothesis. | What `②` (plan W-h) will consume |
| `Select.selNodeC_stall_iff` | 338-357 | ★ **THE FLAG SEMANTICS** as a characterization: the cell-indexed resolver emits no child **iff** no non-singleton cell narrows to `≤ 1` against its own generators. | Mirror of `selNode_stall_iff` |
| `Select.NodeResolvedC` | 359-362 | **The cell-indexed capability predicate, per node**: SOME non-singleton cell narrows to `≤ 1` on the evidence of descents anchored **in that cell**. | Definition |
| `Select.HandledSC` | 364-367 | The cell-indexed capability predicate: every reached non-discrete node has a resolvable cell. | Definition |
| `Select.nodeResolvedC_ofSupply` | 369-370 | At a cell-agnostic supply, `NodeResolvedC` is `NodeResolved`. | `Iff.rfl` |
| `Select.handledSC_ofSupply` | 372-373 | At a cell-agnostic supply, `HandledSC` is `HandledS` — so nothing regresses. | `Iff.rfl` |
| `Select.selNodeC_ne_nil_of_nodeResolvedC` | 375-382 | A `NodeResolvedC` node is never a stall. | — |
| `Select.answersSC_of_handledSC` | 384-396 | ★★ **THE ANSWERS THEOREM** for the cell-indexed object — no flag on a `HandledSC` graph. `descendS_ne_none_reaches` is resolver-generic and `nodeProper_selNodeC` was proved in §1, so the stall characterization is the only new ingredient. | Mirror of `answersS_of_handledS` |
| `Select.not_handledSC_if_flagSC` | 398-403 | **`③`'s SHAPE at the cell-indexed object**: the flag names the cell-indexed residue. | Mirror of `not_handledS_if_flagS` |
| `Select.selNodeC_cost_none` | 424-427 | Stall ⟹ the node's bill is the probe alone. | Mirror of `selNode_cost_none` |
| `Select.selNodeC_cost_some` | 429-434 | Committed ⟹ the probe plus the kept representatives' refinements. | Mirror of `selNode_cost_some` |
| `Select.selNodeC_cost_le` | 436-455 | The per-node bill: the probe, plus **at most one** child refinement (the committed cell narrowed to `≤ 1`). | Mirror of `selNode_cost_le` |
| `Select.selProbeBoundC` | 457-461 | The cell-indexed probe budget: `≤ n` cells, each paying for **its own** supply evaluation, candidate filter, per-member key evaluation and per-member orbit BFS. ⚠ Differs from `selProbeBound` by a factor `n` on the supply terms — honestly, since cell `c` really does evaluate `S c`. | Definition |
| `Select.selProbeCostC_le` | 463-495 | The probe bill, given per-cell supply/candidate/key bounds. | Mirror of `selProbeCost_le` |
| `Select.descentCostS_selNodeC_le` | 497-512 | ★★ **`②`, PARAMETRIC, AT THE CELL-INDEXED OBJECT** — fan-out `≤ 1` holds by construction, so this carries **no firing hypothesis**: it bounds answer and flag alike, on every input. | The `selNodeC` half of plan `W-h` |
| `Select.CellProbe` | 533-535 | One cell's probe data: `(colour, gens, verified gens, supply cost)`. | `abbrev` |
| `Select.cellData` | 537-542 | **The shared per-cell table** — every cell's supply evaluated **once** per node. The cell-indexed analogue of `selNodeFast`'s `let sv := S adj χ`; this is what cures trap #2 for `selNodeC`. | Definition |
| `Select.verOf` | 544-548 | Read a cell's verified list off the table. Direct recursion rather than `List.find?`, so the agreement lemma is a three-line induction. ⚠ Returns `[]` off `nsColours χ` — which is why the twin is a proved equation, not `rfl`. | Definition |
| `Select.verOf_cellData` | 562-566 | **The table agrees with the supply on every cell the object ever probes** (`c ∈ nsColours χ`). | — |
| `Select.selColourT` | 568-571 | The selector against the shared table. | Definition |
| `Select.selColourT_cellData` | 573-579 | …and it picks the same colour as `selColourC`, via `mem_nsColours_iff`. | — |
| `Select.selNodeFastC` | 581-595 | ★★ **THE RUNNABLE CELL-INDEXED RESOLVER** — each cell's supply evaluated once (`cellData`), the probe bill read off the same table, children built through `Refine.ColData` so each refinement is forced exactly once. Cures traps #2 and #1. | Definition |
| `Select.cellData_probeCost` | 597-607 | The shared table reproduces `selProbeCostC` exactly — `cellData` is a `map` over the same `nsColours χ` and each summand is definitionally the same. | — |
| `Select.selNodeFastC_eq` | 609-628 | ★★★ **THE RUNNABLE RESOLVER *IS* THE REASONED-ABOUT ONE.** Rewriting with it carries `selNodeC_canonizer`, `descentCostS_selNodeC_le`, `answersSC_of_handledSC` and `not_handledSC_if_flagSC` onto the runnable object verbatim. ⚠ A **theorem**, not `rfl` — contrast `selNodeFast_eq`. | The one place the cell-indexed twin differs from the node-global one |
| `Select.canonFormFastSC?` | 630-633 | **The runnable top-level cell-indexed object** (root colouring materialised once too). | Definition |
| `Select.canonFormFastSC?_eq` | 635-642 | …and it is the reasoned-about one. | — |
| `Select.descentCostSC_fast_eq` | 644-649 | The runnable object's cost is the reasoned-about cost. | — |
## ChainDescent/RecordDeepenCell.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RecordDeepenCell.recordSupplyDeepenC` | 64-68 | ★★★ **THE ENDGAME SUPPLY** — the record supply, plus, per cell, the guarded harvest of descents anchored **in that cell**: `fun c => recordSupplyFast ++ Deepen.deepenCellSupply c`. | Definition |
| `RecordDeepenCell.wordReach_transport_recordSupply` | 77-87 | The record supply's orbit relation transports, via `Kernel.sameOrbits_recordSupply` against the equivariant reference `Kernel.recordRefSupply`. | Stated at the `foldSupply` spelling; `Fold.foldSupplyFast_eq` bridges |
| `RecordDeepenCell.cellOrbitTransport_recordSupplyDeepenC` | 89-103 | ★★ **`W-d′`** — the endgame supply satisfies `Select.CellOrbitTransport`. Open cells get it from the guard (the relation *is* the intrinsic orbit relation, which conjugates); shut cells inherit it from the record supply. | ⚠ `kernelSupply` is provably NOT `GensEquivariant`; `SameOrbits` is the route |
| `RecordDeepenCell.recordDeepenCell_canonizer` | 105-114 | ★★★ **`①` AT THE ENDGAME OBJECT** — sound ∧ complete ∧ flag-iso-invariant, **globally and with no hypothesis**. The statement the node-global object provably cannot have, and which wind-down option (v) proves only on the class. | **The `①` capstone of design `B`** |
| `RecordDeepenCell.goodCell_of_tinhofer` | 118-127 | **The per-cell guard opens at the TARGET cell**, from `Tinhofer` alone — `Deepen.tinhofer_iff_forall_goodAnchor` is `Iff.rfl` and `Select.branches_eq_cellList` identifies the branch list with the target cell. The node-global guard and the target cell's guard are the same statement. | Why the per-cell strengthening costs no coverage on the class `③` is about |
| `RecordDeepenCell.cellIsOrbit_deepenCellSupply_of_schurianAt` | 129-145 | ★★ **THE TARGET CELL IS ONE ORBIT OF ITS OWN GENERATORS** — `RecordDeepen`'s firing lemma with the harvest restricted to the cell: `SchurianAt` supplies the automorphism, `Deepen.orbitCompleteAt_of_goodCell` turns it into a `WordReach` over generators anchored **inside** the cell. | — |
| `RecordDeepenCell.cellIsOrbit_recordSupplyDeepenC_of_schurianAt` | 147-153 | The same at the endgame supply — extra generators can only merge more (`Deepen.cellIsOrbit_append_right`). | — |
| `RecordDeepenCell.handledSC_of_tinhoferGraph` | 155-169 | ★★★ **A TINHOFER GRAPH IS `HandledSC` — for every key.** At every reached non-discrete node the target cell narrows to one branch **on its own evidence**. | The `③` population at the cell-indexed object |
| `RecordDeepenCell.answersSC_of_tinhoferGraph` | 171-177 | ★★ **A TINHOFER GRAPH ANSWERS** at the endgame object. | — |
| `RecordDeepenCell.not_tinhoferGraph_of_flag` | 179-187 | ★★★ **`③` AT THE ENDGAME OBJECT, FOR EVERY KEY** — if the canonizer flags, the input is provably not a Tinhofer graph. This **is** `Publication.residue_if_flag`'s statement, at the object `canonForm?` is to become. | ⚠ `RecordDeepen`'s version is at `selNode` + the node-global supply, which cannot carry `①` |
| `RecordDeepenCell.recordDeepenSupplyBound` | 206-209 | The endgame supply's per-node work bound: the record's four supplies, plus the cell-anchored harvest **and its guard**. | Definition |
| `RecordDeepenCell.recordDeepenGensBound` | 211-212 | …and its candidate-count bound: the record's, plus `≤ |cell|² ≤ n²` twists. | Definition |
| `RecordDeepenCell.gens_deepenGensOn_length_le` | 214-227 | The cell-anchored harvest emits `≤ |cell|² ≤ n²` generators — `TwinFamily.gens_deepenSupply_length_le`'s `flatMap`-of-`filterMap` shape with `cell` in place of `Descend.branches χ`. | — |
| `RecordDeepenCell.gens_deepenCellSupply_length_le` | 229-234 | The same through the guard (shut ⟹ `[]`). | — |
| `RecordDeepenCell.supplyCost_recordSupplyDeepenC_le` | 236-245 | The endgame supply's work bound. ⚠ Rewrites the **outer** append only — `supplyCost_appendSupply` is `@[simp]` and would otherwise descend into `recordSupplyFast`'s own four-way nest. | — |
| `RecordDeepenCell.gens_recordSupplyDeepenC_length_le` | 247-253 | The endgame supply's candidate-count bound; same outer-append caution. | — |
| `RecordDeepenCell.descentCostSC_recordDeepen_le` | 255-267 | ★★ **`②` AT THE ENDGAME OBJECT, PARAMETRIC** — no hypotheses; bounds answer and flag alike, on every input. | — |
| `RecordDeepenCell.costConst` | 275-278 | The coefficient sum of the `②` bound polynomial: **69**. Against `RecordKey.costConst = 57`: **+8** from billing the supply per cell, **+4** from `W-a`'s guard charge. `ring`-checked, not fitted. | Definition |
| `RecordDeepenCell.costDeg` | 280-282 | The degree of the `②` bound polynomial: **13, unchanged** from `RecordKey.costDeg`. `recordKeyBound` already reaches `n^10` through `orbKeyG`'s guard, and the key term sets the degree — so the per-cell factor `n` and the guard charge both land strictly below it. | Definition |
| `RecordDeepenCell.recordDeepenBound_expand` | 284-295 | The `②` bound, expanded — `ring` checks the transcription, so `costConst`/`costDeg` are computed from the object rather than guessed. | — |
| `RecordDeepenCell.descentCostSC_recordDeepen_monomial` | 297-316 | ★★★ **`②` IN THE PUBLICATION SHAPE** — the endgame object runs within `69 * (n + 1) ^ 13` on **every** input, no hypotheses, no flag disjunct. | ⚠ The `(n+1)` shape is required: the `n`-form is false at `n = 0` |
| `RecordDeepenCell.recordDeepenCell_full` | 318-338 | ★★★ **`①` ∧ `②` ∧ `③` AT ONE OBJECT** — every obligation `Publication.lean` states, all properties of the *same* canonizer, all axiom-clean, `①` and `②` unconditional and `③` at the tight residue `¬ TinhoferGraph`. | **What `Publication.canonForm?` is to be repointed at (plan `W-g`)** |
| `RecordDeepenCell.canonFormFast` | 347-349 | **The runnable endgame canonizer** — what `Publication.canonForm?` is to become (plan `W-g`). | Definition |
| `RecordDeepenCell.costFast` | 351-354 | …and its cost — what `Publication.cost` is to become. | Definition |
| `RecordDeepenCell.canonFormFast_eq` | 356-361 | The runnable canonizer is the reasoned-about one. | — |
| `RecordDeepenCell.costFast_eq` | 363-368 | The runnable cost is the reasoned-about cost. | — |
| `RecordDeepenCell.recordDeepenCell_full_fast` | 370-381 | ★★★ **`①` ∧ `②` ∧ `③` AT THE RUNNABLE OBJECT** — `recordDeepenCell_full` transported along `canonFormFast_eq`/`costFast_eq`. Same object, stated at the definitions that actually execute; the exact triple `Publication.canonForm?`/`cost` are to be repointed at. | ⚠ `②`'s degree is a bound from declared flat charges, not a measurement — see `Publication.lean`'s `costConst`/`costDeg` block |
| `RecordDeepenCell.recordDeepenCell_record` | 383-394 | ★★★ **`①` ∧ `③` AT ONE OBJECT**, at the record key — the first time both hold of the same object with `①` **unconditional**. `②` (plan W-h) is the remaining obligation. | ⛔ Not a second-object split: this is the object `canonForm?` is becoming |
