# Public Theorem Index — GraphCanonizationProofs

Index of public Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project (active source), grouped by source file path. Archived counterparts live in `Archive/PublicTheoremIndex.md`.
The Name, Line, and if present "Used By" columns are mantained by GenerateTheoremIndexes.py, Description and notes are manually updated.
## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line. Gaps between theorems represent whitespace or comments.
- **Description**: A short description of what the theorem proves.
- **Notes**: `@[simp]` / `@[ext]` attributes, `private`, instances, or other special properties.

## ChainDescent.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `POE` | 70-74 | Partial-order entries: the three values `less`, `unknown`, `greater` used to populate a `PMatrix`. | Inductive; `deriving DecidableEq, Repr` |
| `neg` | 87-91 | Antisymmetric reverse on a single `POE`: swaps `less` and `greater`, leaves `unknown` fixed. | — |
| `neg_neg` | 93-94 | `neg` is an involution: `neg (neg e) = e`. | `@[simp]` |
| `swap_less` | 103 | `POE.swap .less = .greater` (definitional unfolding of σ-swap). | `@[simp]` |
| `swap_greater` | 104 | `POE.swap .greater = .less` (definitional unfolding of σ-swap). | `@[simp]` |
| `swap_unknown` | 105 | `POE.swap .unknown = .unknown` (definitional unfolding of σ-swap). | `@[simp]` |
| `PMatrix` | 111-112 | The partial-order matrix type: `Fin n → Fin n → POE`. | Definition |
| `swap` | 118-119 | Pointwise σ-swap of a `PMatrix`: swap `less` with `greater` at every entry. | — |
| `swap_swap` | 121-122 | σ-swap is an involution on `PMatrix`: `swap (swap P) = P`. | `@[simp]` |
| `Antisymmetric` | 124-126 | A `PMatrix` is antisymmetric when `P i j = POE.neg (P j i)` for all `i, j`. | — |
| `AdjMatrix` | 135-136 | Locally-defined adjacency matrix on `Fin n`, wrapping a `Fin n → Fin n → Nat` field. | Structure |
| `applyGuess` | 140-147 | Apply a single guess `(a, b, dir)` to `P`: set `P a b := dir` and `P b a := neg dir`, leaving every other entry unchanged. Does not transitively close. | — |
| `applyGuess_swap` | 149-170 | Applying `(a, b, swap dir)` to the σ-swapped matrix equals σ-swapping after `applyGuess P a b dir` (requires `a ≠ b`); the key fact linking the two guess directions. | Key structure |
| `closeStep` | 174-187 | Single-step transitive closure: derive `P i j` from a uniform chain `i → k → j`, with `less`-chain priority over `greater`-chain at tie-breaks. | — |
| `transitiveClose` | 189-193 | Transitive closure of a `PMatrix` by iterating `closeStep` `n*n` times — enough rounds to reach fixpoint. | — |
| `conflictMatrix` | 224-237 | Concrete 4-vertex `PMatrix` witnessing a conflicted pair `(0,1)` carrying both a `less`-chain and a `greater`-chain; used to refute σ-swap commutation. | — |
| `closeStep_keeps_less` | 239-242 | `closeStep` never demotes a decided `less` entry. | — |
| `iterate_closeStep_keeps_less` | 244-254 | Iterating `closeStep` preserves any `less` entry — once decided, frozen. | — |
| `closeStep_swap_false` | 256-265 | Refutation that `closeStep` commutes with σ-swap unconditionally — fails on `conflictMatrix` because the `less`-first tie-break is not σ-symmetric. | Machine-checked refutation |
| `transitiveClose_conflict_less` | 267-274 | Computes that `transitiveClose conflictMatrix 0 1 = .less`. | — |
| `transitiveClose_swap_conflict_less` | 276-284 | Computes that `transitiveClose (swap conflictMatrix) 0 1 = .less` — the σ-swap fails to flip the tie-break. | — |
| `transitiveClose_swap_false` | 286-300 | Refutation that `transitiveClose` commutes with σ-swap unconditionally; uses `conflictMatrix` as a 4-vertex witness. | Machine-checked refutation |
| `Colouring` | 304-305 | A vertex colouring `Fin n → Nat`. | Definition |
| `signature` | 307-313 | Multiset signature of vertex `v` under colouring `χ` and state `(adj, P)`: collects `(χ u, adj.adj v u, P v u)` tuples for all `u ≠ v`. | — |
| `warmRefine` | 393-403 | Warm 1-WL refinement: iterate `refineStep` `n` times starting from `initial`. `noncomputable` (downstream of `Encodable.encode`). | Definition (`noncomputable`) |
| `refineStep` / `refineStep_iff` | ~320-417 | **Concrete (2026-05-30, no longer axioms):** `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)` (own colour + sorted encoded signature = the C# `WarmPartition.RefineRound`); `refineStep_iff` (same colour ⟺ same old colour + same signature) is now a **theorem**. Removes `refineStep`/`refineStep_iff` from the axiom basis project-wide. Helpers: `POE.toNat`(_injective), `encTuple`(_injective), `sigKey`, `sigKey_eq_iff`. | Def + theorem |
| `samePartition` | 407-410 | Two colourings induce the same partition iff their equivalence classes coincide: `χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j` for every `i, j`. | — |
| `refineStep_refines` | 429-434 | Refinement is split-only (one round): if two vertices end up with the same refined colour they had the same old colour. | — |
| `warmRefine_refines` | 436-462 | Warm refinement is split-only: `warmRefine adj P initial v = warmRefine adj P initial w` implies `initial v = initial w`. | — |
| `iterate_closeStep_fix` | 494-500 | Iterating `closeStep` from a fixpoint of itself stays at that fixpoint. | — |
| `cell_split_uniform_false` | 565-590 | Refutation of the original `cell_split_uniform` claim — cell-mates do not in general keep equal signatures after a guess plus TC, witnessed by `witnessP0`. | Machine-checked refutation |
| `refineStep_preserves_singleton` | 612-619 | One refinement round preserves a singleton: if no vertex shares `a`'s colour, none shares it after `refineStep` either. | — |
| `iterate_refineStep_preserves_singleton` | 621-634 | Iterating refinement preserves a singleton for any number of rounds. | — |
| `signature_applyGuess_off` | 636-650 | Off the guessed pair, the guess is invisible: for `x ∉ {a,b}` the signature under `applyGuess P₀ a b dir` equals the signature under `P₀`. | — |
| `signature_eq_of_samePartition` | 652-679 | Signature equality between two vertices is a partition invariant of the colouring: equal partitions give the same signature-equality relation. | — |
| `warm_6_2` | 681-758 | Direction invariance of warm refinement (chain-descent §6.2): with `a, b` `χι`-singletons, warm refinement after `a < b` and after `b < a` induce the same partition. | Key structure; §6.2 invariant |
| `signature_swap` | 762-772 | σ-swapping `P` relabels each signature's `POE` component by the involution `POE.swap`, leaving colour and adjacency components untouched. | — |
| `warmRefine_swap` | 774-816 | Direction-blindness (Q1): warm refinement on `P` and on its σ-swap induce the same partition. | — |
| `warmRefine_applyGuess_swap` | 818-828 | Warm refinement after `a < b` on `P₀` and after `b < a` on the σ-swapped `P₀` induce the same partition (corollary of `applyGuess_swap` and `warmRefine_swap`). | — |
| `applyGuess_comm` | 830-848 | Guesses commute (Q2): writes to disjoint matrix entries from guessing on `{a,b}` and on `{b,c}` commute when `a, b, c` are pairwise distinct. | — |
| `signature_agree_off` | 856-867 | If `P` and `Q` agree on every entry with an endpoint outside `D`, then off `D` they give the same signature. | — |
| `warmRefine_agree_off'` | 869-916 | Composable cross-branch sharing: two matrices agreeing off `D` and `samePartition`-equal starting colourings (whose `D` is all `χ`-singletons) yield the same warm-refined partition. The workhorse that chains across descent levels. | Key structure |
| `warmRefine_agree_off` | 918-952 | Cell partition depends only on the matrix off the decision set `D`: matrices agreeing off `D` (with `D` `χι`-singletoned) yield the same partition. Same-`χι` specialisation of `warmRefine_agree_off'`. | Key structure |
| `PartitionInvariant` | 969-973 | A target-cell selector is partition-invariant when it depends only on the partition the colouring induces, not on raw colour values. | — |
| `target_direction_blind` | 975-984 | For a partition-invariant selector, the target cell chosen after `a < b` equals the target after `b < a`. Base case of the descent-spine induction. | — |
| `target_agree_off` | 986-999 | Target-cell selection composes across descent levels: for a partition-invariant selector and matrices agreeing off a `D`-singletoned decision set, the target cell is the same even when start colourings only agree up to partition. | — |
| `Egnd` | 1028-1029 | The canonical ground set on `Fin n`: ordered pairs `(i, j)` with `i < j`. | — |
| `mem_Egnd` | 1031-1032 | Membership in `Egnd n` is exactly `p.1 < p.2`. | — |
| `Egnd_ne` | 1034-1035 | Pairs in `Egnd n` have distinct endpoints: `p.1 ≠ p.2`. | — |
| `Pof` | 1037-1050 | Commit a set `S ⊆ Egnd n` of pair-guesses into a P-matrix: write `less` at `(u,v) ∈ S` and `greater` at `(v,u)`, leaving other entries unchanged. | Definition (`noncomputable`) |
| `cl` | 1052-1057 | Propagation closure on pair-guesses: canonical pairs whose endpoints get separated by warm refinement after committing `S`. | Definition (`noncomputable`) |
| `SingletonAt` | 1067-1069 | Fresh-colour hypothesis at a pair `p`: both `p.1` and `p.2` are `χι`-singletons. | — |
| `cl_extensive` | 1071-1086 | M1 extensiveness of `cl`: for canonical `S` whose vertices are all `χι`-singletons, every pair in `S` lies in `cl S`. | — |
| `Pof_mono_entry_of_unknown` | 1116-1140 | Entry-wise monotonicity of `Pof` from the all-unknown base: for `S ⊆ T` canonical, each entry of `Pof _ S` is either `unknown` or equal to the corresponding entry of `Pof _ T`. | — |
| `FullyDiscrete` | 1152-1154 | A colouring is fully discrete when every vertex is its own `χι`-singleton. | — |
| `cl_monotone_discrete` | 1156-1173 | M0 trivially holds under `FullyDiscrete`: every canonical pair lies in every `cl S`, so monotonicity is vacuous. | — |
| `TVerticesSingletons` | 1186-1188 | Every endpoint of every pair in `T` is a `χι`-singleton. | — |
| `warmRefine_samePartition_T_individualised` | 1190-1275 | Strong M0: warm refinement under `Pof P₀ S` and `Pof P₀ T` induce the same partition when `S ⊆ T` and every endpoint of every `T`-pair is a `χι`-singleton. | — |
| `cl_monotone_T_individualised` | 1277-1288 | M0 monotonicity of `cl` under the T-individualised hypothesis: `S ⊆ T` implies `cl S ⊆ cl T`. | — |
| `cl_idempotent` | 1314-1328 | M2 idempotence of `cl` under fresh-colour individualisation of `S ∪ cl S`: `cl (cl S) = cl S`. | — |
| `Pof_fs` | 1400-1406 | Finset-based computable analogue of `Pof`: write `less`/`greater` at the committed entries of a `Finset` of pair-guesses. | — |
| `commitsToP` | 1408-1410 | All-unknown-base commits-to-matrix shortcut: `Pof_fs (fun _ _ => .unknown) S`. | — |
| `cl_prov` | 1412-1417 | Provenance closure (TC-based): the canonical pair-guesses whose direction is decided by `transitiveClose` of `commitsToP S`. | — |
| `closeStep_unknown` | 1421-1425 | `closeStep` returns `.unknown` at every entry of the all-unknown matrix. | — |
| `closeStep_unknown_fixpoint` | 1427-1430 | The all-unknown matrix is a fixpoint of `closeStep`. | — |
| `transitiveClose_unknown` | 1432-1444 | `transitiveClose` of the all-unknown matrix is the all-unknown matrix. | — |
| `cl_prov_empty` | 1448-1457 | CL0 for `cl_prov`: `cl_prov ∅ = ∅`. | — |
| `cl_prov_extensive` | 1459-1473 | CL1 for `cl_prov`: for canonical `S`, every commit's direct `less` write survives transitive closure, so `S ⊆ cl_prov S`. | — |
| `cl_prov_M3_false` | 1491-1501 | Refutation of matroid M3 exchange for `cl_prov`: concrete `n=5, S={(1,2),(3,4)}, x=(2,3), y=(1,4)` witnesses M3-premise but fails the conclusion. | Machine-checked refutation via `decide` |
| `hasLessChain` | 1515-1518 | Existence of a `.less`-chain in `P` from `i` to `j` via some intermediate `k` with both edges `.less`. | — |
| `hasGreaterChain` | 1520-1522 | Existence of a `.greater`-chain in `P` from `i` to `j` via some intermediate `k`. | — |
| `CanConsistent` | 1524-1528 | A `PMatrix` is canonical-consistent when every `.less` entry sits at `i.val < j.val` and every `.greater` entry at `i.val > j.val`. | — |
| `LessMono` | 1530-1533 | One-sided `.less`-direction entry-wise monotonicity between two matrices: `P i j = .less → Q i j = .less`. | — |
| `canConsistent_no_conflict` | 1535-1545 | Under canonical-consistency, no pair simultaneously hosts both a `.less`-chain and a `.greater`-chain. | — |
| `commitsToP_classify` | 1547-1564 | Three-way classification of `commitsToP S i j` by `S`-membership of `(i,j)` and `(j,i)`. | — |
| `commitsToP_canConsistent` | 1566-1580 | `commitsToP` of a canonical `S` is canonical-consistent. | — |
| `closeStep_keeps_greater` | 1584-1587 | `closeStep` never demotes a decided `.greater` entry. | — |
| `iterate_closeStep_keeps_greater` | 1589-1599 | Iterating `closeStep` preserves any `.greater` entry — once decided, frozen. | — |
| `closeStep_decided` | 1601-1607 | `closeStep` preserves any decided entry (`.less` or `.greater`). | — |
| `closeStep_unknown_eq` | 1609-1621 | Expansion of `closeStep P i j` when `P i j = .unknown`, exposing the explicit `if`-chain. | — |
| `closeStep_eq_less_iff` | 1623-1657 | Classification: `closeStep P i j = .less` iff `P i j` was already `.less` or it was `.unknown` with a `.less`-chain through some intermediate vertex. | — |
| `closeStep_eq_greater_iff` | 1659-1711 | Classification: `closeStep P i j = .greater` iff `P i j` was already `.greater` or it was `.unknown` with no `.less`-chain but a `.greater`-chain. | — |
| `closeStep_canConsistent` | 1713-1724 | `closeStep` preserves canonical-consistency. | — |
| `iterate_closeStep_canConsistent` | 1726-1734 | Iterating `closeStep` preserves canonical-consistency. | — |
| `transitiveClose_canConsistent` | 1736-1739 | `transitiveClose` preserves canonical-consistency. | — |
| `closeStep_lessMono` | 1741-1767 | Joint inductive step: under canonical-consistency of `Q` and `LessMono P Q`, `closeStep` preserves `.less`-mono. | — |
| `iterate_closeStep_lessMono` | 1769-1778 | Iterating `closeStep` preserves `.less`-mono under joint canonical-consistency. | — |
| `transitiveClose_lessMono` | 1780-1784 | `transitiveClose` preserves `.less`-mono under joint canonical-consistency. | — |
| `commitsToP_lessMono` | 1786-1799 | Base case for CL3: `S ⊆ T` (with both canonical) gives `LessMono (commitsToP S) (commitsToP T)`. | — |
| `cl_prov_monotone` | 1803-1828 | CL3 monotonicity for `cl_prov`: canonical `S ⊆ T` implies `cl_prov S ⊆ cl_prov T`. | — |
| `numUnknown` | 1837-1840 | Number of `.unknown` entries in a `PMatrix` — the strictly-decreasing potential used to bound TC iteration. | — |
| `numUnknown_le` | 1842-1847 | `numUnknown P ≤ n * n`. | — |
| `closeStep_unknown_subset` | 1849-1858 | The unknown-entry set of `closeStep P` is contained in the unknown-entry set of `P`. | — |
| `closeStep_numUnknown_lt` | 1860-1885 | If `closeStep P ≠ P`, then `numUnknown` strictly drops under one closure round. | — |
| `iterate_closeStep_progress` | 1887-1914 | After `k` `closeStep` iterations either a fixpoint has been reached at some step `≤ k`, or `numUnknown` has dropped by at least `k`. | — |
| `transitiveClose_is_fixpoint` | 1916-1966 | After `n*n` iterations of `closeStep`, the result is a fixpoint: `closeStep (transitiveClose P) = transitiveClose P`. | — |
| `transitiveClose_idempotent` | 1968-1974 | TC idempotence: `transitiveClose (transitiveClose M) = transitiveClose M`. | — |
| `cl_prov_canonical` | 1978-1983 | Every pair in `cl_prov S` is canonical (`p.1.val < p.2.val`). | — |
| `commitsToP_cl_prov_lessMono` | 1985-2003 | `commitsToP (cl_prov S)` is `.less`-bounded by `transitiveClose (commitsToP S)` for canonical `S`. | — |
| `cl_prov_idempotent` | 2005-2035 | CL2 idempotence for `cl_prov`: `cl_prov (cl_prov S) = cl_prov S` for canonical `S`. | — |
| `IndivStep` | 2122-2146 | Existential witness of one descent-step individualisation: a new colouring `χ'` that singletons every vertex in target `T` and refines `χ` outside `T`. | Structure; **Key structure** (§15 modelling) |
| `singletons_union` | 2150-2171 | `D`-singletons are preserved across an `IndivStep`: if `χ` singletons every `v ∈ D`, then `χ'` singletons every `v ∈ D ∪ T`. | — |
| `samePartition_of_samePartition` | 2173-2203 | Two `IndivStep`s applied to `samePartition`-equal starting colourings with the same target `T` produce `samePartition`-equal results — inductive engine for the spine theorem. | — |
| `DescentTrace` | 2265-2303 | Inductive predicate: `(D, P, χι)` is reachable by `k` descent steps from `(P₀, χι₀)` using selector `sel`, with each step carrying an `IndivStep` witness and a matrix that agrees with `P₀` off the enlarged decision set. | Inductive; **Key structure** |
| `singletons` | 2307-2324 | Trace invariant: the trace's colouring `χι` singletons every vertex in its accumulated `D`. | — |
| `P_agrees` | 2326-2336 | Trace invariant: the trace's matrix `P` agrees with the root `P₀` on every entry having an endpoint outside `D`. | — |
| `SpineChain` | 2340-2348 | Bundle of a `DescentTrace` together with its derived state `(D, P, χι)`. The spine theorem is branch-independence of two such chains. | Structure |
| `partition` | 2355-2359 | The chain's level-`k` partition: `warmRefine adj chain.P chain.χι`. | Definition (`noncomputable`) |
| `IndivStep.samePartition_het` | 2365-2378 | Heterogeneous variant of `samePartition_of_samePartition` accepting separate targets `T₁, T₂` with an equality hypothesis `T₁ = T₂`. Used at the spine induction's level-`k+1` step. | — |
| `spine_branch_independent` | 2380-2454 | Descent spine theorem (branch independence): any two `DescentTrace`s through `k` levels agree on the accumulated `D` (literal equality) and the level-`k` partition (`samePartition`). | **Key theorem** (§15 spine) |
| `SpineChain.branch_independent` | 2456-2465 | `SpineChain`-wrapper of `spine_branch_independent`: two chains at level `k` share `D` and level-`k` partition. | — |
| `defaultColouring` | 2486-2496 | The level-`k` colouring of the default reference chain: iterate refine-then-individualise (via `IndivStep.default`) starting from `χι₀`, with the matrix held fixed at `P₀`. | Definition (`noncomputable`) |
| `defaultD` | 2498-2507 | The level-`k` decision set of the default chain: accumulate `sel (warmRefine adj P₀ (defaultColouring k))` across all levels. | Definition (`noncomputable`) |
| `defaultTrace` | 2509-2522 | Concrete `DescentTrace` realising the default construction using `IndivStep.default` at every level. | Definition (`noncomputable`) |
| `defaultSpineChain` | 2524-2532 | Concrete reference `SpineChain` at every level, bundling `defaultD`/`P₀`/`defaultColouring`/`defaultTrace`. | Definition (`noncomputable`) |
| `SpineChain.eq_default` | 2534-2545 | Reference corollary of the spine theorem: every `SpineChain` at level `k` shares `D` and level-`k` partition with `defaultSpineChain`. | — |
| `Discrete` | 2569-2572 | A colouring is discrete when every cell is a singleton — equivalently, `χ : Fin n → Nat` is injective. | — |
| `of_samePartition` | 2576-2580 | Discreteness is `samePartition`-invariant: equal partitions transport `Discrete`. | — |
| `warmRefine_preserves` | 2582-2591 | Warm refinement preserves discreteness: if `χ` is injective, so is `warmRefine adj P χ`. | — |
| `SpineChain.IsLeaf` | 2595-2601 | A `SpineChain` reaches a leaf when its level-`k` partition is discrete (every vertex a singleton). | — |
| `SpineChain.isLeaf_iff_default` | 2603-2612 | `IsLeaf` is spine-invariant: a chain is a leaf iff `defaultSpineChain` at the same level is. | — |
| `TargetsNonsingletonCell` | 2616-2622 | Hypothesis on a selector: every returned vertex has a same-colour partner (sel only picks from non-singleton cells). | — |
| `NonemptyOnNonDiscrete` | 2624-2629 | Hypothesis on a selector: `sel χ` is non-empty whenever `χ` is not yet discrete. | — |
| `defaultD_univ_isLeaf` | 2631-2646 | When the accumulated decision set is the full vertex set, the spine partition is discrete — the default chain reaches a leaf. | — |
| `defaultD_grows_if_not_leaf` | 2648-2687 | If the default chain at level `k` is not yet a leaf, then `defaultD` strictly grows from level `k` to `k+1` under the two selector hypotheses. | — |
| `defaultSpineChain_reaches_leaf` | 2689-2728 | Under `TargetsNonsingletonCell` and `NonemptyOnNonDiscrete`, the default descent reaches a leaf within `n` levels. | — |
| `DirAssignment` | 2751-2757 | Order assignment relative to `(P₀, D)`: an antisymmetric matrix agreeing with `P₀` on every entry with an endpoint outside `D`. Models the linear oracle's input shape. | Structure |
| `default` | 2763-2770 | Trivial `DirAssignment`: when `P₀` is antisymmetric, `P₀` itself is a valid order assignment for any `D` (witnesses non-emptiness). | — |
| `samePartition_pair` | 2772-2784 | Any two `DirAssignment`s over the same `(P₀, D)`, refined against a `D`-singletoning colouring, induce the same partition. | — |
| `samePartition_chain` | 2786-2799 | A `DirAssignment` over a chain's `D`, refined against the chain's colouring, induces the chain's partition — the order-label residual is exactly the choice of `DirAssignment`. | — |
| `flipPair` | 2803-2847 | Single-pair direction flip on a `DirAssignment`: negate the `(a, b)` and `(b, a)` entries via `POE.neg`. Generator of the `Z₂` group action on direction choices. | — |
| `eq_of_σ_eq` | 2849-2859 | `DirAssignment` equality is determined by the matrix field — propositional fields are subsumed by proof irrelevance. | `@[ext]` |
| `flipPair_idempotent` | 2861-2870 | `flipPair` is an involution: two applications to the same pair return the original `DirAssignment`. The Z₂ generator squares to identity. | — |
| `flipPair_partition_invariant` | 2872-2882 | Flipping a pair preserves the partition: `σ` and `σ.flipPair a b _ _` share the spine partition. | — |
| `flipPair_comm` | 2884-2908 | Flips on disjoint pairs commute: when `{a,b} ∩ {c,d} = ∅`, the two `flipPair` operations commute (abelianness of the `Z₂^d` action). | — |
| `IsAut` | 2936-2939 | A `Fin n`-permutation `π` is a graph automorphism of `adj` when it preserves adjacency edge-by-edge: `adj.adj (π v) (π w) = adj.adj v w`. | — |
| `labelledAdj` | 2965-2971 | Adjacency matrix relabelled by a permutation `π`: entry `(i, j)` is the original adjacency between `π⁻¹ i` and `π⁻¹ j`. | — |
| `labelledAdj_eq_of_isAut` | 2973-2986 | Automorphisms fix the labelled adjacency: `IsAut π adj` implies `labelledAdj π adj = adj.adj`. | — |
| `isAut_of_labelledAdj_eq` | 2988-2998 | Converse: a permutation preserving the labelled adjacency is an automorphism. | — |
| `vertexRankNat` | 3011-3013 | Strict rank of vertex `v`: the count of vertices `u` with `χ u < χ v`. | — |
| `vertexRankNat_lt_n` | 3015-3029 | `vertexRankNat χ v < n` for every `v` (the rank is a valid `Fin n` value). | — |
| `vertexRank` | 3031-3033 | Vertex rank packaged as `Fin n` via `vertexRankNat_lt_n`. | — |
| `vertexRank_strict_mono` | 3035-3054 | `vertexRank` is strictly monotonic in the colour value: `χ v < χ w` implies `vertexRank χ v < vertexRank χ w`. | — |
| `vertexRank_injective` | 3056-3066 | On a `Discrete` colouring, `vertexRank` is injective. | — |
| `vertexRank_bijective` | 3068-3071 | On a `Discrete` colouring, `vertexRank` is bijective (injective on `Fin n → Fin n` ⇒ bijective). | — |
| `rankPerm` | 3073-3077 | The rank permutation: bijection `Fin n ≃ Fin n` mapping each vertex to its colour-rank, defined on a `Discrete` colouring. | Definition (`noncomputable`) |
| `rankPerm_apply` | 3079-3080 | Unfolding lemma: `rankPerm χ h v = vertexRank χ v`. | `@[simp]` |
| `SpineChain.canonAdj` | 3098-3124 | Leaf canonical adjacency matrix: given a leaf `SpineChain` and a `DirAssignment σ` over its `D`, relabel `adj` by the rank permutation of the warm-refined partition. | Definition (`noncomputable`) |
| `matrixLT` | 3128-3135 | Row-major lex strict-less-than on `n × n` matrices: there is a first cell `(i, j)` where the matrices disagree, and at that cell `M₁ i j < M₂ i j`. | — |
| `matrixLT_irrefl` | 3137-3140 | `matrixLT` is irreflexive: no matrix is `<` itself. | — |
| `matrixLT_asymm` | 3142-3163 | `matrixLT` is asymmetric: `M₁ < M₂` implies `¬ M₂ < M₁`. | — |
| `PMatrix.fintype` | 3167-3172 | `Fintype` instance for `PMatrix n` (built from `Fin n` and `POE` both being `Fintype`). | Instance |
| `fintype` | 3178-3188 | `Fintype` instance on `DirAssignment P₀ D` via injection of the σ-field into the `Fintype` `PMatrix n`. | Instance (`noncomputable`) |
| `relabelMatrix` | 3192-3199 | Relabel a bare `Fin n → Fin n → Nat` matrix by a permutation `π`: new entry `(i,j)` is `M (π⁻¹ i) (π⁻¹ j)`. | — |
| `MatrixLex` | 3201-3206 | `Fin n → Fin n → Nat` viewed under the row-major lex order via nested `Pi.Lex`. | Abbreviation |
| `toMatrixLex` | 3208-3211 | Wrap a matrix into its Lex'd form (identity at runtime — `Lex` is a type synonym). | — |
| `ofMatrixLex` | 3213-3215 | Unwrap a Lex'd matrix back to a plain `Fin n → Fin n → Nat`. | — |
| `ofMatrixLex_toMatrixLex` | 3217-3218 | `ofMatrixLex (toMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_ofMatrixLex` | 3220-3221 | `toMatrixLex (ofMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_injective` | 3223-3227 | `toMatrixLex` is injective. | — |
| `canonFormImages` | 3229-3238 | The Finset of Lex-wrapped `canonAdj` images over all `DirAssignment`s for a leaf chain. | Definition (`noncomputable`) |
| `canonFormImages_nonempty` | 3240-3246 | `canonFormImages chain isLeaf` is non-empty when `DirAssignment P₀ chain.D` is non-empty. | — |
| `canonForm` | 3248-3268 | Canonical leaf adjacency matrix: the lex-min `canonAdj` over all `DirAssignment`s. Requires `Nonempty (DirAssignment P₀ chain.D)`. | Definition (`noncomputable`) |
| `canonForm_mem_image` | 3270-3285 | `canonForm` equals `canonAdj σ` for some `DirAssignment σ` (the lex-min picks an element of the image). | — |
| `canonForm_le_canonAdj` | 3287-3303 | `canonForm` is the lex-minimum: `toMatrixLex (canonForm) ≤ toMatrixLex (canonAdj σ)` for every `DirAssignment σ`. | — |
| `LinearOracleSpec` | 3307-3323 | Linear-oracle interface type: given a leaf chain and a current-branch `DirAssignment`, return either `none` or a verified automorphism of `adj` (bundled as a subtype). | Definition (`Type`) |
| `some_isAut` | 3330-3342 | Soundness (subtype-level): when the oracle returns `some result`, the returned permutation is automatically an automorphism (immediate from the bundled subtype). | — |
| `LeafTwistSpec` | 3344-3361 | Leaf-twist validity spec for the linear oracle: when it returns `some result`, the returned `π` relabels the input branch's canonical adjacency to that of some other `DirAssignment σ'`. | — |
| `individualizedColouring` | 3399-3403 | Fresh-colour individualisation of a vertex set `S`: each `v ∈ S` gets unique colour `v.val + 1`; vertices outside `S` share colour `0`. | — |
| `FixesPointwise` | 3405-3408 | Predicate: permutation `π` fixes every vertex in `S` pointwise (`π v = v` for `v ∈ S`). | — |
| `complement` | 3414-3422 | A pointwise-fixing permutation stabilises the complement setwise: `v ∉ S` implies `π v ∉ S`. | — |
| `individualizedColouring_invariant` | 3426-3435 | An automorphism fixing `S` pointwise preserves the individualised colouring: `χ_S (π v) = χ_S v` for every `v`. | — |
| `signature_invariant_of_isAut` | 3439-3476 | An automorphism preserving `(adj, P, χ)` pointwise preserves the signature multiset for every vertex — reindexing along `π`. | — |
| `refineStep_invariant_of_isAut` | 3478-3491 | An automorphism preserving `(adj, P, χ)` pointwise preserves one round of `refineStep` (follows from signature invariance via `refineStep_iff`). | — |
| `iterate_refineStep_invariant_of_isAut` | 3493-3509 | Iterated refinement preserves automorphism invariance for any number of rounds. | — |
| `warmRefine_invariant_of_isAut` | 3511-3520 | Warm refinement preserves automorphism invariance: if `(adj, P, χ_init)` are all `π`-invariant, so is `warmRefine adj P χ_init`. | — |
| `OrbitPartition` | 3621-3627 | Aut_S orbit relation on vertices: `v ~ w` iff some automorphism of `adj` preserving `P` and fixing `S` pointwise sends `v` to `w`. | — |
| `refl` | 3633-3636 | Reflexivity of `OrbitPartition` (via the identity permutation). | — |
| `symm` | 3638-3653 | Symmetry of `OrbitPartition` (via permutation inverse). | — |
| `trans` | 3655-3670 | Transitivity of `OrbitPartition` (via permutation composition). | — |
| `subset_warmRefine` | 3672-3687 | Trivial direction of the squeeze: orbits refine 1-WL cells — `OrbitPartition v w` implies `warmRefine` colours of `v` and `w` agree. | — |
| `refineStep_iter_le_eq` | 3700-3718 | Refinement is split-only across iterations: equality at iterate `k + d` implies equality at iterate `k`. | — |
| `warmRefine_eq_iter_eq` | 3720-3734 | `warmRefine` equality implies iterate-`r` equality for any `r ≤ n`; bridge from the fixpoint partition to any earlier-round partition. | — |
| `id_of_discrete_invariant` | 3759-3768 | Fact B (pointwise): a `π`-invariant discrete colouring forces `π` to be the identity. | — |
| `aut_trivial_of_discrete_warmRefine` | 3770-3786 | Fact B (CFI): if `warmRefine adj P χ_S` is discrete, then every automorphism preserving `(adj, P)` and fixing `S` pointwise is the identity. | — |
| `orbit_iff_eq_of_discrete_warmRefine` | 3788-3806 | Fact B (partition): at discrete depth, `OrbitPartition adj P S v w ↔ v = w`. | — |
| `CascadesAt` | 3828-3835 | Cascade-at-depth-`k` predicate: some `S` with `S.card ≤ k` makes `warmRefine adj P (individualizedColouring n S)` discrete. | — |
| `cascadesAt_univ` | 3837-3856 | Trivial cascade at depth `n`: taking `S = univ` gives a discrete starting colouring preserved by warm refinement. | — |
| `CascadesAt.mono` | 3858-3863 | Monotonicity: a cascade at depth `k₁` is a cascade at every depth `k₂ ≥ k₁`. | — |
| `theorem_1_HOR_at_depth` | 3876-3899 | If `adj` cascades at depth `k`, some `S` with `S.card ≤ k` makes `warmRefine` discrete and the `Aut_S`-orbit partition equal to the `warmRefine` partition. The load-bearing Tier-1 theorem. | **Key theorem** (Tier 1 HOR) |
| `theorem_1_HOR_at_n` | 3921-3932 | Theorem 1 trivial-bound corollary: every graph admits orbit recovery at depth `n`; axiom-free specialisation of `theorem_1_HOR_at_depth` to `cascadesAt_univ`. | — |
| `theorem_1_HOR` | 3934-3945 | Theorem 1 (legacy existential form): some `S` makes `warmRefine` discrete and orbits equal cells. Axiom-free corollary of `theorem_1_HOR_at_n`. | — |
| `theorem_1_HOR_pointwise` | 3947-3959 | Theorem 1 pointwise corollary: at the cascade depth, every automorphism preserving `(adj, P)` and fixing `S` is the identity. | — |
| `SchemeProfile` | 4010-4026 | Bundle of a v-profile colouring with two structural facts: profile classes equal `Aut_v` orbits (schurian Step 1) and 1-WL refines the profile partition (intersection-number Step 2). | Structure; **Key structure** (Tier 2) |
| `warm_iff_profile` | 4032-4045 | Squeeze for `SchemeProfile`: 1-WL fixpoint partition equals the profile partition. | — |
| `theorem_2_HOR_of_profile` | 4084-4100 | Theorem 2 (assembly form): given a `SchemeProfile` witness at `v`, the 1-WL fixpoint partition at depth 1 equals the `Aut_v`-orbit partition. | — |
| `theorem_2_HOR` | 4102-4118 | Theorem 2 (HOR for schurian scheme graphs): for any graph satisfying `IsSchurianSchemeGraph`, the 1-WL fixpoint partition at depth 1 equals the `Aut_v`-orbit partition. Conditional on the `schurian_scheme_profile_exists` axiom. | **Key theorem** (Tier 2 HOR); axiomatic via `IsSchurianSchemeGraph` |

## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CFIBase` | 51-62 | A **CFI base graph** on `Fin m`: a simple (symmetric, loopless) `AdjMatrix m` with every vertex of degree at least 2 — the structural prerequisite for building CFI gadgets. | Structure |
| `neighbors` | 70-72 | The neighbour set of `v` in the base graph `H`, returned as a `Finset (Fin m)`. | — |
| `degree` | 74-75 | The degree of `v` in the base graph: `(H.neighbors v).card`. | — |
| `mem_neighbors` | 77-80 | Membership characterisation: `w ∈ H.neighbors v ↔ H.adj.adj v w ≠ 0`. | `@[simp]` |
| `degree_ge_two` | 82-83 | The structural CFI invariant: every base vertex has degree at least 2. | — |
| `not_self_mem_neighbors` | 85-89 | No vertex is its own neighbour (looplessness): `v ∉ H.neighbors v`. | — |
| `mem_neighbors_symm` | 91-94 | The neighbour relation is symmetric: `w ∈ H.neighbors v ↔ v ∈ H.neighbors w`. | — |
| `edgeCountOrdered` | 96-98 | Ordered-pair edge count of the base graph, defined as `∑ v, H.degree v`. | — |
| `gadgetSize` | 111-113 | Size of the CFI gadget at base vertex `v`: `2^(degree v − 1) + 2 * degree v`, i.e. even-subset vertices plus endpoint vertices. | — |
| `cfiVertexCount` | 115-117 | Total vertex count of `CFI(H)`, defined as `∑ v, H.gadgetSize v`. | — |
| `gadgetSize_ge_six` | 119-130 | Every CFI gadget contains at least 6 vertices, since `degree v ≥ 2` gives `2^1 + 2*2 = 6`. | — |
| `cfiVertexCount_pos` | 132-139 | The CFI vertex count is positive whenever the base has at least one vertex (`0 < m`). | — |
| `evenSubsetsOfNeighbors` | 147-150 | The `Finset` of even-cardinality subsets of `N(v)`; indexes the subset vertices `a_S^v` of `CFI(H)`. | — |
| `empty_mem_evenSubsetsOfNeighbors` | 152-155 | The empty set belongs to `evenSubsetsOfNeighbors v` (cardinality 0 is even). | — |
| `mem_evenSubsetsOfNeighbors` | 157-161 | Membership: `S ∈ evenSubsetsOfNeighbors v` iff `S ⊆ N(v)` and `S.card` is even (`S.card % 2 = 0`). | `@[simp]` |
| `triangleBase` | 171-182 | The triangle `K_3` as a `CFIBase 3`: the smallest base graph satisfying the degree-≥-2 invariant. | — |
| `triangleBase_degree` | 184-186 | Every vertex of `triangleBase` has degree 2. | — |
| `triangleBase_cfiVertexCount` | 188-190 | `triangleBase.cfiVertexCount = 18` — three gadgets of size 6. | — |
| `SubsetVertex` | 213-215 | Type-level encoding of subset vertices of `CFI(H)`: pairs `(v, S)` where `S ∈ evenSubsetsOfNeighbors v`. | — |
| `EndpointVertex` | 217-220 | Type-level encoding of endpoint vertices of `CFI(H)`: triples `(v, w, b)` with `w ∈ N(v)` and `b : Bool`. | — |
| `CFIVertex` | 222-230 | The vertex type of `CFI(H)`: the sum `SubsetVertex ⊕ EndpointVertex`. | — |
| `triangleBase_cfiVertex_card` | 284-286 | Smoke test: `Fintype.card triangleBase.CFIVertex = 18`, matching `cfiVertexCount`. | — |
| `cfiAdj` | 312-325 | The CFI adjacency function on `CFIVertex H`, returning 0 or 1 according to the subset/endpoint clauses and the untwisted bridge formula. | — |
| `cfiAdj_symm` | 327-346 | `cfiAdj` is symmetric: `H.cfiAdj x y = H.cfiAdj y x`. | — |
| `cfiAdj_loopless` | 348-365 | `cfiAdj` is loopless: `H.cfiAdj x x = 0` for every CFI vertex `x`. | — |
| `cfi_triangle_no_twins` | 397-400 | `CFI(triangle)` has no twin pairs: any two distinct vertices are separated by some vertex adjacent to one but not the other. Confirms CFI's `Z₂` is a global gadget-flip, not a transposition — the twin slice (`cellsAreOrbits_of_twin_cells`) and CFI are complementary abelian classes (kernel `decide`, axiom-clean). | — |
| `cfiAdjMatrix` | 427-437 | The CFI adjacency matrix `AdjMatrix (Fintype.card H.CFIVertex)` obtained by lifting `cfiAdj` through `Fintype.equivFin`. | `noncomputable` |
| `cfiAdjMatrix_symm` | 439-443 | `cfiAdjMatrix` is symmetric. | — |
| `cfiAdjMatrix_loopless` | 445-449 | `cfiAdjMatrix` is loopless. | — |
| `IsCFI'` | 453-473 | Concrete `IsCFI` predicate: a witness that `adj : AdjMatrix n` is the CFI of some base graph `H : CFIBase m`, with the base graph and bijection `Fin n ≃ H.CFIVertex` exposed as data. | Structure |
| `IsCFI'.baseSize` | 475-480 | The number of base graph vertices `h.m` for a CFI witness `h`; the depth-bound API ties `cfi_depth_bound h` to `h.baseSize`. | — |
| `cfiAdjMatrix_is_cfi` | 482-513 | Self-witness: every `H.cfiAdjMatrix` satisfies the `IsCFI'` predicate, with `H` itself as the base. | `noncomputable` |
| `cfi_depth_bound` | 537-551 | Cascade-depth function for CFI graphs, concretely defined as `h.baseSize`. **M1** of Stage 4 — discharges the former `cfi_depth_bound` axiom. | Stage 4 / M1 |
| `cfi_depth_bound_le` | 553-568 | Trivially `cfi_depth_bound h ≤ h.baseSize`, following from the M1 definition. | Stage 4 / M1 |
| `theorem_1_HOR_cfi` | 570-585 | Tier-1 CFI form of Theorem 1: a CFI graph admits orbit recovery at depth `cfi_depth_bound h`. Conditional on the cascade axiom `cfi_cascades_polynomially`. | — |
| `theorem_1_HOR_cfi_baseSize` | 587-603 | Corollary: orbit recovery at depth `≤ h.baseSize`, by combining `theorem_1_HOR_cfi` with `cfi_depth_bound_le`. | — |
| `card_evenSubsetsOfNeighbors` | 685-695 | `(H.evenSubsetsOfNeighbors v).card = 2^(H.degree v − 1)` — the classical identity that a `d`-element set has `2^(d−1)` even-cardinality subsets. | — |
| `card_SubsetVertex` | 697-704 | `Fintype.card H.SubsetVertex = ∑ v, 2^(H.degree v − 1)`. | — |
| `card_EndpointVertex` | 706-715 | `Fintype.card H.EndpointVertex = ∑ v, 2 * H.degree v`. | — |
| `card_CFIVertex` | 717-724 | Cardinality identity: `Fintype.card H.CFIVertex = H.cfiVertexCount` — the abstract `CFIVertex` count matches the gadget-size sum formula. | — |
| `IsCFI'.six_baseSize_le` | 742-770 | Connector: a CFI graph has at least `6 * baseSize` vertices, since each gadget contributes at least 6. | — |
| `theorem_1_HOR_cfi_n_bound` | 772-794 | Corollary: orbit recovery on a CFI graph holds at depth `S.card ≤ n / 6` (encoded as `6 * S.card ≤ n`), strictly tighter than the trivial `≤ n` bound. | — |
| `aEmpty` | 813-818 | The canonical seed vertex `a_∅^v` of `CFI(H)`: the subset vertex at gadget `v` with the empty subset. | — |
| `endpoint` | 820-823 | The endpoint vertex `e^b_{v→w}` of `CFI(H)` at gadget `v`, pointing toward `w ∈ N(v)` with parity bit `b`. | — |
| `cfiAdj_aEmpty_endpoint_false` | 832-837 | `cfiAdj (a_∅^v) (e^0_{v→w}) = 0` — the b=false endpoint is not adjacent to the empty-subset seed. | — |
| `cfiAdj_aEmpty_endpoint_true` | 839-844 | `cfiAdj (a_∅^v) (e^1_{v→w}) = 1` — the b=true endpoint is adjacent to the empty-subset seed. | — |
| `aEmpty_ne_endpoint` | 846-853 | `H.aEmpty v ≠ H.endpoint hw b`: subset and endpoint vertices are distinct (different `Sum` tags). | — |
| `cfiAdj_aEmpty_endpoint_diff_gadget` | 855-868 | Cross-gadget non-adjacency: `cfiAdj (a_∅^v) (e^b_{v'→w}) = 0` when `v ≠ v'`. | — |
| `cfiAdj_bridge` | 870-886 | Bridge adjacency: `cfiAdj (e^b_{v→w}) (e^b_{w→v}) = 1` — same-parity endpoints at neighbouring gadgets pointing toward each other. | — |
| `IsCFI'.seedVertex` | 899-903 | The `Fin n` vertex corresponding to `a_∅^v` (canonical seed at base vertex `v`) for an `IsCFI'` witness. | — |
| `IsCFI'.endpointVertex` | 905-909 | The `Fin n` vertex corresponding to `e^b_{v→w}` for an `IsCFI'` witness, via the bijection `h.e.symm`. | — |
| `e_seedVertex` | 915-919 | Bijection round-trip: `h.e (h.seedVertex v) = h.H.aEmpty v`. | `@[simp]` |
| `e_endpointVertex` | 921-926 | Bijection round-trip: `h.e (h.endpointVertex hw b) = h.H.endpoint hw b`. | `@[simp]` |
| `seedVertex_ne_endpointVertex` | 928-938 | Seed vertices and endpoint vertices are distinct in `Fin n` (their abstract counterparts have different `Sum` tags). | — |
| `adj_seed_endpoint_false` | 953-959 | Fin-n level: `adj (seedVertex v) (endpointVertex v w false) = 0`. | — |
| `adj_seed_endpoint_true` | 961-967 | Fin-n level: `adj (seedVertex v) (endpointVertex v w true) = 1`. | — |
| `adj_endpoint_seed_false` | 969-975 | Symmetric Fin-n form: `adj (endpointVertex v w false) (seedVertex v) = 0`. | — |
| `adj_endpoint_seed_true` | 977-983 | Symmetric Fin-n form: `adj (endpointVertex v w true) (seedVertex v) = 1`. | — |
| `adj_seed_endpoint_diff_gadget` | 985-993 | Cross-gadget Fin-n non-adjacency: `adj (seedVertex v) (endpointVertex v' w b) = 0` when `v ≠ v'`. | — |
| `adj_endpoint_seed_diff_gadget` | 995-1002 | Symmetric cross-gadget non-adjacency: `adj (endpointVertex v' w b) (seedVertex v) = 0` when `v ≠ v'`. | — |
| `adj_bridge` | 1004-1012 | Fin-n bridge adjacency: `adj (endpointVertex v w b) (endpointVertex w v b) = 1` — the bridge edge between mirror endpoints. | — |
| `endpointVertex_ne_bridge` | 1014-1036 | An endpoint and its bridge partner are distinct `Fin n` vertices (their gadget indices `v` and `w` differ by looplessness). | — |
| `individualizedColouring_singleton_self` | 1049-1052 | `individualizedColouring n {seed} seed = seed.val + 1` — the seed gets its own fresh colour. | `@[simp]` |
| `individualizedColouring_singleton_other` | 1054-1058 | For `u ≠ seed`, `individualizedColouring n {seed} u = 0`. | `@[simp]` |
| `individualizedColouring_singleton_self_pos` | 1060-1064 | The seed's colour under a singleton individualization is nonzero. | — |
| `individualizedColouring_singleton_eq_seed_iff` | 1066-1079 | Uniqueness: under `individualizedColouring n {seed}`, `χ u = χ seed ↔ u = seed`. Powers the M2 signature-distinction argument. | — |
| `signature_endpoint_false_ne_true` | 1098-1144 | **M2.4**: signatures of the b=0 and b=1 endpoints at gadget `v` differ under the singleton seed individualization. | M2.4 |
| `refineStep_endpoint_false_ne_true` | 1152-1168 | **M2.5 / M2 headline**: after one `refineStep` round on the singleton seed colouring, the b=0 and b=1 endpoints at gadget `v` toward neighbour `w` get distinct colours. | M2.5 |
| `individualizedColouring_eq_iff_of_mem` | 1185-1201 | Multi-seed uniqueness: for `v ∈ S`, `individualizedColouring n S u = individualizedColouring n S v ↔ u = v`. Generalises the singleton form. | — |
| `allSeeds` | 1207-1214 | Cascade individualization set `{h.seedVertex v : v ∈ Fin h.m}` — one seed per base vertex; the witness `S` in `cfi_cascades_polynomially`. | `noncomputable` |
| `seedVertex_injective` | 1216-1234 | `h.seedVertex` is injective: different base vertices map to different `Fin n` indices. | — |
| `seedVertex_mem_allSeeds` | 1236-1239 | Every `h.seedVertex v` lies in `h.allSeeds`. | — |
| `allSeeds_card` | 1241-1247 | `h.allSeeds.card = h.baseSize` — the cascade individualization has size equal to the base graph. | `@[simp]` |
| `allSeeds_card_le_baseSize` | 1249-1252 | Convenience form: `h.allSeeds.card ≤ h.baseSize`. | — |
| `signature_endpoint_false_ne_true_allSeeds` | 1271-1319 | **M3.B / signature**: same-gadget parity distinction at signature level under `χ_{allSeeds}`. Multi-seed analogue of `signature_endpoint_false_ne_true`. | M3.B |
| `refineStep_endpoint_false_ne_true_allSeeds` | 1321-1335 | **M3.B / refineStep**: under `χ_{allSeeds}`, one `refineStep` round distinguishes b=0 and b=1 endpoints at the same gadget. | M3.B |
| `signature_endpoint_true_inter_gadget` | 1364-1409 | **M3.C / signature**: inter-gadget signature distinction for b=true endpoints at different gadgets under `χ_{allSeeds}`. | M3.C |
| `refineStep_endpoint_true_inter_gadget` | 1411-1429 | **M3.C / refineStep**: under `χ_{allSeeds}`, one `refineStep` round distinguishes b=true endpoints at different gadgets. | M3.C |
| `signature_bridge_step` | 1455-1506 | **M3.D Phase 1 / signature** — generic bridge-propagation signature distinction: given distinguishable bridge partners and a no-match precondition on `ev'`, the signatures of the two endpoints differ. | M3.D Phase 1 |
| `refineStep_bridge_step` | 1508-1532 | **M3.D Phase 1 headline** — generic bridge-propagation step: under the bridge + no-match preconditions, one `refineStep` distinguishes the endpoint pair. The local step iterated by Phase 2. | M3.D Phase 1 |
| `adj_endpointVertex_eq_one_iff` | 1546-1568 | Endpoint-endpoint adjacency characterisation: two endpoints are adj=1 iff they form a bridge pair `v_a = w_b ∧ w_a = v_b ∧ b_a = b_b`. | — |
| `adj_seedVertex_eq_one_iff` | 1570-1645 | Seed-adjacency characterisation: `adj u (seedVertex w) = 1 ↔ u` is a b=true endpoint at gadget `w`. Key structural fact for Phase 2's (P2) verifications. | — |
| `refineStep_endpoint_true_intra_gadget_partner` | 1678-1742 | **M3.D Phase 2.1**: under `χ_1 = refineStep χ_{allSeeds}`, one more `refineStep` distinguishes b=true endpoints at the same gadget toward different partners (round 2). | M3.D Phase 2.1 |
| `subset` | 1767-1772 | The CFI vertex `a_S^v` for an arbitrary even subset `S ⊆ N(v)`; generalises `aEmpty v` (the `S = ∅` case). | — |
| `aEmpty_eq_subset_empty` | 1774-1776 | `aEmpty v` is the empty-subset case of `subset`. | — |
| `cfiAdj_subset_endpoint_same_gadget_true_of_not_mem` | 1778-1788 | `cfiAdj (a_S^v) (e^1_{v→w}) = 1` when `w ∉ S` — a non-saturated subset is adjacent to its b=true endpoints outside `S`. | — |
| `cfiAdj_subset_endpoint_same_gadget_false_of_mem` | 1790-1800 | `cfiAdj (a_S^v) (e^0_{v→w}) = 1` when `w ∈ S` — a subset is adjacent to b=false endpoints at neighbours it contains. | — |
| `cfiAdj_subset_endpoint_diff_gadget` | 1802-1812 | Cross-gadget non-adjacency for subset vertices: `cfiAdj (a_S^v) (e^b_{v'→w}) = 0` when `v ≠ v'`. | — |
| `subset_ne_endpoint` | 1814-1821 | Subset and endpoint vertices are distinct (different `Sum` tags). | — |
| `IsCFI'.subsetVertex` | 1825-1831 | Fin-n level extractor for `a_S^v`: `h.e.symm (h.H.subset hS)`. Generalises `seedVertex v` (the `S = ∅` case). | — |
| `e_subsetVertex` | 1837-1843 | Bijection round-trip: `h.e (h.subsetVertex hS) = h.H.subset hS`. | `@[simp]` |
| `seedVertex_eq_subsetVertex_empty` | 1845-1848 | `seedVertex v` is the empty-subset case of `subsetVertex`. | — |
| `subsetVertex_ne_endpointVertex` | 1850-1858 | Subset and endpoint vertices are distinct in `Fin n`. | — |
| `adj_subsetVertex_endpoint_same_gadget_true_of_not_mem` | 1860-1868 | Fin-n: `adj (subsetVertex hS) (endpointVertex hw true) = 1` when `w ∉ S`. The Phase 2.3 witness adjacency. | — |
| `adj_subsetVertex_endpoint_same_gadget_false_of_mem` | 1870-1878 | Fin-n: `adj (subsetVertex hS) (endpointVertex hw false) = 1` when `w ∈ S`. The Phase 2.2 witness adjacency. | — |
| `adj_subsetVertex_endpoint_diff_gadget` | 1880-1889 | Fin-n cross-gadget non-adjacency for subset vertices: `adj (subsetVertex hS) (endpointVertex hw b) = 0` when `v ≠ v'`. | — |
| `adj_subsetVertex_eq_one_iff` | 1891-1944 | Subset-adjacency characterisation: `adj u (subsetVertex hS') = 1` iff `u` is an endpoint at gadget `v'` with parity-mismatching membership in `S'`. Parallel to `adj_seedVertex_eq_one_iff`. | — |
| `signature_endpoint_b0_ne_b1_general_allSeeds` | 1966-2017 | **M3.B+ / signature**: round-1 signature distinction between a b=0 endpoint at any gadget `v'` and a b=1 endpoint at gadget `v` under `χ_{allSeeds}`. | M3.B+ |
| `refineStep_endpoint_b0_ne_b1_general_allSeeds` | 2019-2033 | **M3.B+ / refineStep**: one `refineStep` round distinguishes a b=0 endpoint at any `v'` from a b=1 endpoint at `v` under `χ_{allSeeds}`. | M3.B+ |
| `signature_subset_step` | 2057-2102 | **Subset step / signature** — generic subset-distinction primitive: given a b=true witness endpoint and a no-match precondition, the χ-signatures of two subset vertices differ. | Phase 2.3 step |
| `refineStep_subset_step` | 2104-2124 | **Subset step / refineStep** — Approach 3 primitive for subset propagation: under the witness + no-match preconditions, one `refineStep` distinguishes two subset vertices. | Phase 2.3 step |
| `signature_subset_inter_gadget_round2` | 2177-2212 | **Phase 2.3 / signature** — under `χ_1 = refineStep χ_{allSeeds}`, subset vertices at different gadgets have differing signatures, provided the LHS has a witness `w ∈ N(v) \ S`. | Phase 2.3 |
| `refineStep_subset_inter_gadget_round2` | 2214-2236 | **Phase 2.3 headline** — subset by gadget at round 2: under `χ_2 = refineStep χ_1`, subset vertices at different gadgets get distinct colours (given a non-saturated LHS subset). | Phase 2.3 |
| `adj_subsetVertex_seedVertex` | 2260-2270 | `adj (subsetVertex hS) (seedVertex w) = 0` — subset and seed vertices are never CFI-adjacent (both are `Sum.inl`). | — |
| `signature_subsetVertex_ne_endpoint_true_allSeeds` | 2272-2318 | **M3.B++ / signature**: round-1 signature distinction between a subset vertex (any gadget, any T) and a b=1 endpoint at gadget `v` under `χ_{allSeeds}`. | M3.B++ |
| `refineStep_subsetVertex_ne_endpoint_true_allSeeds` | 2320-2333 | **M3.B++ / refineStep**: one `refineStep` round distinguishes any subset vertex from a b=1 endpoint at gadget `v` under `χ_{allSeeds}`. | M3.B++ |
| `signature_subsetVertex_ne_endpoint_false_round2` | 2359-2466 | **Cross-type round-2 / signature**: a subset with witness and a b=0 endpoint at any gadget have differing χ_1-signatures. | Phase 2.2 prereq |
| `refineStep_subsetVertex_ne_endpoint_false_round2` | 2468-2485 | **Cross-type round-2 / refineStep**: a subset with witness and a b=0 endpoint at any gadget get distinct χ_2 colours. | Phase 2.2 prereq |
| `signature_endpoint_false_inter_gadget_round3` | 2516-2616 | **Phase 2.2 / signature** — round-3 signature distinction between b=0 endpoints at different gadgets, given a witness subset `a_S^v` with `w ∈ S` and `x ∈ N(v) \ S`. | Phase 2.2 |
| `refineStep_endpoint_false_inter_gadget_round3` | 2618-2645 | **Phase 2.2 headline** — b=0 endpoint inter-gadget distinction at round 3: three `refineStep` rounds on `χ_{allSeeds}` distinguish b=0 endpoints at different gadgets, given the subset witness (requires `deg(v) ≥ 3`). | Phase 2.2 |
| `OddDegree` | 2673-2676 | `OddDegree h`: the base graph of `h` has every vertex of odd degree, ensuring no even subset of `N(v)` saturates to `N(v)`. | OddDegree |
| `exists_witness_of_oddDegree` | 2678-2699 | Under `OddDegree`, every even subset `S ⊆ N(v)` admits a Phase-2.3 witness `y ∈ N(v) \ S`. | OddDegree |
| `exists_phase22_witness` | 2701-2750 | Under `OddDegree`, for any `v ∈ N(w)` there exists a Phase-2.2 witness: an even `S ⊆ N(w)` containing `v` plus an `x ∈ N(w) \ S`. Used by Phase 2.X to instantiate Phase 2.2 at bridge-partner gadgets. | OddDegree |
| `refineStep_endpoint_false_intra_gadget_partner_round4` | 2774-2880 | **Phase 2.X headline** — under `OddDegree`, four `refineStep` rounds on `χ_{allSeeds}` distinguish b=0 endpoints at the same gadget toward different partners. | Phase 2.X / OddDegree |
| `refineStep_subset_intra_gadget_S_round5` | 2906-2991 | **Phase 2.4 headline** — under `OddDegree`, five `refineStep` rounds on `χ_{allSeeds}` distinguish subset vertices `a_S^v` and `a_{S'}^v` at the same gadget when `S ≠ S'`. | Phase 2.4 / OddDegree |
| `cfi_cascades_polynomially_oddDeg` | 3011-3215 | **M4** — discharges `cfi_cascades_polynomially` for the `OddDegree` CFI class: `warmRefine adj P χ_{allSeeds}` is `Discrete` and `CascadesAt adj P (cfi_depth_bound h)` holds (axiom-free, no `5 ≤ n` hypothesis). | Stage 4 / M4 / OddDegree |
| `theorem_1_HOR_cfi_oddDeg` | 3217-3236 | **Theorem 1 (CFI, OddDegree, axiom-free)** — orbit recovery for OddDegree CFI graphs at depth ≤ `h.baseSize`. Conditional only on `OddDegree`; no CFI axioms remain. | Stage 4 / OddDegree; axiom-free |

## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme` | 44-88 | A symmetric association scheme on `Fin n`: a partition of `Fin n × Fin n` into `rank + 1` symmetric relations `R_0, ..., R_rank` (with `R_0` the diagonal) plus well-defined intersection numbers `p^k_{ij}`. | Structure; T2.1 |
| `relOfPair` | 104-106 | The unique relation index `i : Fin (S.rank + 1)` for which `rel i v w = true`, extracted from `rel_partition`. | Noncomputable; §1.1 |
| `rel_relOfPair` | 108-111 | The pair `(v, w)` lies in `R_{relOfPair v w}`. | — |
| `relOfPair_unique` | 113-116 | Uniqueness: any relation containing `(v, w)` is `relOfPair v w`. | — |
| `rel_iff_relOfPair` | 118-121 | Characterisation: `rel i v w = true ↔ i = relOfPair v w`. | — |
| `relOfPair_symm` | 123-128 | `relOfPair v w = relOfPair w v` (relations are symmetric). | — |
| `relOfPair_self` | 130-134 | `relOfPair v v = 0`: the diagonal sits in `R_0`. | — |
| `relOfPair_eq_zero_iff` | 136-144 | Diagonal characterisation: `relOfPair v w = 0 ↔ v = w`. | — |
| `IsSchemeAut` | 166-171 | Scheme automorphism: a permutation of `Fin n` preserving every relation index of `S`. | — |
| `relOfPair_eq` | 196-205 | Scheme automorphisms preserve `relOfPair`: `relOfPair (π v) (π w) = relOfPair v w`. | — |
| `SchurianScheme` | 209-220 | An `AssociationScheme` whose relations are exactly the orbits of `IsSchemeAut` acting diagonally on pairs: any two pairs in the same relation are connected by some scheme automorphism. | Structure; T2.1.b |
| `trivialScheme` | 232-248 | The trivial scheme on `Fin 1` (rank 0, single relation `R_0`); smoke test confirming `AssociationScheme` is inhabited. | §3 |
| `trivialSchurianScheme` | 250-258 | The trivial scheme is schurian: only the identity permutation is needed on `Fin 1`. | §3 |
| `vProfile` | 277-286 | The v-profile colouring: `w ↦ (relOfPair v w).val`, used as a 1-WL-style vertex invariant relative to a fixed individualized vertex `v`. | Noncomputable; T2.2 |
| `vProfile_self` | 292-296 | `vProfile S v v = 0`. | — |
| `vProfile_eq_iff` | 298-301 | `vProfile S v w = vProfile S v u ↔ relOfPair v w = relOfPair v u`. | — |
| `vProfile_eq_zero_iff` | 303-315 | `vProfile S v w = 0 ↔ w = v`: the diagonal-relation form of `relOfPair_eq_zero_iff`. | — |
| `vProfile_ne_self_of_ne` | 317-324 | `v` is a singleton in `vProfile S v ·`: for `w ≠ v`, `vProfile S v w ≠ vProfile S v v`. Matches the `SchemeProfile.v_singleton` field. | — |
| `SchemeOrbitPartition` | 339-343 | The v-stabilized scheme-Aut orbit relation: `SchemeOrbitPartition S v w u` holds when some scheme automorphism with `π v = v` sends `w` to `u`. | §4.1 |
| `vProfile_eq_of_schemeOrbit` | 408-416 | Trivial direction (S1.a packaged): `SchemeOrbitPartition` refines `vProfile`-equality. | — |
| `vProfile_eq_imp_schemeOrbit` | 422-435 | S1.b — under the schurian assumption, two vertices with the same `vProfile` are connected by some scheme automorphism fixing `v`. | — |
| `vProfile_iff_schemeOrbit` | 437-446 | Step 1 of Theorem 2 (combined): profile equality at `v` is exactly v-stabilized scheme-Aut orbit equivalence, for a schurian scheme. | — |
| `SchemeGraph` | 465-474 | A graph derived from an association scheme by designating a set `J ⊆ Fin (rank + 1)` of relation indices as edges, with `0 ∉ J` enforcing looplessness. | Structure; §5 |
| `adj` | 480-483 | The derived adjacency matrix: `(v, w)` is an edge iff `relOfPair v w ∈ J`. | Noncomputable |
| `adj_eq_one_iff` | 485-489 | Adjacency characterisation: `adj v w = 1 ↔ relOfPair v w ∈ J`. | — |
| `adj_eq_zero_iff` | 491-495 | Non-adjacency characterisation: `adj v w = 0 ↔ relOfPair v w ∉ J`. | — |
| `adj_self` | 497-500 | Loopless: `adj v v = 0`. | — |
| `adj_symm` | 502-506 | Symmetric: `adj v w = adj w v`. | — |
| `adj_eq_zero_or_one` | 508-513 | Adjacency takes values in `{0, 1}`. | — |
| `SchurianSchemeGraph` | 537-551 | A `SchemeGraph` together with two schurian properties w.r.t. graph automorphisms: `schurian_transitive` (orbits ⊇ relations) and `isAut_imp_isSchemeAut` (orbits ⊆ relations). | Structure; §6 |
| `relOfPair_aut_eq` | 557-562 | Graph automorphisms of a `SchurianSchemeGraph` preserve `relOfPair`. | — |
| `vProfile_aut_invariant` | 564-569 | Graph automorphisms of a `SchurianSchemeGraph` that fix `v` preserve `vProfile S v ·`. | — |
| `GraphOrbitFixing` | 586-590 | The v-stabilized graph-Aut orbit relation (without P-preservation): some `π ∈ Aut(adj)` satisfies `π v = v` and `π w = u`. | §7 |
| `vProfile_eq_imp_graphOrbit` | 623-632 | Step 1 (forward, graph-Aut terms): vProfile-equality implies graph-orbit equivalence, using `schurian_transitive`. | — |
| `graphOrbit_imp_vProfile_eq` | 634-642 | Step 1 (reverse, graph-Aut terms): graph-orbit equivalence implies vProfile-equality, using `isAut_imp_isSchemeAut`. | — |
| `vProfile_iff_graphOrbit` | 644-652 | Step 1 (graph-Aut combined): vProfile equality iff v-stabilized graph-Aut orbit equivalence — the form that bridges to `OrbitPartition adj P {v}` in T2.M4. | — |
| `individualizedColouring_singleton_eq_v_iff` | 694-707 | `χ_v` uniqueness: `individualizedColouring n {v} u = individualizedColouring n {v} v ↔ u = v`. | — |
| `refineStep_round1_pair_eq` | 709-757 | S2.a round-1 lemma — under `χ_v`, if non-`v` vertices `w, u` get equal colours after one `refineStep`, then `(adj w v, P w v) = (adj u v, P u v)`. | S2.a |
| `refineStep_round1_adj_eq` | 759-767 | S2.a (adj-only specialisation): round-1 equality forces `adj w v = adj u v`. | S2.a |
| `SchemeGraph.refineStep_round1_J_eq` | 769-799 | S2.a for scheme graphs: round-1 equality under `χ_v` forces matching J-class membership of `relOfPair v ·`. | S2.a |
| `iterSignature` | 820-828 | The signature multiset of `w` computed against the iter[k] refinement of `χ_v`. | Noncomputable; §8.b |
| `iter_succ_eq_iff` | 830-841 | Round-by-round unfolding: iter[k+1] equality decomposes into iter[k] equality plus matching iter-k signatures. | — |
| `AssociationScheme.intersectionCount_via_w` | 843-869 | For any pair `(v, w)`, the count of intermediate `u'` with `(v, u') ∈ R_i` and `(w, u') ∈ R_l` equals `intersectionNumber i l (relOfPair v w)`. | — |
| `AssociationScheme.intersectionCount_eq_of_vProfile_eq` | 871-885 | Corollary: if `relOfPair v w = relOfPair v u`, then for every `(i, l)` the intersection counts at `(v, w)` and `(v, u)` coincide. | — |
| `Step2_target` | 894-910 | Step 2 statement (target): for a `SchurianSchemeGraph` and compatible `P`, `warmRefine` cells refine `vProfile` classes. | §8.c |
| `signature_count_eq_card` | 926-937 | Bridge lemma: `Multiset.count t (signature adj P χ w)` equals the cardinality of the matching preimage filter over `u' ≠ w`. | §8.b.2 |
| `signature_eq_card_eq` | 939-952 | Count equality from signature equality: if `signature χ w = signature χ u`, the preimage-filter cardinalities match for every tuple `t`. | — |
| `iter_succ_count_eq` | 954-969 | Iter-round count equality: iter[k+1] equality forces matching counts of intermediate vertices for every (round-k colour, adj-value, P-value) triple. | — |
| `signature_countP_eq_card` | 971-982 | `countP` form of `signature_count_eq_card`: `Multiset.countP p (signature ...)` equals the matching preimage filter cardinality. | — |
| `signature_eq_countP_eq` | 984-994 | Aggregate `countP` equality from signature equality, for any decidable predicate `p`. | — |
| `iter_succ_countP_eq` | 996-1012 | Aggregate iter-round count equality: under iter[k+1] equality, the count of intermediate `u'` whose (iter[k] colour, adj, P) satisfies any decidable `p` matches between `w` and `u`. | — |
| `iter_succ_colour_count_eq` | 1014-1033 | Colour-only specialisation of `iter_succ_countP_eq`: under iter[k+1] equality, the count of intermediate vertices whose round-k colour satisfies `q` matches between `w` and `u`. | — |
| `iter_succ_adj_eq` | 1047-1061 | S2.a lifted to any depth ≥ 1: iter[k+1] equality between two non-`v` vertices forces matching adj-to-`v`. | §8.b.3 |
| `warmRefine_adj_eq` | 1063-1078 | warmRefine version of S2.a: two non-`v` vertices in the same warmRefine cell share adjacency to `v`. | — |
| `SchurianSchemeGraph.warmRefine_J_eq` | 1080-1104 | J-class match from warmRefine equality: two non-`v` vertices in the same warmRefine cell share J-class membership of `relOfPair v ·`. The coarsest non-trivial Step 2 refinement. | — |
| `toSchemeProfile` | 1132-1165 | The `SchemeProfile` constructor: given a `SchurianSchemeGraph`, a P-invariance hypothesis, and a `Step2_target` witness, produces the abstract `SchemeProfile G.adj P v` from `ChainDescent.lean §18.1`. | Noncomputable; T2.M4 |
| `schurian_scheme_profile_exists_of_step2` | 1167-1176 | Packages `toSchemeProfile` as a `Nonempty` existence result, matching the shape of the `schurian_scheme_profile_exists` axiom from `ChainDescent.lean §18`. | T2.M4 |
| `trivialPMatrix` | 1187-1188 | The trivial `PMatrix`: every entry is `POE.unknown`. | §9.1 |
| `trivialPMatrix_invariant` | 1190-1194 | Every permutation preserves `trivialPMatrix`. | — |
| `SchurianSchemeGraph.toSchemeProfile_trivialP` | 1196-1203 | Specialisation of `toSchemeProfile` to the trivial P: the P-invariance hypothesis is discharged automatically, leaving only `Step2_target`. | Noncomputable |
| `IsSchurianSchemeGraph'` | 1221-1227 | Concrete schurian-scheme-graph predicate: `adj` arises as the derived adjacency of some `SchurianSchemeGraph`. | Structure; §9.2 |
| `theorem_2_HOR_concrete` | 1229-1256 | Theorem 2 (HOR for schurian scheme graphs), concrete form: from `IsSchurianSchemeGraph' adj` plus P-invariance plus a `Step2_target` witness, derive the `OrbitPartition ↔ warmRefine` equivalence. | T2.M4 |
| `theorem_2_HOR_concrete_trivialP` | 1258-1271 | `theorem_2_HOR_concrete` specialised to `trivialPMatrix`: the P-invariance hypothesis becomes automatic, leaving only `Step2_target`. | — |
| `trivialSchurianSchemeGraph` | 1285-1297 | The trivial 1-vertex schurian scheme graph (empty edge set, identity automorphism only). | §9.3 |
| `trivialSchurianSchemeGraph_step2` | 1299-1305 | `Step2_target` holds trivially on the 1-vertex scheme: any two vertices in `Fin 1` are equal. | — |
| `theorem_2_HOR_trivial` | 1307-1325 | First fully discharged Theorem 2 instance: for the trivial 1-vertex schurian scheme graph with trivial P, the `OrbitPartition ↔ warmRefine` equivalence holds unconditionally. | — |
| `step2_of_rank_le_one` | 1339-1378 | Step 2 for rank ≤ 1 schurian scheme graphs: `vProfile` takes only the two values `0` (at `v`) and `1` (elsewhere), so warmRefine separation suffices. | §9.4 |
| `theorem_2_HOR_concrete_rank_le_one` | 1380-1392 | Theorem 2 unconditional for rank ≤ 1 schurian scheme graphs (e.g., K_n); combines `step2_of_rank_le_one` with `theorem_2_HOR_concrete`. | — |
| `Step2_at_depth` | 1409-1418 | Depth-parametrised Step 2: iter[k] equality implies `vProfile` equality; a depth-explicit version of `Step2_target`. | §10 |
| `step2_of_step2_at_depth` | 1420-1428 | `Step2_at_depth G P v k` for any `k ≤ n` lifts to `Step2_target G P v` via `warmRefine_eq_iter_eq`. | — |
| `step2_at_depth_zero_of_rank_le_one` | 1430-1463 | Sanity instance: `Step2_at_depth G P v 0` for rank ≤ 1 schurian scheme graphs, the cleaner form of `step2_of_rank_le_one`. | — |
| `ncard_setOf_eq_filter_card` | 1488-1495 | Bridge lemma: for `Fintype` and decidable predicate `p`, `{x | p x}.ncard = (Finset.univ.filter p).card`. Used to bridge `Set.ncard`-based `schemePart_at` to the `Finset.filter.card` form output by `signature_eq_countP_eq`. | — |
| `schemePart_at` | 1497-1521 | Recursive partition predicate at depth `k`: at depth 0, `χ_v`-equality; at depth `k+1`, depth-`k` equivalence plus matching (adj, P, depth-`k` class) counts via `Set.ncard {u' | ...}` (sidesteps `Decidable` instance bridging issues). | Noncomputable; §10.1 |
| `schemePart_at_refl` | 1529-1537 | `schemePart_at G P v k` is reflexive. | §10.2 |
| `schemePart_at_symm` | 1539-1549 | `schemePart_at G P v k` is symmetric. | — |
| `schemePart_at_trans` | 1551-1563 | `schemePart_at G P v k` is transitive. | — |
| `iter_refines_schemePart_at` | 1581-1668 | Inductive refinement: the `iter[k] χ_v` partition refines `schemePart_at G P v k`; the substantive intersection-number induction step of Step 2. | §10.3 |
| `Step2_converges_at` | 1686-1693 | Step 2 convergence at depth `k`: `schemePart_at`-k equivalence implies `vProfile` equality. | §10.4 |
| `step2_of_converges_at` | 1695-1706 | Step 2 from convergence plus the inductive step: `Step2_converges_at G P v k` with `k ≤ n` implies `Step2_target G P v`. | — |
| `step2_converges_at_zero_of_rank_le_one` | 1708-1719 | Sanity check: the convergence framework recovers the rank-≤-1 case at depth 0, where `schemePart_at` reduces to `χ_v`-equality. | — |
| `schemePart_at_one_to_v` | 1737-1787 | **Depth-1 extraction**: for `w, u ≠ v`, `schemePart_at G P v 1 w u` forces `adj w v = adj u v ∧ P w v = P u v`. Was originally blocked by a `Decidable` instance issue; the `Set.ncard` restructure made the proof go through cleanly. | §10.5 |
| `schemePart_at_one_adj_to_v` | 1789-1794 | Depth-1 extraction, adj-only specialization. | — |
| `RelOfPairDetByAdjP` | 1816-1824 | **Depth-1 separation hypothesis**: `(adj v ·, P v ·)` determines `relOfPair v ·` on non-`v` vertices. Sufficient for `Step2_converges_at G P v 1` via the depth-1 extraction. | §10.6 |
| `step2_converges_at_one_of_det` | 1826-1853 | **Step 2 convergence at depth 1 under depth-1 separation**. Reduces to the depth-1 extraction plus the separation hypothesis. | — |
| `relOfPairDetByAdjP_of_rank_le_one` | 1855-1879 | `rank ≤ 1` schurian scheme graphs trivially satisfy depth-1 separation. | — |
| `step2_of_det` | 1886-1896 | `Step2_target G P v` from `RelOfPairDetByAdjP`; lifts depth-1 convergence to the full step-2 target via `step2_of_converges_at`. | §10.7 |
| `theorem_2_HOR_concrete_of_det` | 1898-1908 | **Theorem 2 unconditional under depth-1 separation** (Petersen-class). Plugs `step2_of_det` into `theorem_2_HOR_concrete`. | T2.M4 |
| `AdjSeparatesRelations` | 1931-1935 | Cleaner reformulation of depth-1 separation: `(· ∈ J)` is injective on non-diagonal relations. Equivalent to `RelOfPairDetByAdjP` and decoupled from `P`. | §10.8 |
| `relOfPairDetByAdjP_of_adjSeparates` | 1937-1953 | `AdjSeparatesRelations` implies `RelOfPairDetByAdjP` (transport through adj symmetry + `adj_eq_one_iff`). | — |
| `adjSeparates_of_rank_le_one` | 1955-1966 | `rank ≤ 1` ⇒ `AdjSeparatesRelations` (≤ 1 non-diagonal index, trivially injective). | — |
| `adjSeparates_of_rank_two_J_singleton` | 1968-2012 | **`rank = 2` + `|J| = 1` ⇒ `AdjSeparatesRelations`.** The unique element of `J` distinguishes the two non-diagonal relations. Covers Petersen / Kneser `K(5,2)` / Johnson `J(5,2)`. | — |
| `relOfPairDetByAdjP_of_rank_two_J_singleton` | 2014-2021 | Combined: `rank = 2` + `|J| = 1` ⇒ `RelOfPairDetByAdjP`. | — |
| `theorem_2_HOR_concrete_rank_two_J_singleton` | 2023-2037 | **Theorem 2 unconditional for rank-2 + `|J| = 1` schurian scheme graphs** — covers Petersen, Kneser `K(5,2)`, Johnson `J(5,2)`. Axiom-clean (only `refineStep`/`refineStep_iff` + standard basis). | T2.M4 / headline |
| `Depth2Det` | 2065-2081 | **Depth-2 separation predicate** (§10.9). The depth-2 invariant — adj/`P`-to-`v` plus the depth-1 block-degree vector — determines `relOfPair v ·`. Weaker than `RelOfPairDetByAdjP` (may use block-degrees). | Definition |
| `det2_of_det` | 2083-2090 | Depth-1 separation ⇒ depth-2 separation (ignores block-degrees). Confirms depth-2 subsumes the depth-1 coverage. | — |
| `step2_converges_at_two_of_det2` | 2092-2121 | **Step 2 convergence at depth 2 under depth-2 separation.** The 2nd component of `schemePart_at 2` is the block-degree condition; the 1st yields adj/`P`-to-`v` via `schemePart_at_one_to_v`. | — |
| `step2_of_det2` | 2123-2138 | Lifts `Step2_converges_at … 2` to `Step2_target` (`2 ≤ n`; `n < 2` vacuous via `Fin` subsingleton). | — |
| `theorem_2_HOR_concrete_of_det2` | 2140-2152 | Theorem 2 from depth-2 separation; depth-2 analogue of `theorem_2_HOR_concrete_of_det`. | — |
| `schemePart_at_of_orbit` | 2185-2195 | A v-fixing `P`-preserving automorphism puts `w, u` in the same `schemePart_at k` class (orbit ⟹ `subset_warmRefine` ⟹ iter[k] ⟹ `schemePart_at k`). | — |
| `orbit_of_vProfile_eq` | 2197-2211 | `vProfile`-equality ⟹ `OrbitPartition` (schurian Step 1 gives a v-fixing graph aut; `P`-invariance upgrades it). | — |
| `ncard_eq_sum_POE` | 2213-2228 | P-value fibering of an `ncard`: counting splits over the finitely-many `POE` values of `P x ·`. Drops `P` from a block-degree count to recover an intersection number. | — |
| `IntersectionSeparates` | 2230-2239 | **Intersection-number separation hypothesis**: `intersectionNumber j0 j0 ·` distinguishes the non-edge, non-diagonal relations (the ones adjacency alone cannot). | Definition |
| `depth2Det_of_intersectionSeparates` | 2241-2365 | **Discharges `Depth2Det`** for single-edge (`J = {j0}`) schurian scheme graphs with an edge-neighbour of `v` and intersection-number separation. The `schemePart_at 1` class of an edge-neighbour is exactly `R_{j0}`, so the depth-2 block-degree = `intersectionNumber j0 j0`. | **Key theorem** |
| `theorem_2_HOR_concrete_intersectionSeparates` | 2367-2387 | **Theorem 2 unconditional for single-edge schurian scheme graphs with intersection-number separation** — first genuinely rank-≥-3 coverage (depth-1 insufficient, depth-2 sufficient; e.g. the 7-cycle scheme). Strictly subsumes the rank-2/`|J|=1` case. Axiom-clean. | T2 depth-2 / headline |
| `RelIsolatedAt` | 2415-2422 | **Relation-isolation predicate** (§10.11): relation `l`'s `schemePart_at k` class is exactly `R_l` from `v`. The bootstrap's central object. | Definition |
| `vProfile_imp_schemePart_at` | 2424-2433 | The free ⊇ direction: same relation with `v` ⟹ same `schemePart_at k` class (composes `orbit_of_vProfile_eq` + `schemePart_at_of_orbit`). | — |
| `schemePart_at_le` | 2435-2446 | `schemePart_at` is downward-monotone in the depth. | — |
| `relCommon_eq_intersectionNumber` | 2451-2467 | Common-neighbour count = structure constant: `#{u' : (v,u')∈R_l ∧ (z,u')∈R_m} = p^{relOfPair v z}_{l,m}`. Generalises the depth-2 `hcommon`. | `AssociationScheme` |
| `isolatedCount_eq` | 2465-2521 | **The reusable counting heart**: a depth-`k`-isolated `l` lets `schemePart_at (k+1)` pin the intersection number `p^{·}_{l,j0}` (block-degree into `R_l`, summed over `P`). | **Key theorem** |
| `relIsolatedAt_one_j0` | 2523-2559 | **Base case**: the edge relation `j0` is isolated at depth 1 (⊆ from `schemePart_at_one_to_v` + `|J|=1`, ⊇ from the orbit chain). | — |
| `relIsolatedAt_zero` | 2561-2575 | The diagonal `R_0 = {v}` is isolated at every depth. | — |
| `relIsolatedAt_mono` | 2577-2592 | Isolation is upward-closed in depth (`k ≤ j ≤ n`). | — |
| `relIsolatedAt_succ` | 2594-2642 | **The bootstrap step**: a finset `Iso` of depth-`k`-isolated relations + a separation pinning `i` by `(adjacency, counts into Iso)` ⟹ `i` is isolated at depth `k+1`. | **Key theorem** |
| `convergence_of_all_isolated` | 2644-2653 | All relations isolated at depth `k` ⟹ `Step2_converges_at G P v k` (`schemePart_at k` = `vProfile` partition). | — |
| `theorem_2_HOR_concrete_of_isolation` | 2655-2674 | **Theorem 2 from an isolation chain** — the general engine. An instantiator proves Theorem 2 for any scheme by exhibiting that every relation isolates by depth `k ≤ n` (edge via `one_j0`, deeper via `succ`, lifting via `mono`). Axiom-clean. | T2 general engine |
| `theorem_2_HOR_concrete_intersectionSeparates3` | 2676-2743 | **Theorem 2 for depth-3 single-anchor schemes** (e.g. the 9-cycle) — edge isolates at depth 1, anchor `l0` at depth 2 (by `p^{·}_{j0,j0}`), all relations at depth 3 (by `(adj, p^{·}_{j0,j0}, p^{·}_{l0,j0})`). Reaches rank-≥-4 schemes the depth-2 result cannot. Axiom-clean. | T2 depth-3 / headline |

## ChainDescent/CascadeOracle.lean

The a-priori cascade-oracle Lean contract (plan: `docs/Archive/ChainDescent/chain-descent-cascade-oracle-lean-brief.md`). Builds axiom-clean (only `refineStep`/`refineStep_iff` + Lean foundationals), no `sorry`. Phase A = soundness/validity, Phase B = the completeness reduction (wired to the axiom-free orbit-recovery theorems), Phase C = the residual obligations: verdict iso-invariance is *discharged conditionally* (`verdictIsoInvariant_of_complete` — it reduces to localisation), and localisation is *split* into (1a) bounded-depth recoverability — **proved** on the cascade class (`RecoverableByDepth` + `recoverableByDepth_cfi`/`_scheme`, anchored by `cellsAreOrbits_of_discrete`) — and (1b) intermediate-to-deep bridging, **open but not GI ∈ P** (cascade-class construction correctness). Only general-class completeness is the GI ∈ P obligation. §C.0 also proves the deferred-decisions foundation `real_stays_real`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `mono` | 59-68 | Orbit monotonicity in the fixed set: `S ⊆ S'` and `OrbitPartition adj P S' v w` give `OrbitPartition adj P S v w` (same witness; fixing the larger set pointwise implies fixing the smaller). | Deferred-decisions foundation; axiom-light |
| `real_stays_real` | 70-78 | Contrapositive of `mono`: a real decision (no orbit relation) at `S` stays real at every `S' ⊇ S`. Makes deferring a real decision free. | Deferred-decisions §2 |
| `orbitPartition_of_support_disjoint` | 112-126 | **Support backbone**: a `P`-preserving automorphism `π` whose `π.support` is disjoint from the individualized set `S` (= `π` fixes `S` pointwise) and sends `v→w` witnesses `OrbitPartition … S v w`. Fixing `S` collapses `π` only when `S` meets `supp(π)`. | axiom-light (no `refineStep`) |
| `exists_orbit_witness_of_aut` | 128-138 | **Availability depth**: a symmetry of support `s = |supp π|` keeps its orbit pair `(v, π v)` alive down to `S = (π.support)ᶜ` of size `n − s`. Support-graded bound: full-support (rotations) certifiable only at root, transpositions down to `n−2` (twin end). Availability, not certification (that's 1b). | axiom-light (no `refineStep`) |
| `CascadeOracleSpec` | 140-152 | A-priori cascade-oracle interface type: given a `SpineChain` (internal node, committed path `chain.D`) and reps `v w`, return `none` or a verified automorphism of `adj`. Parallel to `LinearOracleSpec` but not leaf-gated. | Definition (`Type`) |
| `some_isAut` | 3330-3342 | Soundness (subtype-level): when the oracle returns `some result`, the returned permutation is automatically an automorphism (immediate from the bundled subtype). | — |
| `OrbitMapSpec` | 169-181 | Cascade-orbit validity (the `LeafTwistSpec` analogue): a returned merge witnesses `OrbitPartition adj chain.P chain.D v w` — the soundness anchor that justifies pruning. | Definition |
| `merged_sameCell` | 183-194 | A valid (`OrbitMapSpec`) oracle never merges across 1-WL cells: a certified merge forces `v, w` into the same `warmRefine` cell. Via `OrbitPartition.subset_warmRefine`. | — |
| `OrbitRecoverableAt` | 216-225 | Oracle vocabulary for the orbit-recovery squeeze: the `Aut_S`-orbit relation equals the 1-WL cell relation at `S` — so refinement computes orbits and a complete oracle is realizable. | Definition |
| `orbitRecoverable_of_cascade` | 227-235 | General foundation: on the cascade class (`CascadesAt adj P k`), orbits are recoverable at some `S` with `S.card ≤ k`. Re-export of `theorem_1_HOR_at_depth`. | — |
| `orbitRecoverable_cfi` | 237-245 | CFI instance: OddDegree CFI graphs are orbit-recoverable at depth ≤ `cfi_depth_bound h`, via `theorem_1_HOR_cfi_oddDeg`. | axiom-free |
| `orbitRecoverable_scheme` | 247-257 | Scheme instance: rank-2, single-edge-class (`J.card = 1`) schurian scheme graphs are orbit-recoverable at depth 1, via `theorem_2_HOR_concrete_rank_two_J_singleton` (non-trivial cells). | axiom-free |
| `CellsAreOrbits` | 259-272 | The non-trivial half of `OrbitRecoverableAt`: every same-cell pair is a genuine `Aut_S` orbit pair (cells no coarser than orbits). Holds at cascade/discretizing depth, fails at generic intermediate nodes — names exactly the open content of localisation. | Definition |
| `orbitRecoverableAt_iff_cellsAreOrbits` | 274-283 | `OrbitRecoverableAt` decomposes: the orbits-refine-cells half is unconditional (`subset_warmRefine`), so recoverability **is** `CellsAreOrbits` — pinning the localisation obligation to a single implication. | — |
| `cellsAreOrbits_of_discrete` | 285-297 | **The recursion-bottom anchor**: at any discretizing depth, `CellsAreOrbits` holds for free (both cell and orbit relations collapse to equality, Fact B). Shows localisation is *not* GI-hard — the recursion deepens to discreteness where cells = orbits automatically. | axiom-free |
| `refineStep_singleton_pair_eq` | 299-324 | General-singleton round-1 match: if `s` is a `χ`-singleton and `a, b ≠ s` get the same colour after one `refineStep`, they share adjacency and `P`-relation to `s`. Arbitrary-singleton generalisation of `Scheme.refineStep_round1_pair_eq`. | axiom-light |
| `isAut_swap_of_twin` | 326-360 | **A twin pair's transposition is an automorphism**: adjacency-twins `v,w` (`adj v s = adj w s` for all other `s`) of a simple graph (`hsymm`, `hloop`) ⟹ `IsAut (Equiv.swap v w) adj`. The `adj`-only half of the twin swap witness, extracted so the linear oracle builds a `ConfigSwap` from the same twin hypothesis (`LinearOracle.configSwap_of_twin`). | axiom-light |
| `orbitPartition_swap_of_twin` | 362-427 | **Transposition orbit witness from a twin pair** (the support-grading's reconstruction core, extracted from the depth bound): an order-undecided twin pair `v,w ∉ S` (`unknown` between themselves, identical adjacency/`P` to all others) ⟹ the transposition `(v w)` witnesses `OrbitPartition adj P S v w`. Works at **any** support. Consumed by the `Sᶜ.card ≤ 2` endpoint, `cellsAreOrbits_of_twin_cells`, and (via `isAut_swap_of_twin`) the linear oracle. | axiom-light |
| `cellsAreOrbits_of_compl_card_le_two` | 429-543 | **Twin endpoint (`s = 2` end of the support-grading)**: `Sᶜ.card ≤ 2` (i.e. `|S| ≥ n−2`) ⟹ `CellsAreOrbits`. The omitted pair is a twin pair, so the transposition `(v w)` is the orbit witness (via `orbitPartition_swap_of_twin`). With `cellsAreOrbits_of_discrete` pins both ends of the support spectrum. Needs `adj` symmetric+loopless, `P` antisymmetric (simple-graph/partial-order setting). | axiom-light |
| `cellsAreOrbits_of_twin_cells` | 545-601 | **Twin-cells: cells-are-orbits at ARBITRARY support** — the twin-reconstructible slice of localisation obligation 1b. If *every* same-cell distinct pair is an order-undecided twin pair, `CellsAreOrbits adj P S` holds for **any** `S` (no `|Sᶜ|` bound), witness = the transposition. Covers the **genuine-twin / module** abelian regime — **not** CFI, which has no twins (`CFI.cfi_triangle_no_twins`) and routes through general orbit recovery + the gadget twist. Non-twin same-cell case stays open. | axiom-light |
| `orbitRecoverableAt_of_twin_cells` | 603-622 | Oracle-vocabulary form of `cellsAreOrbits_of_twin_cells` (via `orbitRecoverableAt_iff_cellsAreOrbits`): on the twin regime, refinement computes the `Aut_S`-orbit partition at any node with no depth bound. The within-the-wall-boundary half of localisation, discharged. | axiom-light |
| `RecoverableByDepth` | 624-633 | "There is a polynomially bounded depth where cells = orbits" — the oracle-contract cascade-class-membership predicate. The bound carries all content (unbounded form is vacuous). | Definition |
| `recoverableByDepth_of_cascade` | 635-641 | Cascade-class foundation: cascading at depth `k` ⟹ `RecoverableByDepth … k`. Re-export of `theorem_1_HOR_at_depth` via the `CellsAreOrbits` decomposition. | — |
| `recoverableByDepth_cfi` | 643-649 | **(1a) PROVED for CFI** (axiom-free, OddDegree): recoverable by depth `cfi_depth_bound h` (≤ baseSize ≤ n/6). | axiom-free |
| `recoverableByDepth_scheme` | 651-663 | **(1a) PROVED for schemes** (axiom-free, rank 2 / `|J|=1`): recoverable by depth 1 — non-trivially, at the very node the oracle acts on (cells not singletons). | axiom-free |
| `recoverableByDepth_univ` | 665-672 | The unbounded form is vacuous: every graph is recoverable by depth `n` (individualize all → discrete). So only the polynomial bound is cascade-class content. Mirror of `cascadesAt_univ`. | axiom-free |
| `CascadeComplete` | 679-686 | Completeness predicate: the oracle certifies every genuine `OrbitPartition` pair. With `OrbitMapSpec` ⟹ the oracle computes the orbit relation exactly. | Definition |
| `certifies_iff_orbit` | 688-702 | A sound (`OrbitMapSpec`) and complete (`CascadeComplete`) cascade oracle returns `some` for `v, w` iff they share an `Aut_D` orbit. | — |
| `CellComplete` | 704-711 | Cell-completeness: the oracle certifies every pair sharing a 1-WL cell — the refinement-decidable (polynomial) completeness. | Definition |
| `complete_of_cellComplete_recoverable` | 713-726 | The completeness payoff: at an orbit-recoverable node, cell-completeness suffices for orbit-completeness — the hard "certify every orbit map" reduces to the polynomial "certify every same-cell pair". | **Key theorem** |
| `VerdictIsoInvariant` | 773-786 | Verdict iso-invariance (strategy §15 gap 2): the oracle's merge decision depends only on the iso-invariant 1-WL partition (cell-equivalent pairs get the same answer). Partition-determined form. **Derivable** — see `verdictIsoInvariant_of_complete`. | Definition |
| `cascadeComplete_of_localization` | 788-799 | Capstone: cell-completeness plus all-nodes-recoverable gives `CascadeComplete`. Names the (open) localisation obligation as its two sufficient hypotheses. | — |
| `cascadeComplete_of_cellsAreOrbits` | 801-812 | Sharpened capstone: cell-completeness plus `CellsAreOrbits` at every node gives `CascadeComplete`. Same strength as `cascadeComplete_of_localization` (via the iff) but states the hypothesis as the single genuinely-open implication. | — |
| `verdictIsoInvariant_of_complete` | 814-829 | **Phase C obligation 3, discharged conditionally**: a sound + complete oracle at orbit-recoverable nodes is automatically `VerdictIsoInvariant` — its verdict equals the orbit relation (`certifies_iff_orbit`) which equals the iso-invariant cell relation. Iso-invariance ⊆ localisation, not independent. | **Key theorem** |
| `computes_orbits_of_complete` | 831-843 | Capstone: a sound + complete oracle computes the `Aut_D`-orbit relation exactly (program-level correctness, conditional on the completeness obligation). | — |

## ChainDescent/LinearOracle.lean

The linear-oracle / abelian-stripping work (tractable-buildout B2; plan + status in `docs/chain-descent-linear-oracle.md` §8.2). Built on the §15.8 scaffolding (`DirAssignment`/`flipPair`/`LinearOracleSpec`/`LeafTwistSpec`/`canonAdj`). Builds axiom-clean (`refineStep`/`refineStep_iff` + foundationals), no `sorry`. **B2 soundness core DONE 2026-05-30:** §L.1 soundness anchor, §L.2 the *forced* candidate twist (rank rebasing — the construction is determined, not searched; the `canonAdj_rebase` bridge), §L.3 abelian `Z₂^d` structure. Remaining: `canonForm` lex-min tie (needs descent-with-pruning model), completeness, lifting twists to subgroup `N` (Part A).

### §L.1 — Soundness anchor (B2.1)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RealizesFlip` | 52-61 | The precise relation "twist `t` relabels branch `σ`'s leaf to the flipped branch `flipPair σ a b`'s leaf" (`relabelMatrix t (canonAdj σ) = canonAdj (flipPair σ a b)`). The `LeafTwistSpec` conclusion with the partner branch pinned to the flip. | Definition |
| `TwistWitness` | 63-83 | The verified data a twist discovery produces: decided pair `(a,b)`, candidate permutation `t`, its `IsAut` proof (the §4.5 edge-check — sole soundness anchor), and a `RealizesFlip` proof. | Structure |
| `twistOracle` | 85-95 | A concrete `LinearOracleSpec` instance parameterised by an abstracted `discover` function (canonical-id matching, C#-side). Returns the verified automorphism on a `TwistWitness`, `none` otherwise; verification is inside the witness so every output is a genuine automorphism. | Definition |
| `twistOracle_leafTwist` | 97-116 | **B2.1 discharge**: `twistOracle` satisfies `LeafTwistSpec`, with the flipped branch as the **explicit** witness `σ' = flipPair σ` (sharper than the bare existential). Closes the §2.3 pruning-justification contract modulo discovery. | **Key theorem**; axiom-light |

### §L.2 — The forced candidate twist (B2.2 + most of B2.3)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `relabelMatrix_labelledAdj` | 141-150 | Relabelling composes: `relabelMatrix t (labelledAdj s adj) = labelledAdj (t * s) adj` — the `Equiv.Perm` group action on labelled matrices. | axiom-light |
| `canonAdj_eq_labelledAdj` | 152-157 | `canonAdj σ = labelledAdj (rankPerm π_σ) adj` for any discreteness proof (rank perm is proof-irrelevant); `rfl`. | axiom-light |
| `canonAdj_rebase` | 159-174 | **The bridge (B2.3 core)**: relabelling `σ`'s canonical leaf by the rank rebasing `rankPerm π_{σ'} * (rankPerm π_σ)⁻¹` gives `σ'`'s leaf. General over branches; the flip is the `σ' = flipPair σ` instance. | **Key theorem**; axiom-light |
| `branch_discrete` | 176-182 | A branch's warm-refined colouring is discrete at a leaf (`samePartition_chain` + `isLeaf`), derived as `canonAdj` derives it. | axiom-light |
| `candidateTwist` | 184-192 | **The forced candidate**: the rank rebasing `rankPerm π_flip * (rankPerm π_σ)⁻¹`. The twist is determined, not searched. | Definition (`noncomputable`) |
| `candidateTwist_realizesFlip` | 194-201 | The forced candidate **always** realises the flip (`canonAdj_rebase` at the flip). Construction is forced — no ambiguity. | **Key theorem**; axiom-light |
| `candidateTwist_unique` | 203-215 | Determinacy: the candidate is the unique perm rank-aligning `σ` to the flipped branch — the iso-invariance gate (§15 gap 2) at the leaf level. | axiom-light |
| `twistWitness_of_isAut` | 217-234 | The oracle reduces to verification: a verified-automorphism candidate yields a complete `TwistWitness`. Discovery = one decidable edge-check on the forced candidate. | Definition (`noncomputable`) |
| `canonicalTwistOracle` | 235-249 | A **fully concrete** `LinearOracleSpec`: for the selected pair, compute the forced candidate, return it iff `IsAut` verifies. Only abstracted piece = pair selection (which decision — soundness-irrelevant). | Definition (`noncomputable`) |
| `canonicalTwistOracle_leafTwist` | 251-259 | `canonicalTwistOracle` satisfies `LeafTwistSpec` (it is a `twistOracle`) — a concrete verified linear oracle, sound by construction. | **Key theorem**; axiom-light |

### §L.3 — Abelian structure (B2.4, partial)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `candidateTwist_flip_inv` | 282-291 | The twist is a `Z₂` involution at the twist level: the forced candidate for the flip-back is the inverse of the candidate for the flip. With `DirAssignment.flipPair_comm` (commuting flips) = the elementary-abelian `Z₂^d` structure of the residual. | axiom-light |

### §L.4 — Completeness / effectiveness (when the oracle fires)

Characterizes *when* the oracle fires and proves firing is semantically justified. The
oracle is complete exactly on the **abelian regime** (forced candidate ∈ Aut) — the
calculator §6 boundary; the general converse fails (conjugation gap). The
abelian-sufficiency lemma (forced candidate IsAut for genuine abelian flips, via
`warm_6_2` rank machinery) is the open core scoped in the §L.4 doc-comment.

| Name | Description | Notes |
|------|-------------|-------|
| `candidateTwist_mul_rankPerm` | 319-327 | The forced candidate satisfies the rank-alignment equation `candidate · π_σ = π_flip`. | axiom-light |
| `isAut_candidateTwist_iff_aligned` | 329-344 | **Firing characterisation**: `IsAut candidate ⟺ ∃ g ∈ Aut(adj)` rank-aligned (`g · π_σ = π_flip`). Forward = the candidate; backward = `candidateTwist_unique`. | **Key**; axiom-light |
| `RealizableFlip` | 346-352 | The decision is a genuine `Aut(adj)` symmetry: some automorphism realises the flip (branches isomorphic). | Definition |
| `realizableFlip_of_isAut_candidateTwist` | 354-365 | **Firing is semantically justified**: when the forced candidate verifies, the branches are genuinely `Aut(adj)`-equivalent (candidate is the witness). Pruning reflects a real symmetry. | axiom-light |
| `canonicalTwistOracle_isSome_iff` | 367-383 | **The oracle fires ⟺ forced candidate is an automorphism** (given the pair selector returns `(a,b)`). The whole completeness question = one decidable edge-check. | **Key**; axiom-light |
| `candidateTwist_flipBack_isAut` | 385-396 | **`Z₂`-direction-consistency**: firing on `σ → flip` forces firing on the flip-back `flip → σ` (its inverse, via `candidateTwist_flip_inv` + `IsAut.symm`). | axiom-light |

### §L.5 — Toward abelian sufficiency (partial)

The open core of completeness — *forced candidate ∈ Aut for abelian decisions* — needs
gadget-level rank-alignment (at a leaf both branches are discrete, so `warm_6_2`'s
partition equality is vacuous; the content is in the rank order). Provable progress:

| Name | Description | Notes |
|------|-------------|-------|
| `rankPerm_comp` | 421-441 | **Rank reindexing**: `rankPerm (χ ∘ e) = rankPerm χ · e` (relabelling conjugate-shifts the rank perm). Pure `Finset.card` reindex. The precise reason colouring-alignment gives a *conjugate* of the realizing aut, not the forced candidate — the conjugation gap. | axiom-light (`propext, Quot.sound`) |
| `candidateTwist_eq_one_of_rankPerm_eq` | 443-454 | **Absorbed decision**: equal leaf rank-perms ⟹ forced candidate `= 1`. | axiom-light |
| `isAut_candidateTwist_of_rankPerm_eq` | 456-464 | The absorbed decision fires (candidate `= 1 ∈ Aut`) — the degenerate genuine abelian instance (branches give the identical canonical leaf). | axiom-light |

### §L.7 — The CFI bridge (M1b): candidate as a conjugate of a graph automorphism

Now that `refineStep` is concrete, the cross-config transport (`§16.2b` in ChainDescent.lean)
lets us express the forced candidate via a *real* automorphism. A **config-swap** `g` carries the
σ-branch config onto the flip-branch config; it forces `π_σ = π_flip · g`, so the candidate is the
`π_σ`-conjugate of `g⁻¹`. This reduces the opaque `IsAut candidate adj` to the structural gadget
rank-alignment, isolating the genuine CFI nut (shared with Tier-3a B1 `hwit`): (1) a config-swap
exists, (2) its `π_σ`-conjugate is an automorphism.

| Name | Description | Notes |
|------|-------------|-------|
| `vertexRank_comp` | 603-621 | `vertexRank (χ ∘ g) v = vertexRank χ (g v)` — pure `Finset.card` reindex along `g`. | axiom-light |
| `ConfigSwap` | 623-635 | An automorphism carrying σ-config onto flip-config (`IsAut`, fixes `χι`, `(flipPair σ).σ (g·)(g·) = σ.σ`). For CFI: the gadget twist swapping the decided pair. | Structure |
| `configSwap_rankPerm` / `_flip` | The leaf rank perms differ by `g`: `π_σ = π_flip · g` (resp. `π_flip = π_σ · g⁻¹`), from transport + `vertexRank_comp`. | axiom-light |
| `candidateTwist_eq_conjugate` | 663-673 | **The rank-space reduction**: given a `ConfigSwap g`, `candidateTwist = π_σ · g⁻¹ · π_σ⁻¹`. The forced candidate is the `π_σ`-conjugate of a genuine graph automorphism. | axiom-light |
| `isAut_candidateTwist_iff_conjugate` | 675-686 | `IsAut candidate adj ↔ IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj` — the *rank-space* firing obligation is exactly the gadget rank-alignment. | axiom-light |

**§L.7b — vertex-model soundness (Approach C, the faithful C# model).** A config-swap is a real
graph automorphism, so both branches give the *same canonical leaf* — no rank-alignment needed. This
is the soundness the C# `TwistConstruction` actually uses (it verifies a vertex automorphism, not the
rank rebasing).

| Name | Description | Notes |
|------|-------------|-------|
| `canonAdj_eq_of_configSwap` | 697-712 | **Equal canonical leaves**: a `ConfigSwap` ⟹ `canonAdj σ = canonAdj flip` (via `π_flip = π_σ·g⁻¹` + `g⁻¹ ∈ Aut`, so relabelling by it is invisible). Pruning the flip branch loses nothing. | **Key**; axiom-light |
| `realizableFlip_of_configSwap` | 714-728 | A `ConfigSwap` ⟹ `RealizableFlip` (identity witness, since the leaves coincide) — the decision is a genuine `Aut(adj)` symmetry, with no rank-alignment obligation. | axiom-light |

**§L.8 — CFI completeness: config-swap from a swapping automorphism (M1c step 3, the cascade-1b bridge).**
*Where a config-swap comes from.* A swapping automorphism `g` (`g a = b`, `g b = a`) is exactly an
`OrbitPartition adj P S a b` witness specialised to the size-2 decision cell — the cascade oracle's
currency. So linear-oracle CFI completeness reduces to the **shared cascade-1b** obligation
(bounded-depth half `recoverableByDepth_cfi` proved; decision-node-depth bridge open, *not* `GI∈P`).

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_swap` | 760-827 | **Closed instance**: a σ-cell-coherent *transposition* automorphism (`g` swaps `a,b`, fixes the rest + `χι`; `σ.σ a w = σ.σ b w` off the pair) *is* a `ConfigSwap`. The `Z₂` twin-swap — the simplest genuine abelian decision. Real proof content (swap case-analysis + antisymmetry). | **Key**; axiom-light |
| `configSwap_of_twin` | 829-857 | **The twin → config-swap bridge** (linear-oracle analog of `CascadeOracle.cellsAreOrbits_of_twin_cells`, sharing the twin hypothesis + the `isAut_swap_of_twin` witness): an **(adj, σ)-twin** decision pair (adjacency-twin on a simple graph + σ-cell-coherent, `χι a = χι b`) ⟹ `ConfigSwap`, via `configSwap_of_swap` fed by `isAut_swap_of_twin`. Closes the **genuine-twin / module** abelian decision class — both oracles fire on the same twin class through one shared lemma. **Not** CFI (no twins; CFI uses the general non-transposition gadget twist). | **Key**; axiom-light |
| `ConfigSwapRecoverable` | 859-869 | Graph-level predicate: every leaf decision admits a config-swap = the linear oracle's **decision-node recoverability** = the named cascade-1b obligation (analog of `AbelianSufficiencyHolds`). | def |
| `canonAdj_eq_of_configSwapRecoverable` | 871-882 | Capstone (pruning soundness): `ConfigSwapRecoverable` ⟹ both branches give the identical canonical leaf at every decision. | axiom-light |
| `realizableFlip_of_configSwapRecoverable` | 884-895 | Capstone (real symmetry): `ConfigSwapRecoverable` ⟹ every decision is a genuine `Aut(adj)` symmetry — vertex-model completeness, no rank-alignment. | axiom-light |

Open (not a `sorry`): `configSwapRecoverable_of_cfi : IsCFI adj → ConfigSwapRecoverable` — the general
gadget twist (non-transposition `g`, moves the whole coupled component) needs the deferred Stage-3
`Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` machinery = the same `hwit` as Tier-3a B1; plus the decision-node-depth half
of cascade-1b.

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
| `RankAligned` | 501-509 | The algebraic firing condition: a rank-aligned automorphism exists (`∃ g ∈ Aut, g · π_σ = π_flip`). | Definition |
| `isAut_candidateTwist_iff_rankAligned` | 511-519 | **Interface**: forced candidate `∈ Aut ⟺ RankAligned`. The whole completeness question is "does a rank-aligned aut exist?" (= `isAut_candidateTwist_iff_aligned`). | axiom-light |
| `AbelianSufficiency` | 521-531 | **Per-decision relativized target**: `RealizableFlip → IsAut candidate`. FALSE in the non-abelian regime (the wall); the claim to discharge on the abelian/cascade class. | Definition |
| `oracleFires_of_abelianSufficiency` | 533-548 | **Capstone (what suffices)**: `AbelianSufficiency` + a real symmetry ⟹ the oracle fires. Linear-oracle analog of cascade's `cascadeComplete_of_localization`. | axiom-light |
| `abelianSufficiency_of_rankPerm_eq` | 550-561 | **Non-vacuous closed instance**: the absorbed decision is abelian-sufficient (candidate `= 1 ∈ Aut` outright). Validates the scaffold. | axiom-light |
| `AbelianSufficiencyHolds` | 563-571 | Graph-level discharge target (every leaf decision abelian-sufficient). Open obligation `abelianSufficiencyHolds_of_cfi : IsCFI adj → AbelianSufficiencyHolds adj` (downstream, via `theorem_1_HOR_cfi_oddDeg` — the gadget rank-alignment = B1 `hwit`). | Definition |
| `oracleFires_of_abelianSufficiencyHolds` | 573-587 | **Graph-level capstone**: `AbelianSufficiencyHolds` ⟹ the oracle fires at every leaf decision that is a real symmetry (relativized completeness on the abelian class). | axiom-light |

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
| `AutGroup adj` | The subgroup `{π | IsAut π adj}` of `Equiv.Perm (Fin n)`. `Subgroup` axioms discharged from `IsAut.refl/.trans/.symm` (`mul_mem'` uses `a * b = b.trans a`). | Definition |
| `mem_autGroup` | 69-70 | `π ∈ AutGroup adj ↔ IsAut π adj`. | `@[simp]` |
| `orbitPartition_iff_autGroup` | 72-87 | **The bridge**: `OrbitPartition adj P S v w ↔ ∃ g : AutGroup adj, (g preserves P) ∧ FixesPointwise ↑g S ∧ ↑g v = w` — repackages `OrbitPartition`'s bare `π` as a group element (in the pointwise-`S`-stabilizer), keeping `OrbitPartition` the working object. | axiom-light |

### A2 — Action on vertices + orbit bridge

| Name | Description | Notes |
|------|-------------|-------|
| `autGroup_smul` | 96-98 | The subgroup action's smul is permutation application: `g • v = (↑g) v`. | `@[simp]`, `rfl` |
| `mem_orbit_autGroup_iff` | 100-109 | `w ∈ MulAction.orbit (AutGroup adj) v ↔ ∃ π, IsAut π adj ∧ π v = w` — orbit membership unfolded (pure, pre-`P`). | axiom-light |
| `mem_orbit_autGroup_iff_orbitPartition` | 111-125 | **Orbit bridge**: under `P`-invariance (`∀ π, IsAut π adj → π preserves P`; the Tier-2 `hP_invariant` pattern), `v`'s `AutGroup`-orbit = the root relation `OrbitPartition adj P ∅` (no individualization). | axiom-light |

### A3 — Normal subgroup chains

| Name | Description | Notes |
|------|-------------|-------|
| `LayerChain adj` | A finite descending chain `AutGroup adj = layer 0 ⊵ … ⊵ layer len = ⊥` with each layer relatively normal in its predecessor (`(layer (i+1)).subgroupOf (layer i)` is `Normal`). The `H₀ ⊵ … ⊵ H_k` substrate B1 (Tier 3a) is stated over. | Structure |
| `LayerChain.trivial` | The one-step chain `AutGroup adj ⊵ ⊥` (`⊥` normal in anything) — witnesses `LayerChain` is inhabited (`Inhabited` instance). | Definition |

### A4 — quotient graph + cell = quotient-vertex

| Name | Description | Notes |
|------|-------------|-------|
| `orbitSetoid adj P S` | The `Aut_S`-orbit relation `OrbitPartition adj P S` packaged as a `Setoid` (from its proved `refl/symm/trans`). | Definition |
| `OrbitQuotient adj P S` | **The quotient vertex set** `V(G)/Aut_S` = `Quotient (orbitSetoid …)`. `Fintype` + `DecidableEq` instances (noncomputable, classical). | `abbrev` |
| `orbitMk` / `orbitMk_eq_iff` | The quotient map `v ↦ ⟦v⟧`; `orbitMk v = orbitMk w ↔ OrbitPartition adj P S v w`. | Definition / `Quotient.eq` |
| `cell_iff_orbitMk_eq` | 226-242 | **The cell = quotient-vertex lemma** (B1's induction step): under `CellsAreOrbits`, `v,w` share a 1-WL cell of `(G,S)` **iff** `orbitMk v = orbitMk w`. Forward = `CellsAreOrbits`+`Quotient.sound`; backward = unconditional `subset_warmRefine`+`Quotient.exact`. | **Key theorem**; axiom-light |
| `QuotientAdjCompatible` | 246-254 | The well-definedness condition for a simple induced quotient adjacency: `adj v w` constant on `Aut_S`-orbit pairs. (Genuinely conditional — fails for coarse `S`; the multigraph subtlety the doc flags.) | Definition |
| `quotientAdj` / `quotientAdj_mk` | The induced adjacency on `OrbitQuotient`, well-defined under `QuotientAdjCompatible` (via `Quotient.lift₂`); `quotientAdj h ⟦v⟧ ⟦w⟧ = adj.adj v w` (`rfl`). | Definition / `@[simp]` |
| `quotientAdjCompatible_of_discrete` | 269-280 | At discreteness the quotient graph is always well-defined (orbits singletons) — the recursion-bottom anchor, paralleling `cellsAreOrbits_of_discrete`. | axiom-light |
| `orbitPartition_empty_iff_orbitRel` | 290-302 | The root orbit relation `OrbitPartition adj P ∅` = the `AutGroup` `MulAction` orbit relation (under `P`-invariance) — relational form, symmetrised for `orbitRel`. | axiom-light |
| `orbitQuotientEquivAutGroup` | 304-312 | **The root quotient is `V(G)/Aut(G)`**: `OrbitQuotient adj P ∅ ≃ MulAction.orbitRel.Quotient (AutGroup adj) (Fin n)` (under `P`-invariance), tying A4's relational quotient back to A1/A2's group object. | Definition (`noncomputable`) |

## ChainDescent/Cascade.lean

B1 (Tier 3a cascade composition) of `docs/chain-descent-tier3-tractable-buildout.md`,
Phases A + C. Build plan: `docs/chain-descent-tier3a-b1-build-plan.md`. The headline
"depths add" theorem, **conditional on the per-layer transfer** (`LayerStep`, = paper
§4.2.5, discharged in the not-yet-built Phase D). Stays on `Fin n` (no quotient
re-typing) by telescoping cumulative individualization sets. Axiom-clean (standard
basis; `refineStep` via `warmRefine`).

### Phase A — interface

| Name | Description | Notes |
|------|-------------|-------|
| `IsBase adj P T` | `T` is a base of the `P`-preserving automorphism group: `Aut_T`-orbits are trivial (`OrbitPartition adj P T v w → v = w`). The chain's bottom `H_k = {1}`. | Definition |
| `LayerStep adj P T S` | The per-layer transfer obligation: `CellsAreOrbits adj P T → CellsAreOrbits adj P (T ∪ S)` (paper §4.2.5 transferred to `G`). Consumed by the composition induction; discharged from Tier-1/2 in Phase D. | Definition |
| (cascade-class predicate) | `RecoverableByDepth adj P bound` (in `CascadeOracle.lean`) — Tier-1 (`recoverableByDepth_cfi`) / Tier-2 (`recoverableByDepth_scheme`) instances already proved. | (existing) |

### Phase C — composition theorem

| Name | Description | Notes |
|------|-------------|-------|
| `discrete_of_cellsAreOrbits_base` | 69-76 | **(C1) Finish**: `CellsAreOrbits adj P T` + `IsBase adj P T` ⟹ `Discrete (warmRefine … T)`. Same-cell → same-orbit → equality. | axiom-light |
| `cellsAreOrbits_compose` | 78-91 | **(C2) The induction**: from layer-1 recoverability (`CellsAreOrbits` at `T 0`) + per-layer steps (`hstep i : CellsAreOrbits (T i) → CellsAreOrbits (T (i+1))`), conclude `CellsAreOrbits` at the final cumulative `T k`. Telescopes the layers. | **Key theorem**; axiom-light |
| `cumulative_card_le` | 93-99 | **Depths add (cardinality)**: `|⋃_{i≤k} S i| ≤ Σ_{i≤k} f i` when `|S i| ≤ f i` (`card_biUnion_le` + `sum_le_sum`). | axiom-light |
| `cascadeComposition` | 101-113 | **Theorem 3a headline (conditional)**: cumulative sets + layer-1 base + per-layer transfer steps + final set a base ⟹ warm refinement at `T k` is `Discrete`. With `cumulative_card_le`, depth `≤ Σ fᵢ`. Conditional on `hstep` (= §4.2.5, Phase D). | **Key theorem**; axiom-light |
| `cascadeComposition_single` | 121-124 | The `k = 0` case: a single cascade-class layer (Tier-1/2) that is a base reaches discreteness — recovers the orbit-recovery theorems as the composition's base case. | axiom-light |

### Phase D — discharging `LayerStep` (the §4.2.5 transfer), intrinsic route

Approach B (build-plan §3): stay on `Fin n`, reduce `LayerStep` to a witness-upgrade via
**set-monotonicity** of warm refinement (reusing `refineStep_iff`); the materialized-quotient
route was rejected (`refineStep` axiomatic, no cross-size API).

| Name | Description | Notes |
|------|-------------|-------|
| `Refines χ₁ χ₂` | `χ₁` refines `χ₂` (finer partition): `∀ a b, χ₁ a = χ₁ b → χ₂ a = χ₂ b`. | Definition |
| `signature_refines` | 142-163 | **The crux**: `Refines χ₁ χ₂` ⟹ equal `χ₁`-signatures give equal `χ₂`-signatures (`signature χ₂ = (signature χ₁).map G` for a coarsening map `G` built from `Refines`). | axiom-light |
| `refineStep_mono` | 165-171 | `Refines χ₁ χ₂ → Refines (refineStep χ₁) (refineStep χ₂)` (via `refineStep_iff` + `signature_refines`). | axiom-light |
| `iterate_refineStep_refines` / `warmRefine_refines_initial` | warm refinement monotone in the initial colouring's partition order. | axiom-light |
| `individualizedColouring_refines` | 189-201 | `T ⊆ T'` ⟹ `Refines (individualizedColouring n T') (individualizedColouring n T)`. | axiom-light |
| `warmRefine_indiv_mono` | 203-211 | **Set-monotonicity (the payoff)**: same `(T ∪ S)`-cell ⟹ same `T`-cell. "1-WL monotone in the individualization set" — the lemma the docs had mis-cited as `warmRefine_refines`. | **Key**; axiom-light |
| `WitnessUpgrade adj P T S` | The genuine §4.2.5 content: same-`Aut_T`-orbit + same-`(T∪S)`-cell `v,w` ⟹ `OrbitPartition (T∪S) v w` (the orbit relation upgrades to the finer stabilizer). | Definition |
| `layerStep_of_witnessUpgrade` | 225-232 | **The reduction**: a witness-upgrade discharges a `LayerStep` (via `warmRefine_indiv_mono` + `CellsAreOrbits T`). Where Phase C meets the per-layer content. | **Key**; axiom-light |
| `layerStep_empty` / `layerStep_subset` / `layerStep_of_cellsAreOrbits` / `layerStep_of_discrete` | Trivial real instances: no-op layer (`S = ∅`), `S ⊆ T`, independently-recoverable target, and the discretizing recursion-bottom. | axiom-light |
| `witnessUpgrade_of_pathFixing` | 257-272 | **Bridge to harvested generators**: if every same-orbit, same-cell pair has a `P`-preserving automorphism with support disjoint from `T ∪ S` (fixing the committed path) sending `v ↦ w`, the upgrade holds (`orbitPartition_of_support_disjoint`). Exactly what the cascade/linear oracles produce. | axiom-light |

### Step 5 — the synthesis (Theorem 3a reduced to harvested generators)

| Name | Description | Notes |
|------|-------------|-------|
| `cascadeComposition_pathFixing` | 291-312 | **Theorem 3a, reduced to harvested path-fixing generators**: cumulative sets by increments + layer-1 recoverable + *every layer's residual symmetry realized by path-fixing automorphisms* (`hwit`, = harvested generators) + final set a base ⟹ warm refinement at `T k` is `Discrete`. Reduces the whole of Theorem 3a to one hypothesis (per-layer path-fixing witness existence). The bridge to calculator §2's harvested-chain picture. | **Key theorem**; axiom-light |
| `cascadeComposition_twoLayer` | 314-329 | The smallest genuine composition: outer cascade-class layer at `T₀` + inner path-fixing layer (increment `S`) + union a base ⟹ `Discrete`. The `CFI(scheme)` / `Scheme(CFI)` shape once the inner witnesses are constructed. | axiom-light |
