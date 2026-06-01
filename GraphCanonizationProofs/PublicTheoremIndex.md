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
| `POE` | 70-74 | Partial-order entries: the three values `less`, `unknown`, `greater` that populate a `PMatrix`. | Inductive |
| `neg` | 87-91 | Antisymmetric reverse on one entry: swaps `less`/`greater`, fixes `unknown`. | Definition |
| `neg_neg` | 93-94 | `neg` is an involution: `neg (neg e) = e`. | `@[simp]` |
| `POE.swap` | 96-99 | σ-swap on one entry (the matrix-wide relabelling of the direction-symmetry argument); coincides with `neg`. | Definition |
| `POE.swap_swap` | 101 | σ-swap is an involution: `swap (swap e) = e`. | `@[simp]` |
| `swap_less` | 103 | `swap .less = .greater`. | `@[simp]` |
| `swap_greater` | 104 | `swap .greater = .less`. | `@[simp]` |
| `swap_unknown` | 105 | `swap .unknown = .unknown`. | `@[simp]` |
| `PMatrix` | 111-112 | The partial-order matrix type `Fin n → Fin n → POE`. | Definition |
| `swap` | 118-119 | Pointwise σ-swap of a `PMatrix`: swap `less` with `greater` at every entry. | Definition |
| `swap_swap` | 121-122 | σ-swap is an involution on `PMatrix`: `swap (swap P) = P`. | `@[simp]` |
| `Antisymmetric` | 124-126 | A `PMatrix` is antisymmetric when `P i j = POE.neg (P j i)` for all `i, j`. | Definition |
| `AdjMatrix` | 135-136 | Self-contained adjacency matrix on `Fin n`, wrapping a `Fin n → Fin n → Nat` field. | Structure |
| `applyGuess` | 140-147 | Apply a single guess `(a, b, dir)` to `P`: set `P a b := dir`, `P b a := neg dir`, leaving every other entry unchanged. Does not transitively close. | Definition |
| `applyGuess_swap` | 149-170 | Applying `(a, b, swap dir)` to the σ-swapped matrix equals σ-swapping after `applyGuess P a b dir` (needs `a ≠ b`); links the two guess directions through σ. | — |
| `closeStep` | 174-187 | Single-step transitive closure: derive `P i j` from a uniform chain `i → k → j`, with `less`-chains taking priority over `greater`-chains at ties. | Definition |
| `transitiveClose` | 189-193 | Transitive closure of a `PMatrix` by iterating `closeStep` `n*n` times — enough rounds to reach fixpoint. | Definition |
| `conflictMatrix` | 224-237 | Concrete 4-vertex witness with a conflicted pair `(0,1)` carrying both a `less`-chain and a `greater`-chain; refutes σ-swap commutation. | Definition |
| `closeStep_swap_false` | 256-265 | **Refutation:** `closeStep` does not commute with σ-swap unconditionally — the `less`-first tie-break is not σ-symmetric (fails on `conflictMatrix`). | — |
| `transitiveClose_swap_false` | 286-300 | **Refutation:** `transitiveClose` does not commute with σ-swap unconditionally (witnessed by `conflictMatrix`). | — |
| `Colouring` | 304-305 | A vertex colouring `Fin n → Nat`. | Definition |
| `signature` | 307-313 | Multiset signature of vertex `v` under colouring `χ` and state `(adj, P)`: the `(χ u, adj.adj v u, P v u)` tuples over all `u ≠ v`. | Definition |
| `POE.toNat` | 315-320 | Numeric code for a `POE` entry matching the C# packing: `less ↦ 0`, `unknown ↦ 1`, `greater ↦ 2`. | Definition |
| `encTuple` | 326-332 | Canonical injection of a signature tuple `(colour, edge-label, POE)` into `Nat` (Cantor pairing); mirrors the C# neighbour-tuple packing. | Definition |
| `sigKey` | 341-348 | Canonical refinement key of a vertex: its old colour followed by the sorted encoded signature multiset (the C# `[own-colour, sorted neighbour-tuples]`). | Definition |
| `sigKey_eq_iff` | 350-364 | Two vertices share a `sigKey` iff they have the same old colour and the same signature. | — |
| `warmRefine` | 393-403 | Warm 1-WL refinement: iterate `refineStep` `n` times from `initial`; concrete and computable. | Definition |
| `refineStep` / `refineStep_iff` | ~320-417 | **Concrete (2026-05-30, no longer axioms):** `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)` (own colour + sorted encoded signature = the C# `WarmPartition.RefineRound`); `refineStep_iff` (same colour ⟺ same old colour + same signature) is now a **theorem**. Removes `refineStep`/`refineStep_iff` from the axiom basis project-wide. Helpers: `POE.toNat`(_injective), `encTuple`(_injective), `sigKey`, `sigKey_eq_iff`. | Def + theorem |
| `samePartition` | 407-410 | Two colourings induce the same partition: `χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j` for every `i, j`. | Definition |
| `samePartition.refl` | 416 | `samePartition` is reflexive. | — |
| `samePartition.symm` | 418-419 | `samePartition` is symmetric. | — |
| `samePartition.trans` | 421-423 | `samePartition` is transitive. | — |
| `refineStep_refines` | 429-434 | **Refinement is split-only (one round).** Equal refined colour implies equal old colour. | — |
| `warmRefine_refines` | 436-462 | Warm refinement is split-only: equal warm-refined colour implies equal starting colour. | — |
| `iterate_closeStep_fix` | 494-500 | Iterating `closeStep` from a fixpoint of itself stays at that fixpoint. | — |
| `cell_split_uniform_false` | 565-590 | **Refutation:** cell-mates do not in general keep equal signatures after a guess plus TC (witnessed by `witnessP0`, the gap fixed only by singleton-cell `a`, `b`). | — |
| `refineStep_preserves_singleton` | 612-619 | One refinement round preserves a singleton: if no vertex shares `a`'s colour, none does after `refineStep`. | — |
| `iterate_refineStep_preserves_singleton` | 621-634 | Iterating refinement preserves a singleton for any number of rounds. | — |
| `signature_applyGuess_off` | 636-650 | Off the guessed pair, the guess is invisible: for `x ∉ {a,b}` the signature under `applyGuess P₀ a b dir` equals the signature under `P₀`. | — |
| `signature_eq_of_samePartition` | 652-679 | **Signature equality is a partition invariant of the colouring:** partition-equal colourings induce the same signature-equality relation between vertices. | — |
| `warm_6_2` | 681-758 | **§6.2 direction invariance.** With `a, b` `χι`-singletons, warm refinement after `a < b` and after `b < a` induce the same partition. | — |
| `signature_swap` | 762-772 | σ-swapping `P` relabels each signature's `POE` component by `POE.swap`, leaving colour and adjacency components untouched. | — |
| `warmRefine_swap` | 774-816 | **Direction-blindness (Q1).** Warm refinement on `P` and on its σ-swap induce the same partition. | — |
| `warmRefine_applyGuess_swap` | 818-828 | Warm refinement after `a < b` on `P₀` and after `b < a` on the σ-swapped `P₀` induce the same partition. | — |
| `applyGuess_comm` | 830-848 | **Q2 — guesses commute.** Guessing on `{a,b}` then `{b,c}` (pairwise-distinct vertices) gives the same `(adj, P)` as the reverse order, since the writes touch disjoint matrix entries. | — |
| `signature_agree_off` | 856-867 | If `P` and `Q` agree on every entry with an endpoint outside `D`, then off `D` they yield the same signature. | — |
| `warmRefine_agree_off'` | 869-916 | **§6.2 — composable cross-branch sharing.** Matrices agreeing off `D` and `samePartition`-equal starting colourings (with `D` all `χ`-singletons) yield the same warm-refined partition; the cross-level form that chains across descent levels. | — |
| `warmRefine_agree_off` | 918-952 | **§6.2 — the cell partition depends only on the matrix off the decision set `D`.** Matrices agreeing off `D` (its vertices `χι`-singletoned) yield the same partition; the same-`χι` specialisation of `warmRefine_agree_off'`. | — |
| `PartitionInvariant` | 969-973 | A target-cell selector is partition-invariant when it depends only on the partition a colouring induces, not on raw colour values. | Definition |
| `target_direction_blind` | 975-984 | **§6.2 spine — base case.** For a partition-invariant selector, the target cell chosen after `a < b` equals the one after `b < a`. | — |
| `target_agree_off` | 986-999 | **§6.2 spine — inductive step.** For a partition-invariant selector and matrices agreeing off a singletoned decision set `D`, the target cell is the same even when the start colourings only agree up to partition. | — |
| `Egnd` | 1028-1029 | **§13.** The canonical ground set on `Fin n`: ordered pairs `(i, j)` with `i < j`. | Definition |
| `mem_Egnd` | 1031-1032 | Membership in `Egnd n` is exactly `p.1 < p.2`. | — |
| `Egnd_ne` | 1034-1035 | Pairs in `Egnd n` have distinct endpoints: `p.1 ≠ p.2`. | — |
| `Pof` | 1037-1050 | **§13.** Commit a set `S ⊆ Egnd n` of pair-guesses into a P-matrix: write `less` at `(u,v) ∈ S`, `greater` at `(v,u)`, leaving other entries unchanged. | Definition, `noncomputable` |
| `cl` | 1052-1057 | **§13.** Propagation closure on pair-guesses: the canonical pairs whose endpoints get separated by warm refinement after committing `S`. | Definition |
| `SingletonAt` | 1067-1069 | The fresh-colour hypothesis at a pair `p`: both `p.1` and `p.2` are `χι`-singletons. | Definition |
| `cl_extensive` | 1071-1086 | **§13 M1 — extensiveness of `cl`.** For canonical `S` whose vertices are all `χι`-singletons, every pair in `S` lies in `cl S`. | — |
| `Pof_mono_entry_of_unknown` | 1116-1140 | Entry-wise monotonicity of `Pof` from the all-unknown base: for canonical `S ⊆ T`, each entry of `Pof _ S` is either `unknown` or equal to the corresponding `Pof _ T` entry (does not lift to a `cl` monotonicity result). | — |
| `FullyDiscrete` | 1152-1154 | A colouring is fully discrete when every vertex is its own `χι`-singleton. | Definition |
| `cl_monotone_discrete` | 1156-1173 | **§13 M0, vacuous case.** Under `FullyDiscrete`, every canonical pair lies in every `cl S`, so `cl S = Egnd n` and monotonicity carries no structural information. | — |
| `TVerticesSingletons` | 1186-1188 | Every endpoint of every pair in `T` is a `χι`-singleton. | Definition |
| `warmRefine_samePartition_T_individualised` | 1190-1275 | **§13 M0, strong form.** Warm refinement under `Pof P₀ S` and `Pof P₀ T` induces the *same* partition when `S ⊆ T` and every endpoint of every `T`-pair is a `χι`-singleton. | — |
| `cl_monotone_T_individualised` | 1277-1288 | **§13 M0 — monotonicity of `cl`** under the T-individualised hypothesis: `S ⊆ T` implies `cl S ⊆ cl T`. | — |
| `cl_idempotent` | 1314-1328 | **§13 M2 — idempotence of `cl`** under fresh-colour individualisation of `S ∪ cl S`: `cl (cl S) = cl S`. | — |
| `Pof_fs` | 1400-1406 | **§14.** Finset-based computable analogue of `Pof`, enabling `decide`-checkable refutations. | Definition |
| `commitsToP` | 1408-1410 | **§14.** All-unknown-base commits-to-matrix shortcut: `Pof_fs (fun _ _ => .unknown) S`. | Definition |
| `cl_prov` | 1412-1417 | **§14.** Provenance closure (TC-based): the canonical pair-guesses whose direction is decided by `transitiveClose` of `commitsToP S`. | Definition |
| `closeStep_unknown` | 1421-1425 | `closeStep` returns `.unknown` at every entry of the all-unknown matrix. | — |
| `closeStep_unknown_fixpoint` | 1427-1430 | The all-unknown matrix is a fixpoint of `closeStep`. | — |
| `transitiveClose_unknown` | 1432-1444 | `transitiveClose` of the all-unknown matrix is the all-unknown matrix. | — |
| `cl_prov_empty` | 1448-1457 | **§14 CL0 for `cl_prov`:** `cl_prov ∅ = ∅`. | — |
| `cl_prov_extensive` | 1459-1473 | **§14 CL1 for `cl_prov`:** for canonical `S`, every commit's direct `less` write survives transitive closure, so `S ⊆ cl_prov S`. | — |
| `cl_prov_M3_false` | 1491-1501 | **§14 — refutes matroid M3 exchange for `cl_prov`.** A concrete `n=5, S={(1,2),(3,4)}, x=(2,3), y=(1,4)` counterexample where the M3 premise holds but the conclusion fails; machine-checked by `decide`. | — |
| `hasLessChain` | 1515-1518 | Existence of a `.less`-chain in `P` from `i` to `j` via some intermediate `k` with both edges `.less`. | Definition |
| `hasGreaterChain` | 1520-1522 | Existence of a `.greater`-chain in `P` from `i` to `j` via some intermediate `k`. | Definition |
| `CanConsistent` | 1524-1528 | A `PMatrix` is canonical-consistent when every `.less` entry sits at `i.val < j.val` and every `.greater` entry at `i.val > j.val`. | Definition |
| `LessMono` | 1530-1533 | One-sided `.less`-direction entry-wise monotonicity between two matrices: `P i j = .less → Q i j = .less`. | Definition |
| `canConsistent_no_conflict` | 1535-1545 | Under canonical-consistency, no pair simultaneously hosts both a `.less`-chain and a `.greater`-chain. | — |
| `commitsToP_classify` | 1547-1564 | Three-way classification of `commitsToP S i j` by `S`-membership of `(i,j)` and `(j,i)`. | — |
| `commitsToP_canConsistent` | 1566-1580 | `commitsToP` of a canonical `S` is canonical-consistent. | — |
| `closeStep_keeps_greater` | 1584-1587 | `closeStep` never demotes a decided `.greater` entry. | — |
| `iterate_closeStep_keeps_greater` | 1589-1599 | Iterating `closeStep` preserves any `.greater` entry — once decided, frozen. | — |
| `closeStep_decided` | 1601-1607 | `closeStep` preserves any decided entry (`.less` or `.greater`). | — |
| `closeStep_eq_less_iff` | 1623-1657 | `closeStep P i j = .less` iff `P i j` was already `.less`, or it was `.unknown` with a `.less`-chain through some intermediate vertex. | — |
| `closeStep_eq_greater_iff` | 1659-1711 | `closeStep P i j = .greater` iff `P i j` was already `.greater`, or it was `.unknown` with no `.less`-chain but a `.greater`-chain. | — |
| `closeStep_canConsistent` | 1713-1724 | `closeStep` preserves canonical-consistency. | — |
| `iterate_closeStep_canConsistent` | 1726-1734 | Iterating `closeStep` preserves canonical-consistency. | — |
| `transitiveClose_canConsistent` | 1736-1739 | `transitiveClose` preserves canonical-consistency. | — |
| `closeStep_lessMono` | 1741-1767 | Joint inductive step: under canonical-consistency of `Q` and `LessMono P Q`, `closeStep` preserves `.less`-mono. | — |
| `iterate_closeStep_lessMono` | 1769-1778 | Iterating `closeStep` preserves `.less`-mono under joint canonical-consistency. | — |
| `transitiveClose_lessMono` | 1780-1784 | `transitiveClose` preserves `.less`-mono under joint canonical-consistency. | — |
| `commitsToP_lessMono` | 1786-1799 | Base case for CL3: canonical `S ⊆ T` gives `LessMono (commitsToP S) (commitsToP T)`. | — |
| `cl_prov_monotone` | 1803-1828 | **§14 CL3 — monotonicity for `cl_prov`:** canonical `S ⊆ T` implies `cl_prov S ⊆ cl_prov T`. | — |
| `numUnknown` | 1837-1840 | Number of `.unknown` entries in a `PMatrix` — the strictly-decreasing potential bounding TC iteration. | Definition |
| `numUnknown_le` | 1842-1847 | `numUnknown P ≤ n * n`. | — |
| `closeStep_numUnknown_lt` | 1860-1885 | If `closeStep P ≠ P`, then `numUnknown` strictly drops under one closure round. | — |
| `iterate_closeStep_progress` | 1887-1914 | After `k` `closeStep` iterations, either a fixpoint has been reached at some step `≤ k`, or `numUnknown` has dropped by at least `k`. | — |
| `transitiveClose_is_fixpoint` | 1916-1966 | After `n*n` iterations of `closeStep`, the result is a fixpoint: `closeStep (transitiveClose P) = transitiveClose P`. | — |
| `transitiveClose_idempotent` | 1968-1974 | **TC idempotence.** `transitiveClose (transitiveClose M) = transitiveClose M`. | — |
| `cl_prov_idempotent` | 2005-2035 | **CL2 — idempotence.** `cl_prov (cl_prov S) = cl_prov S` for canonical `S`. | — |
| `IndivStep` | 2122-2146 | Existential witness of one descent-step individualisation: a colouring `χ'` that singletons every vertex in target `T` and refines `χ` outside `T`. Data, not a function — the trace carries one per step. | Structure |
| `singletons_union` | 2150-2171 | **D-singletons preserved.** If `χ` singletons every `v ∈ D`, an `IndivStep` with target `T` singletons every `v ∈ D ∪ T`. | — |
| `samePartition_of_samePartition` | 2173-2203 | Two `IndivStep`s applied to `samePartition`-equal colourings with the same target `T` produce `samePartition`-equal results — the inductive engine of the spine theorem. | — |
| `IndivStep.default` | 2205-2256 | **Concrete `IndivStep` witness.** A constructive individualisation step (parity-tagged base-`n` encoding), proving traces exist at every level so the spine theorem is non-vacuous. | Definition |
| `DescentTrace` | 2265-2303 | Inductive predicate: `(D, P, χι)` is reachable by `k` descent steps from `(P₀, χι₀)` under selector `sel`, each step carrying an `IndivStep` witness and a matrix agreeing with `P₀` off the enlarged decision set. | Inductive |
| `singletons` | 2307-2324 | **Trace invariant.** A trace's colouring singletons its whole decision set `D`. | — |
| `P_agrees` | 2326-2336 | **Trace invariant.** A trace's matrix agrees with `P₀` on every entry with an endpoint outside `D`. | — |
| `SpineChain` | 2340-2348 | Bundle of a `DescentTrace` with its derived state `(D, P, χι)`. The spine theorem is branch-independence of two such chains. | Structure |
| `partition` | 2355-2359 | The chain's level-`k` partition: warm refinement of its accumulated `(P, χι)`. | Definition |
| `IndivStep.samePartition_het` | 2365-2378 | Heterogeneous `samePartition_of_samePartition`: accepts separate targets `T₁, T₂` with an equality hypothesis. Used at the spine induction's level-`k+1` step. | — |
| `spine_branch_independent` | 2380-2454 | **The spine theorem (branch independence).** Any two `DescentTrace`s through `k` levels agree on the accumulated `D` (literal) and the level-`k` partition (`samePartition`) — handing the oracle one fixed partition instead of `2^d` refinement worlds. | — |
| `SpineChain.branch_independent` | 2456-2465 | **The spine theorem, `SpineChain` wrapper.** Two chains at level `k` share `D` and level-`k` partition. | — |
| `defaultColouring` | 2486-2496 | The level-`k` colouring of the default reference chain: iterate refine-then-individualise (via `IndivStep.default`) from `χι₀`, with the matrix held fixed at `P₀`. | Definition |
| `defaultD` | 2498-2507 | The level-`k` decision set of the default chain: accumulate `sel (warmRefine adj P₀ (defaultColouring k))` across all levels. | Definition |
| `defaultTrace` | 2509-2522 | The concrete `DescentTrace` realising the default construction, using `IndivStep.default` at every level and `P = P₀` throughout. | Definition |
| `defaultSpineChain` | 2524-2532 | The concrete reference `SpineChain` at every level, bundling `defaultD`/`P₀`/`defaultColouring`/`defaultTrace`. | Definition |
| `SpineChain.eq_default` | 2534-2545 | **Reference corollary.** Every `SpineChain` at level `k` shares `D` and level-`k` partition with `defaultSpineChain` — there is a canonical level-`k` partition, computable by one deterministic descent. | — |
| `Discrete` | 2569-2572 | A colouring is discrete when every cell is a singleton — equivalently, `χ : Fin n → Nat` is injective. | Definition |
| `of_samePartition` | 2576-2580 | Discreteness is `samePartition`-invariant: equal partitions transport `Discrete`. | — |
| `warmRefine_preserves` | 2582-2591 | Warm refinement preserves discreteness: if `χ` is injective, so is `warmRefine adj P χ`. | — |
| `SpineChain.IsLeaf` | 2595-2601 | A `SpineChain` reaches a leaf when its level-`k` partition is discrete (every vertex a singleton). | Definition |
| `SpineChain.isLeaf_iff_default` | 2603-2612 | `IsLeaf` is spine-invariant: a chain is a leaf iff `defaultSpineChain` at the same level is. | — |
| `TargetsNonsingletonCell` | 2616-2622 | Selector hypothesis: every returned vertex has a same-colour partner (`sel` only picks from non-singleton cells). | Definition |
| `NonemptyOnNonDiscrete` | 2624-2629 | Selector hypothesis: `sel χ` is non-empty whenever `χ` is not yet discrete. | Definition |
| `defaultD_univ_isLeaf` | 2631-2646 | **`D` covers all vertices ⇒ leaf.** When the accumulated decision set is the full vertex set, the default chain's spine partition is discrete. | — |
| `defaultD_grows_if_not_leaf` | 2648-2687 | **`D` strictly grows on every non-leaf step.** Under the two selector hypotheses, a non-leaf level-`k` chain has `|defaultD k| < |defaultD (k+1)|`. | — |
| `defaultSpineChain_reaches_leaf` | 2689-2728 | **Leaf existence.** Under `TargetsNonsingletonCell` and `NonemptyOnNonDiscrete`, the default descent reaches a leaf within `n` levels. | — |
| `DirAssignment` | 2751-2757 | Order assignment relative to `(P₀, D)`: an antisymmetric matrix agreeing with `P₀` on every entry with an endpoint outside `D`. The linear oracle's input shape — a point in the order-label residual. | Structure |
| `default` | 2763-2770 | **Trivial `DirAssignment`.** When `P₀` is antisymmetric, `P₀` itself is a valid order assignment for any `D` (witnesses non-emptiness). | Definition |
| `samePartition_pair` | 2772-2784 | Any two `DirAssignment`s over the same `(P₀, D)`, refined against a `D`-singletoning colouring, induce the same partition. | — |
| `samePartition_chain` | 2786-2799 | **Spine equivalence.** A `DirAssignment` over a chain's `D`, refined against the chain's colouring, induces the chain's partition — the residual is exactly the choice of `DirAssignment`, partition fixed. | — |
| `flipPair` | 2803-2847 | **Single-pair direction flip.** Negate the `(a, b)` and `(b, a)` entries of a `DirAssignment` via `POE.neg`. The generator of the `Z₂` group action on direction choices. | Definition |
| `eq_of_σ_eq` | 2849-2859 | `DirAssignment` equality is determined by the matrix field — propositional fields subsumed by proof irrelevance. | — |
| `flipPair_idempotent` | 2861-2870 | **Flip is an involution.** Two applications of `flipPair` to the same pair return the original `DirAssignment` — the `Z₂` generator squares to identity. | — |
| `flipPair_partition_invariant` | 2872-2882 | **Flipping preserves the partition.** `σ` and `σ.flipPair a b` share the spine partition — the order labels move, the partition doesn't. | — |
| `flipPair_comm` | 2884-2908 | **Flips on disjoint pairs commute** — the abelian-ness of the `Z₂^d` action: distinct decisions don't interfere. | — |
| `IsAut` | 2936-2939 | A `Fin n`-permutation `π` is a graph automorphism of `adj` when it preserves adjacency edge-by-edge: `adj.adj (π v) (π w) = adj.adj v w`. | Definition |
| `IsAut.refl` | 2945-2946 | The identity permutation is an automorphism. | — |
| `IsAut.trans` | 2948-2953 | Composition of automorphisms is an automorphism. | — |
| `IsAut.symm` | 2955-2961 | The inverse of an automorphism is an automorphism. | — |
| `labelledAdj` | 2965-2971 | **Labelled adjacency.** Adjacency matrix relabelled by `π`: entry `(i, j)` is the original adjacency between `π⁻¹ i` and `π⁻¹ j`. | Definition |
| `labelledAdj_eq_of_isAut` | 2973-2986 | **Automorphisms fix the labelled adjacency.** `IsAut π adj` implies `labelledAdj π adj = adj.adj` — an automorphism is invisible at the labelled level. | — |
| `isAut_of_labelledAdj_eq` | 2988-2998 | **Converse.** A permutation preserving the labelled adjacency is an automorphism. | — |
| `vertexRankNat` | 3011-3013 | Strict rank of vertex `v`: the count of vertices `u` with `χ u < χ v`. | Definition |
| `vertexRank` | 3031-3033 | Vertex rank packaged as `Fin n` via `vertexRankNat_lt_n`. | Definition |
| `vertexRank_strict_mono` | 3035-3054 | `vertexRank` is strictly monotonic in the colour value: `χ v < χ w` implies `vertexRank χ v < vertexRank χ w`. | — |
| `vertexRank_injective` | 3056-3066 | On a `Discrete` colouring, `vertexRank` is injective. | — |
| `vertexRank_bijective` | 3068-3071 | On a `Discrete` colouring, `vertexRank` is bijective. | — |
| `rankPerm` | 3073-3077 | **The rank permutation.** Bijection `Fin n ≃ Fin n` mapping each vertex to its colour-rank on a `Discrete` colouring. | Definition, `noncomputable` |
| `rankPerm_apply` | 3079-3080 | Unfolding lemma: `rankPerm χ h v = vertexRank χ v`. | `@[simp]` |
| `SpineChain.canonAdj` | 3098-3124 | **Leaf canonical adjacency.** Given a leaf `SpineChain` and a `DirAssignment σ` over its `D`, relabel `adj` by the rank permutation of the warm-refined partition. | Definition, `noncomputable` |
| `matrixLT` | 3128-3135 | **Row-major lex strict less-than on `n × n` matrices.** The first disagreeing cell `(i, j)` (row-then-column order) has `M₁ i j < M₂ i j`. | Definition |
| `matrixLT_irrefl` | 3137-3140 | `matrixLT` is irreflexive: no matrix is `<` itself. | — |
| `matrixLT_asymm` | 3142-3163 | `matrixLT` is asymmetric: `M₁ < M₂` implies `¬ M₂ < M₁` (strict-order fact). | — |
| `PMatrix.fintype` | 3167-3172 | `Fintype` instance for `PMatrix n`, stated explicitly since `PMatrix` is a `def` and so does not inherit the `Pi` instance transparently. | Instance |
| `fintype` | 3178-3188 | **`Fintype` on `DirAssignment P₀ D`.** Obtained by injecting the σ-field into the `Fintype` `PMatrix n`. | Instance, `noncomputable` |
| `relabelMatrix` | 3192-3199 | **Relabel a bare matrix** `Fin n → Fin n → Nat` by a permutation `π`: entry `(i,j)` becomes `M (π⁻¹ i) (π⁻¹ j)`. Lets `LeafTwistSpec` state the leaf-relabelling property without re-wrapping as an `AdjMatrix`. | Definition |
| `MatrixLex` | 3201-3206 | `Fin n → Fin n → Nat` viewed under the row-major lex order via nested `Pi.Lex`. | `abbrev` |
| `toMatrixLex` | 3208-3211 | Wrap a matrix into its Lex'd form (identity at runtime — `Lex` is a type synonym). | Definition |
| `ofMatrixLex` | 3213-3215 | Unwrap a Lex'd matrix back to a plain `Fin n → Fin n → Nat`. | Definition |
| `ofMatrixLex_toMatrixLex` | 3217-3218 | `ofMatrixLex (toMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_ofMatrixLex` | 3220-3221 | `toMatrixLex (ofMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_injective` | 3223-3227 | `toMatrixLex` is injective. | — |
| `canonFormImages` | 3229-3238 | The Finset of Lex-wrapped `canonAdj` images over all `DirAssignment`s for a leaf chain — the candidate set `canonForm` minimises over. | Definition, `noncomputable` |
| `canonFormImages_nonempty` | 3240-3246 | `canonFormImages chain isLeaf` is non-empty when `DirAssignment P₀ chain.D` is. | — |
| `canonForm` | 3248-3268 | **The canonical leaf adjacency matrix:** the lex-min `canonAdj` over all `DirAssignment`s (row-major lex). Requires `Nonempty (DirAssignment P₀ chain.D)`. | Definition, `noncomputable` |
| `canonForm_mem_image` | 3270-3285 | **`canonForm` comes from some `DirAssignment`:** it equals `canonAdj σ` for some `σ`. | — |
| `canonForm_le_canonAdj` | 3287-3303 | **`canonForm` is the lex-minimum:** `toMatrixLex (canonForm) ≤ toMatrixLex (canonAdj σ)` for every `DirAssignment σ`. | — |
| `LinearOracleSpec` | 3307-3323 | **The linear-oracle interface type:** given a leaf chain and a current-branch `DirAssignment`, return either `none` or a verified automorphism of `adj` (bundled as a subtype). | Definition |
| `some_isAut` | 3330-3342 | **Soundness (subtype-level):** when the oracle returns `some result`, the returned permutation is automatically an automorphism. | — |
| `LeafTwistSpec` | 3344-3361 | **Leaf-twist validity spec:** when the oracle returns `some result`, the returned `π` relabels the input branch's canonical adjacency to that of some other `DirAssignment σ'` — the property justifying pruning. | Definition |
| `individualizedColouring` | 3399-3403 | **Fresh-colour individualisation** of a vertex set `S`: each `v ∈ S` gets unique colour `v.val + 1`; vertices outside `S` share colour `0`. | Definition |
| `FixesPointwise` | 3405-3408 | Predicate: permutation `π` fixes every vertex in `S` pointwise (`π v = v` for `v ∈ S`). | Definition |
| `complement` | 3414-3422 | A pointwise-fixing permutation stabilises the complement setwise: `v ∉ S` implies `π v ∉ S`. | — |
| `individualizedColouring_invariant` | 3426-3435 | An automorphism fixing `S` pointwise preserves the individualised colouring: `χ_S (π v) = χ_S v` for every `v`. | — |
| `signature_invariant_of_isAut` | 3439-3476 | An automorphism preserving `(adj, P, χ)` pointwise preserves the signature multiset at every vertex. | — |
| `refineStep_invariant_of_isAut` | 3478-3491 | An automorphism preserving `(adj, P, χ)` pointwise preserves one round of `refineStep`. | — |
| `iterate_refineStep_invariant_of_isAut` | 3493-3509 | Iterated refinement preserves automorphism invariance for any number of rounds. | — |
| `warmRefine_invariant_of_isAut` | 3511-3520 | Warm refinement preserves automorphism invariance: if `(adj, P, χ_init)` are all `π`-invariant, so is `warmRefine adj P χ_init`. | — |
| `signature_transport` | 3534-3559 | **Signature transport.** An automorphism `g` carrying `(P₁, χ₁)` to `(P₂, χ₂)` maps the `(P₂, χ₂)`-signature at `g v` to the `(P₁, χ₁)`-signature at `v`. Cross-config form of `signature_invariant_of_isAut`. | — |
| `sigKey_transport` | 3561-3568 | **`sigKey` transport** — cross-config: `sigKey adj P₂ χ₂ (g v) = sigKey adj P₁ χ₁ v`. | — |
| `refineStep_transport` | 3570-3578 | **`refineStep` transport** — one round, cross-config: `refineStep adj P₂ χ₂ (g v) = refineStep adj P₁ χ₁ v`. | — |
| `iterate_refineStep_transport` | 3580-3594 | **Iterated `refineStep` transport** across any number of rounds, cross-config. | — |
| `warmRefine_transport` | 3596-3605 | **Warm-refinement transport.** An automorphism carrying `(P₁, χ₁)` to `(P₂, χ₂)` carries the warm refinement of the first onto the second. | — |
| `OrbitPartition` | 3621-3627 | **Aut_S orbit relation** on vertices: `v ~ w` iff some automorphism of `adj` preserving `P` and fixing `S` pointwise sends `v` to `w`. | Definition |
| `refl` | 3633-3636 | Reflexivity of `OrbitPartition` (via the identity permutation). | — |
| `symm` | 3638-3653 | Symmetry of `OrbitPartition` (via permutation inverse). | — |
| `trans` | 3655-3670 | Transitivity of `OrbitPartition` (via permutation composition). | — |
| `subset_warmRefine` | 3672-3687 | **Trivial direction of the squeeze:** orbits refine 1-WL cells — `OrbitPartition v w` implies `warmRefine` colours of `v` and `w` agree. | — |
| `refineStep_iter_le_eq` | 3700-3718 | Refinement is split-only across iterations: equality at iterate `k + d` implies equality at iterate `k`. | — |
| `warmRefine_eq_iter_eq` | 3720-3734 | `warmRefine` equality implies iterate-`r` equality for any `r ≤ n`; the bridge from the fixpoint partition to any earlier-round partition. | — |
| `id_of_discrete_invariant` | 3759-3768 | **Fact B (pointwise):** a `π`-invariant discrete colouring forces `π` to be the identity. | — |
| `aut_trivial_of_discrete_warmRefine` | 3770-3786 | **Fact B (CFI):** if `warmRefine adj P χ_S` is discrete, every automorphism preserving `(adj, P)` and fixing `S` pointwise is the identity. | — |
| `orbit_iff_eq_of_discrete_warmRefine` | 3788-3806 | **Fact B (partition):** at discrete depth, `OrbitPartition adj P S v w ↔ v = w`. | — |
| `CascadesAt` | 3828-3835 | **Cascade-at-depth-`k` predicate:** some `S` with `S.card ≤ k` makes `warmRefine adj P (individualizedColouring n S)` discrete. | Definition |
| `cascadesAt_univ` | 3837-3856 | **Trivial cascade at depth `n`:** taking `S = univ` gives a discrete starting colouring preserved by warm refinement — the every-graph fallback. | — |
| `CascadesAt.mono` | 3858-3863 | Monotonicity: a cascade at depth `k₁` is a cascade at every depth `k₂ ≥ k₁`. | — |
| `theorem_1_HOR_at_depth` | 3876-3899 | **Key theorem (Tier 1 HOR).** If `adj` cascades at depth `k`, some `S` with `S.card ≤ k` makes `warmRefine` discrete and the `Aut_S`-orbit partition equal to the `warmRefine` partition. | — |
| `theorem_1_HOR_at_n` | 3921-3932 | **Theorem 1, trivial-bound corollary:** every graph admits orbit recovery at depth `n`. Axiom-free specialisation to `cascadesAt_univ`. | — |
| `theorem_1_HOR` | 3934-3945 | **Theorem 1 (legacy existential form):** some `S` makes `warmRefine` discrete and orbits equal cells. | — |
| `theorem_1_HOR_pointwise` | 3947-3959 | **Theorem 1, pointwise corollary:** at the cascade depth, every automorphism preserving `(adj, P)` and fixing `S` is the identity. | — |
| `SchemeProfile` | 4010-4026 | **Key structure (Tier 2).** Bundles a v-profile colouring with its structural facts: profile classes equal `Aut_v` orbits (schurian Step 1) and 1-WL refines the profile partition (intersection-number Step 2). | Structure |
| `warm_iff_profile` | 4032-4045 | **Squeeze for `SchemeProfile`:** the 1-WL fixpoint partition equals the profile partition. | — |
| `IsSchurianSchemeGraph` | 4065-4069 | **Abstract predicate** (axiom-Prop): placeholder for `adj` admitting a vertex-transitive schurian association scheme containing its edge relation. Becomes a real definition once the scheme machinery lands. | axiom |
| `schurian_scheme_profile_exists` | 4071-4082 | **Scheme-profile existence axiom (Tier-2 Fact A analogue):** any graph satisfying `IsSchurianSchemeGraph` admits a `SchemeProfile` at every vertex. Becomes a theorem once association-scheme infrastructure lands. | axiom |
| `theorem_2_HOR_of_profile` | 4084-4100 | **Theorem 2 (assembly form):** given a `SchemeProfile` witness at `v`, the 1-WL fixpoint partition at depth 1 equals the `Aut_v`-orbit partition. | — |
| `theorem_2_HOR` | 4102-4118 | **Key theorem (Tier 2 HOR).** For any graph satisfying `IsSchurianSchemeGraph`, the depth-1 1-WL fixpoint partition equals the `Aut_v`-orbit partition. Conditional on the `schurian_scheme_profile_exists` axiom. | — |

## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `CFIBase` | 57-68 | §1 A **CFI base graph** on `Fin m`: a simple (symmetric, loopless) `AdjMatrix m` with every vertex of degree at least 2 — the structural prerequisite for building CFI gadgets. | Structure |
| `neighbors` | 76-78 | The neighbour set of `v` in the base graph, as a `Finset (Fin m)`. | Definition |
| `degree` | 80-81 | The degree of `v` in the base graph: `(H.neighbors v).card`. | Definition |
| `mem_neighbors` | 83-86 | Membership characterisation: `w ∈ H.neighbors v ↔ H.adj.adj v w ≠ 0`. | `@[simp]` |
| `degree_ge_two` | 88-89 | The structural CFI invariant: every base vertex has degree at least 2. | — |
| `not_self_mem_neighbors` | 91-95 | No vertex is its own neighbour (looplessness): `v ∉ H.neighbors v`. | — |
| `mem_neighbors_symm` | 97-100 | The neighbour relation is symmetric: `w ∈ H.neighbors v ↔ v ∈ H.neighbors w`. | — |
| `gadgetSize` | 117-119 | §3 Size of the CFI gadget at base vertex `v`: `2^(degree v − 1) + 2 * degree v` — even-subset vertices plus endpoint vertices. | Definition |
| `cfiVertexCount` | 121-123 | Total vertex count of `CFI(H)`: `∑ v, H.gadgetSize v`. | Definition |
| `gadgetSize_ge_six` | 125-136 | Every CFI gadget contains at least 6 vertices (`degree v ≥ 2` gives `2^1 + 2*2 = 6`). | — |
| `evenSubsetsOfNeighbors` | 153-156 | §4 The `Finset` of even-cardinality subsets of `N(v)`; indexes the subset vertices `a_S^v` of `CFI(H)`. | Definition |
| `empty_mem_evenSubsetsOfNeighbors` | 158-161 | The empty set belongs to `evenSubsetsOfNeighbors v` (cardinality 0 is even) — supplies the `a_∅^v` seed witness. | — |
| `mem_evenSubsetsOfNeighbors` | 163-167 | Membership: `S ∈ evenSubsetsOfNeighbors v ↔ S ⊆ N(v) ∧ S.card % 2 = 0`. | `@[simp]` |
| `triangleBase` | 177-188 | §5 The triangle `K_3` as a `CFIBase 3`: the smallest base graph satisfying the degree-≥-2 invariant; the running smoke-test base. | Definition |
| `triangleBase_degree` | 190-192 | Every vertex of `triangleBase` has degree 2. | — |
| `triangleBase_cfiVertexCount` | 194-196 | `triangleBase.cfiVertexCount = 18` — three gadgets of size 6. | — |
| `SubsetVertex` | 219-221 | §6 Type-level encoding of subset vertices of `CFI(H)`: pairs `(v, S)` with `S ∈ evenSubsetsOfNeighbors v`. | `abbrev` |
| `EndpointVertex` | 223-226 | §6 Type-level encoding of endpoint vertices of `CFI(H)`: triples `(v, w, b)` with `w ∈ N(v)` and `b : Bool`. | `abbrev` |
| `CFIVertex` | 228-236 | §6 The vertex type of `CFI(H)`: the sum `SubsetVertex ⊕ EndpointVertex`. | `abbrev` |
| `triangleBase_cfiVertex_card` | 290-292 | §7 Smoke test: `Fintype.card triangleBase.CFIVertex = 18`, matching `cfiVertexCount`. | — |
| `cfiAdj` | 318-331 | §8 **The CFI adjacency function** on `CFIVertex H`, returning 0/1 per the subset/endpoint clauses and the untwisted inter-gadget bridge formula. | Definition |
| `cfiAdj_symm` | 333-352 | `cfiAdj` is symmetric: `H.cfiAdj x y = H.cfiAdj y x`. | — |
| `cfiAdj_loopless` | 354-371 | `cfiAdj` is loopless: `H.cfiAdj x x = 0` for every CFI vertex `x`. | — |
| `cfi_triangle_no_twins` | 403-406 | §8.1 `CFI(triangle)` has no twin pairs: any two distinct vertices are separated by some third vertex. Confirms CFI's `Z₂` is a global gadget-flip, not a transposition — so the twin slice and CFI are complementary abelian classes. | — |
| `cfiAdjMatrix` | 433-443 | §9 **The CFI adjacency matrix** on `Fin (Fintype.card H.CFIVertex)`, lifting `cfiAdj` through `Fintype.equivFin`. | Definition, `noncomputable` |
| `cfiAdjMatrix_symm` | 445-449 | `cfiAdjMatrix` is symmetric. | — |
| `cfiAdjMatrix_loopless` | 451-455 | `cfiAdjMatrix` is loopless. | — |
| `IsCFI'` | 459-479 | §9 **Concrete `IsCFI` predicate.** A witness that `adj : AdjMatrix n` is the CFI of some base `H : CFIBase m`, exposing the base graph and bijection `Fin n ≃ H.CFIVertex` as addressable data. | Structure |
| `IsCFI'.baseSize` | 481-486 | The base graph's vertex count `h.m` for a CFI witness `h`; the depth-bound API ties `cfi_depth_bound h` to `h.baseSize`. | `abbrev` |
| `cfiAdjMatrix_is_cfi` | 488-519 | **Self-witness**: every `H.cfiAdjMatrix` satisfies `IsCFI'`, with `H` itself as the base. | Definition, `noncomputable` |
| `cfi_depth_bound` | 543-557 | §10 **Cascade-depth function for CFI graphs**, concretely `h.baseSize` (discharges the former axiom in Stage-4 M1). | Definition |
| `cfi_depth_bound_le` | 559-563 | **The CFI depth bound is `≤ baseSize`**, trivial after the M1 concretization. | — |
| `cfi_cascades_polynomially` | 565-574 | §10 **Fact A (cascade axiom).** A CFI graph cascades at depth `cfi_depth_bound h`; the sole remaining Tier-1 CFI axiom, awaiting the Cai-Fürer-Immerman cascade formalisation. | axiom |
| `theorem_1_HOR_cfi` | 576-591 | §10 **Theorem 1 (CFI form).** A CFI graph admits orbit recovery at depth `cfi_depth_bound h`; conditional on `cfi_cascades_polynomially`, and tighter than the `n`-bounded `theorem_1_HOR_at_n`. | — |
| `theorem_1_HOR_cfi_baseSize` | 593-609 | **Corollary**: orbit recovery at depth `≤ h.baseSize`, the headline `Nat`-shaped CFI bound for downstream consumers. | — |
| `card_CFIVertex` | 723-730 | §11 **The cardinality identity**: `Fintype.card H.CFIVertex = H.cfiVertexCount` — the abstract vertex type matches the gadget-size sum formula. | — |
| `IsCFI'.six_baseSize_le` | 748-776 | §12 **Connector**: a CFI graph has at least `6 * baseSize` vertices (each gadget contributes ≥ 6) — yields the `n/6` depth bound. | — |
| `theorem_1_HOR_cfi_n_bound` | 778-800 | §12 **Corollary (n-shaped bound).** Orbit recovery on a CFI graph holds at depth `≤ n/6` (as `6 * S.card ≤ n`), strictly tighter than the trivial `≤ n` bound. | — |
| `aEmpty` | 819-824 | §13.1 The canonical seed vertex `a_∅^v` of `CFI(H)`: the subset vertex at gadget `v` with the empty subset, individualized by the M2-M4 cascade. | Definition |
| `endpoint` | 826-829 | §13.1 The endpoint vertex `e^b_{v→w}` of `CFI(H)` at gadget `v`, pointing toward `w ∈ N(v)` with parity bit `b`. | Definition |
| `cfiAdj_aEmpty_endpoint_false` | 838-843 | §13.2 `cfiAdj (a_∅^v) (e^0_{v→w}) = 0` — the b=false endpoint is not adjacent to the empty-subset seed. | — |
| `cfiAdj_aEmpty_endpoint_true` | 845-850 | §13.2 `cfiAdj (a_∅^v) (e^1_{v→w}) = 1` — the b=true endpoint is adjacent to the empty-subset seed. | — |
| `aEmpty_ne_endpoint` | 852-859 | `H.aEmpty v ≠ H.endpoint hw b`: subset and endpoint vertices are distinct (different `Sum` tags). | — |
| `cfiAdj_aEmpty_endpoint_diff_gadget` | 861-874 | **Cross-gadget non-adjacency**: `cfiAdj (a_∅^v) (e^b_{v'→w}) = 0` when `v ≠ v'`. | — |
| `cfiAdj_bridge` | 876-892 | **The bridge edge**: `cfiAdj (e^b_{v→w}) (e^b_{w→v}) = 1` — same-parity endpoints at neighbouring gadgets pointing toward each other. | — |
| `IsCFI'.seedVertex` | 905-909 | §13.3 The `Fin n` vertex corresponding to the seed `a_∅^v` for an `IsCFI'` witness — what the cascade individualizes. | Definition |
| `IsCFI'.endpointVertex` | 911-915 | §13.3 The `Fin n` vertex corresponding to `e^b_{v→w}` for an `IsCFI'` witness — the endpoints the cascade probes. | Definition |
| `e_seedVertex` | 921-925 | Bijection round-trip: `h.e (h.seedVertex v) = h.H.aEmpty v`. | `@[simp]` |
| `e_endpointVertex` | 927-932 | Bijection round-trip: `h.e (h.endpointVertex hw b) = h.H.endpoint hw b`. | `@[simp]` |
| `seedVertex_ne_endpointVertex` | 934-944 | Seed and endpoint vertices are distinct in `Fin n` (their abstract counterparts have different `Sum` tags). | — |
| `adj_seed_endpoint_false` | 959-965 | §13.4 Fin-n: `adj (seedVertex v) (endpointVertex v w false) = 0`. | — |
| `adj_seed_endpoint_true` | 967-973 | §13.4 Fin-n: `adj (seedVertex v) (endpointVertex v w true) = 1`. | — |
| `adj_endpoint_seed_false` | 975-981 | §13.4 Symmetric Fin-n form: `adj (endpointVertex v w false) (seedVertex v) = 0`. | — |
| `adj_endpoint_seed_true` | 983-989 | §13.4 Symmetric Fin-n form: `adj (endpointVertex v w true) (seedVertex v) = 1`. | — |
| `individualizedColouring_singleton_self` | 1055-1058 | Individualizing a single seed gives it colour `seed.val + 1`. | `@[simp]` |
| `individualizedColouring_singleton_other` | 1060-1064 | Under a singleton individualization, every non-seed vertex gets colour `0`. | `@[simp]` |
| `individualizedColouring_eq_iff_of_mem` | 1191-1207 | Multi-seed uniqueness: under `individualizedColouring n S`, for `v ∈ S` a vertex shares v's colour iff it equals v. Generalises the singleton form to arbitrary S. | — |
| `allSeeds` | 1213-1220 | §13.8 The cascade individualization set `{seedVertex v : v ∈ Fin m}` — one seed per base vertex; the witness used in `cfi_cascades_polynomially`. | Definition |
| `seedVertex_injective` | 1222-1240 | `seedVertex` is injective: distinct base vertices map to distinct `Fin n` indices. | — |
| `seedVertex_mem_allSeeds` | 1242-1245 | Every `seedVertex v` lies in `allSeeds`. | — |
| `allSeeds_card` | 1247-1253 | `|allSeeds| = h.baseSize`; with `six_baseSize_le` the cascade individualization has at most n/6 vertices. | `@[simp]` |
| `adj_endpointVertex_eq_one_iff` | 1552-1574 | §13.12 Endpoint-endpoint adjacency characterisation: two endpoints are adjacent iff they form a bridge pair (`v_a = w_b ∧ w_a = v_b ∧ b_a = b_b`). | — |
| `adj_seedVertex_eq_one_iff` | 1576-1651 | §13.12 Seed-adjacency characterisation: a vertex is adjacent to `seedVertex w` iff it is a b=true endpoint in gadget w. Key structural fact for the cascade's no-match preconditions. | — |
| `subset` | 1773-1778 | §13.14 The CFI vertex `a_S^v`: the subset vertex at gadget v with even subset S ⊆ N(v). Generalises `aEmpty v` (the S = ∅ case). | Definition |
| `IsCFI'.subsetVertex` | 1831-1837 | §13.14 The `Fin n` vertex for `a_S^v`. Generalises `seedVertex v` (the empty-subset case). | Definition |
| `e_subsetVertex` | 1843-1849 | Bijection round-trip: `h.e (subsetVertex hS) = subset hS`. | `@[simp]` |
| `adj_subsetVertex_eq_one_iff` | 1897-1950 | §13.14 Subset-adjacency characterisation: `adj u (subsetVertex_{v'} hS') = 1` iff u is an endpoint at v' whose parity satisfies `(w' ∈ S') ⊕ b`. Generalises `adj_seedVertex_eq_one_iff` (S' = ∅). | — |
| `IsCFI'.adj_symm` | 2149-2153 | §13.16.5 CFI adjacency is symmetric at the `Fin n` level: `adj.adj i j = adj.adj j i`. | — |
| `OddDegree` | 2679-2682 | §13.21 Odd-degree CFI base: every base vertex has odd degree, ensuring no even subset of N(v) is saturated. Hypothesis for the axiom-free cascade (covers K₄, K₃,₃, Petersen). | Definition |
| `exists_witness_of_oddDegree` | 2684-2705 | §13.21 Under `OddDegree`, every even subset of N(v) has a strict non-element y ∈ N(v) \ S — the subset-distinction witness. | — |
| `cfi_cascades_polynomially_oddDeg` | 3017-3221 | §13.24 M4 — for OddDegree CFI graphs, `warmRefine adj P χ_{allSeeds}` is `Discrete`; discharges `CascadesAt` (the cascade axiom) axiom-free at depth `cfi_depth_bound h`. | — |
| `theorem_1_HOR_cfi_oddDeg` | 3223-3242 | **Tier-1 CFI orbit recovery.** Theorem 1 for OddDegree CFI graphs, axiom-free: orbit partition coincides with the warm-refined colouring at depth ≤ baseSize, conditional only on `OddDegree`. | — |

**§15 — Stage 3: gadget-flip automorphisms (the `Z₂^β` generators).** *We build the generator
*existence* (the cycle-space flips), not the full `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` iso — the hard
surjectivity half is needed by no consumer. Both consumers (`LinearOracle.configSwap_of_aut`
and Tier-3a B1's `hwit`) want the same object: a CFI automorphism with controlled support,
realised by the even-subgraph (cycle-space) flip. Phases 0–1 below; Phases 2–6 (adjacency
preservation, `Fin n` lift, support/locality, `P`-preservation, consumer wiring) follow.*

| Name | Description | Notes |
|------|-------------|-------|
| `card_symmDiff_mod_two` | **Parity helper.** `|S ∆ T| ≡ |S| + |T| (mod 2)` — the fact behind "an even subgraph preserves the even-subset invariant." | private |
| `CFIBase.flipSet` | The `F`-incident neighbours of `v` (`F : Fin m → Fin m → Bool` an even subgraph), as a subset of `N(v)`. | Definition |
| `CFIBase.symmDiff_flipSet_mem_even` | **Even-subset invariant preserved.** If every `flipSet F v` is even (`F` an even subgraph), `S ∆ flipSet F v` stays an even subset of `N(v)`. | — |
| `CFIBase.cfiFlip` | **The cycle-space gadget flip** on `CFIVertex H`: toggles endpoint parities along `F` (`e^b_{v→w} ↦ e^{b⊕F v w}_{v→w}`) and complements subsets (`a_S^v ↦ a_{S ∆ flipSet F v}^v`). | Definition (Phase 1) |
| `CFIBase.cfiFlip_involutive` | The gadget flip is an involution (`(S ∆ F) ∆ F = S`; `(b⊕c)⊕c = b`). | — |
| `CFIBase.cfiFlipEquiv` | The gadget flip as an `Equiv.Perm CFIVertex` (self-inverse). | Definition |
| `xor_eq_xor_iff` / `xor_ne_xor_iff` | Xor right-cancellation on `Bool` (`(a⊕c) = (b⊕c) ↔ a = b`, and the `≠` form). | private |
| `CFIBase.decide_mem_symmDiff_flipSet` | **Phase 2 bridge.** For `w ∈ N(v)`, `w ∈ S ∆ flipSet F v ↔ (w∈S) ⊕ F v w` — endpoint parity and subset membership flip together. | — |
| `CFIBase.cfiFlip_isAut` | **Phase 2 (the automorphism core).** For `F` an even subgraph that is symmetric (`F v w = F w v`), `cfiFlip F` preserves `cfiAdj` on every pair. Subset–endpoint: the `(w∈S)⊕b` invariant survives the joint flip; endpoint–endpoint bridge: the single edge `{v,w}` has one `F`-bit (symmetry), so `b₁=b₂` survives. | — |
| `IsCFI'.cfiFlipAut` | **Phase 3.** The gadget flip transported to `adj`'s vertices `Fin n` via the CFI labelling `h.e`: `g = e⁻¹ ∘ cfiFlip F ∘ e`. | Definition |
| `IsCFI'.e_cfiFlipAut` | Transport identity `e (g v) = cfiFlip F (e v)` — `e` intertwines the `Fin n` and `CFIVertex` flips. | — |
| `IsCFI'.isAut_cfiFlipAut` | **Phase-3 deliverable.** For `F` an even symmetric subgraph, `cfiFlipAut F ∈ Aut(adj)` — an honest `IsAut … adj` (via `matching` + `cfiFlip_isAut`) the consumers (`configSwap_of_aut`, Tier-3a `hwit`) use. | — |
| `IsCFI'.cfiFlipAut_involutive` | The lifted flip is an involution (needed where the decision pair must be *swapped*, `g a = b ∧ g b = a`). | — |
| `CFIBase.gadget` | **Phase 4.** The base vertex (gadget) of a CFI vertex. | Definition |
| `CFIBase.cfiFlip_eq_self_of_flipSet_empty` | **Locality.** If `F` has no edge at `x`'s gadget (`flipSet F (gadget x) = ∅`), the flip fixes `x` (`S ∆ ∅ = S`; empty flip set ⟹ `F v w = false` ⟹ parity unchanged). | — |
| `IsCFI'.cfiFlipAut_eq_self_of_flipSet_empty` | Locality lifted to `Fin n`: `F` avoiding `i`'s gadget ⟹ `cfiFlipAut F` fixes `i`. | — |
| `IsCFI'.disjoint_support_cfiFlipAut` | **Phase-4 deliverable.** If every vertex of a committed set `T` lives in an `F`-free gadget, then `Disjoint T (cfiFlipAut F).support` — the exact `Disjoint (committed set) π.support` the path-fixing consumers (`hwit`, `configSwap`) require. | — |
| `CFIBase.cfiFlip_endpoint` / `_swap` | **C1b.0 recon.** The flip toggles `e^b_{v→w}`'s parity by `F v w`; so it swaps the parity-pair `e^0/e^1` iff `{v,w} ∈ F` — the primary flippable decision pair. | simp / — |
| `CFIBase.cfiFlip_subset` | The flip symmetric-differences `a_S^v` by `flipSet F v` — swaps the subset-pair iff the gadget is `F`-touched (the second flippable kind). | — |
| `IsCFI'.cfiFlipAut_endpointVertex` / `_swaps_endpointVertex` | **C1b.0 (lifted).** The `Fin n` swap fact: `cfiFlipAut F` swaps `endpointVertex hw false ↔ true` iff `F v w = true` — the foundational swap C1b.1 keys on. | — |
| `triFlip_swaps_edge_01` | C1b.0 prototype validation: the triangle flip swaps the parity-pair on edge `{0,1}` (`decide`, independent confirmation). | — |
| `CFIBase.isEdgeOf` / `triEdge` | **C1b.2a.** The triangle even-subgraph through edge `{v,w}` with apex `u` — the minimal even subgraph through an edge. | Definition |
| `CFIBase.triEdge_eq_true` / `_iff` / `_symm` / `_cyclic` / `_apex` | Characterisation (membership, source-grouped), symmetry, cyclic invariance `{v,w,u}={w,u,v}`, and `F v w = true`. | — |
| `CFIBase.flipSet_triEdge` / `_other` | The triangle's flip set is `{w,u}` at base vertex `v` (degree 2), and `∅` off `{v,w,u}` (the avoidance → D-locality). | — |
| `CFIBase.triEdge_even` | The triangle is an even subgraph (every vertex F-degree 2 or 0). | — |
| `CFIBase.exists_even_triangle` | **C1b.2a deliverable.** If the decision edge has a common neighbour `u` (distinct, in `N(v)∩N(w)`), an even symmetric `F` through `{v,w}` exists with support `{v,w,u}` (avoids everything else) — the concrete cycle `F` cascade-1b needs, for triangle-containing bases. General triangle-free bases (K₃,₃, Petersen) need C1b.2b. | — |
| `CFIBase.evenPermEdge` | **C1b.2b.** The even-subgraph indicator of a permutation-cycle `σ` (the cycle's "next-vertex" map). A vertex's F-neighbours are `{σ p, σ⁻¹ p}` — degree 2, no list arithmetic. | Definition |
| `CFIBase.evenPermEdge_eq_true` / `_symm` / `_iff_of_mem` | Membership characterisation, symmetry, and the moved-vertex F-neighbours `= {σ p, σ⁻¹ p}`. | — |
| `CFIBase.flipSet_evenPermEdge_of_mem` / `_of_fixed` | Flip set `= {σ p, σ⁻¹ p}` at a moved vertex (degree 2), `∅` at a fixed point (avoidance). | — |
| `CFIBase.evenPermEdge_even` | The permutation-cycle is an even subgraph (degree 2 on the cycle via no-2-cycle, 0 off it). | — |
| `CFIBase.exists_even_cycle` | **C1b.2b deliverable.** A permutation-cycle `σ` through `{v,w}` (`σ v = w`) with H-edges (`hEdge`) and orbits ≥ 3 (`hNo2`) yields an even symmetric `F` through `{v,w}` avoiding every `σ`-fixed vertex. Subsumes the triangle; covers triangle-free bases. The cycle's *existence* in `H − Σ` is the isolated graph hypothesis (where treewidth enters). | — |
| `IsCFI'.cfiFlipAut_preserves_P` | **Phase 5.** The gadget flip preserves any `P` that *every* `adj`-automorphism preserves (the descent's profile/trivial `P`) — transported through `isAut_cfiFlipAut`. Honest scope: a component-moving flip preserves exactly the automorphism-invariant `P`'s. | — |
| `IsCFI'.cfiFlipAut_pathFixing_witness` | **Phase-5 deliverable (Tier-3a B1 `hwit` shape).** Assembles Phases 3–5 + `g v = w` into `∃ π, IsAut π adj ∧ (∀ x u, P (π x)(π u) = P x u) ∧ Disjoint T π.support ∧ π v = w` — exactly what `Cascade.cascadeComposition_pathFixing`'s `hwit` consumes. | — |
| `triFlipEdges` / `triFlip_even` | **Phase-0 prototype:** `triangleBase`'s unique nontrivial even subgraph (all 3 edges; β=1) and its even-flip-set fact. | Definition / — |
| `triFlip_involutive_check` | Phase-0 smoke test: triangle gadget flip is an involution (`decide`, kernel, axiom-clean). | — |
| `triFlip_isAut_check` | **Phase-0 crux:** the triangle gadget flip preserves `cfiAdj` on all 18×18 pairs (`decide`) — validates cycle-flip-is-automorphism on the smallest case before the general Phase-2 proof. | — |
| `triFlip_nontrivial` | Phase-0 smoke test: the triangle gadget flip moves some vertex — a nontrivial `CFI(triangle)` automorphism. | — |

| `CFIBase.flipSet_subset` | 3303-3306 | The flip set is a set of neighbours: `flipSet F v ⊆ N(v)`. | — |
| `CFIBase.mem_flipSet` | 3308-3311 | Membership in the flip set: `w ∈ flipSet F v ↔ w ∈ N(v) ∧ F v w`. | `@[simp]` |
| `CFIBase.cfiFlip_endpoint_swap` | 3450-3459 | **C1b.0.** The flip swaps the parity-pair `e^0_{v→w}/e^1_{v→w}` iff `F v w = true` (the swap companion of `cfiFlip_endpoint`). | — |
| `CFIBase.triEdge_symm` | 3494-3496 | The triangle even-subgraph indicator is symmetric in its edge endpoints: `triEdge v w u p q = triEdge v w u q p`. | — |
| `CFIBase.triEdge_apex` | 3498-3500 | The decision edge lies in its triangle: `triEdge v w u v w = true`. | — |
| `CFIBase.triEdge_cyclic` | 3502-3504 | Cyclic invariance of the triangle even-subgraph: `triEdge v w u = triEdge w u v` (so `{v,w,u}` is unordered). | — |
| `CFIBase.triEdge_iff` | 3506-3510 | Membership characterisation of the triangle even-subgraph indicator `triEdge v w u`. | — |
| `CFIBase.flipSet_triEdge_other` | 3529-3539 | **D-locality.** Off the triangle `{v,w,u}` the triangle's flip set is empty, so the triangle flip fixes every other gadget. | — |
| `CFIBase.evenPermEdge_symm` | 3592-3595 | The permutation-cycle even-subgraph indicator is symmetric: `evenPermEdge σ p q = evenPermEdge σ q p`. | — |
| `CFIBase.evenPermEdge_iff_of_mem` | 3597-3611 | At a moved vertex (`σ p ≠ p`), the cycle's F-neighbours are exactly `{σ p, σ⁻¹ p}` — degree 2, no list arithmetic. | — |
| `CFIBase.flipSet_evenPermEdge_of_fixed` | 3625-3634 | **D-locality (triangle-free bases).** At a `σ`-fixed vertex the permutation-cycle flip set is empty, so the cycle flip avoids every fixed gadget. | — |
| `IsCFI'.cfiFlipAut_swaps_endpointVertex` | 3798-3810 | **C1b.0 (lifted to `Fin n`).** `cfiFlipAut F` swaps `endpointVertex hw false ↔ true` iff `F v w = true` — the foundational decision-pair swap C1b.1 keys on. | — |
## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme` | 44-88 | A symmetric association scheme on `Fin n`: a partition of `Fin n × Fin n` into `rank + 1` symmetric relations `R_0, …, R_rank` (`R_0` the diagonal) with well-defined intersection numbers `p^k_{ij}`. | Structure |
| `relOfPair` | 104-106 | §1.1 The unique relation index `i : Fin (S.rank + 1)` for which `rel i v w = true`. | Definition, `noncomputable` |
| `rel_relOfPair` | 108-111 | The pair `(v, w)` lies in `R_{relOfPair v w}`. | — |
| `relOfPair_unique` | 113-116 | Uniqueness: any relation containing `(v, w)` is `relOfPair v w`. | — |
| `rel_iff_relOfPair` | 118-121 | Characterisation: `rel i v w = true ↔ i = relOfPair v w`. | — |
| `relOfPair_symm` | 123-128 | `relOfPair v w = relOfPair w v`. | — |
| `relOfPair_self` | 130-134 | `relOfPair v v = 0`: the diagonal sits in `R_0`. | — |
| `relOfPair_eq_zero_iff` | 136-144 | Diagonal characterisation: `relOfPair v w = 0 ↔ v = w`. | — |
| `IsSchemeAut` | 166-171 | §2 Scheme automorphism: a permutation of `Fin n` preserving every relation index of `S`. | Definition |
| `IsSchemeAut.refl` | 177-178 | The identity is a scheme automorphism. | — |
| `IsSchemeAut.trans` | 180-186 | Scheme automorphisms compose. | — |
| `IsSchemeAut.symm` | 188-194 | The inverse of a scheme automorphism is a scheme automorphism. | — |
| `relOfPair_eq` | 196-205 | Scheme automorphisms preserve `relOfPair`: `relOfPair (π v) (π w) = relOfPair v w`. | — |
| `SchurianScheme` | 209-220 | An `AssociationScheme` whose relations are exactly the diagonal orbits of `IsSchemeAut`: any two pairs in a relation are connected by some scheme automorphism. | Structure |
| `trivialScheme` | 232-248 | §3 The trivial scheme on `Fin 1` (rank 0, single relation `R_0`); smoke test confirming `AssociationScheme` is inhabited. | Definition |
| `trivialSchurianScheme` | 250-258 | §3 The trivial `Fin 1` scheme is schurian (only the identity is needed). | Definition |
| `vProfile` | 277-286 | T2.2 The v-profile colouring `w ↦ (relOfPair v w).val`: a vertex invariant relative to a fixed individualized `v`. | Definition, `noncomputable` |
| `vProfile_self` | 292-296 | `vProfile S v v = 0`. | — |
| `vProfile_eq_iff` | 298-301 | `vProfile S v w = vProfile S v u ↔ relOfPair v w = relOfPair v u`. | — |
| `vProfile_eq_zero_iff` | 303-315 | `vProfile S v w = 0 ↔ w = v`: the diagonal-relation form. | — |
| `vProfile_ne_self_of_ne` | 317-324 | `v` is a singleton in `vProfile S v ·`: for `w ≠ v`, `vProfile S v w ≠ vProfile S v v`. Matches the `SchemeProfile.v_singleton` field. | — |
| `SchemeOrbitPartition` | 339-343 | §4.1 The v-stabilized scheme-Aut orbit relation: some scheme automorphism with `π v = v` sends `w` to `u`. | Definition |
| `SchemeOrbitPartition.refl` | 349-351 | Reflexivity of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.symm` | 353-361 | Symmetry of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.trans` | 363-373 | Transitivity of `SchemeOrbitPartition`. | — |
| `AssociationScheme.vProfile_aut_invariant` | 394-404 | §4.2 S1.a — a v-stabilizing scheme automorphism preserves `vProfile`: `vProfile S v (π w) = vProfile S v w`. | — |
| `vProfile_eq_of_schemeOrbit` | 408-416 | Trivial direction: `SchemeOrbitPartition` refines `vProfile`-equality. | — |
| `vProfile_eq_imp_schemeOrbit` | 422-435 | S1.b — under the schurian axiom, equal `vProfile` implies a v-fixing scheme automorphism connecting the two vertices. | — |
| `vProfile_iff_schemeOrbit` | 437-446 | Step 1 of Theorem 2 (combined): for a schurian scheme, profile equality at `v` is exactly v-stabilized scheme-Aut orbit equivalence. | — |
| `SchemeGraph` | 465-474 | §5 A graph derived from a scheme by marking a set `J ⊆ Fin (rank + 1)` of relations as edges (`0 ∉ J`, so loopless). | Structure |
| `adj` | 480-483 | The derived adjacency matrix: `(v, w)` is an edge iff `relOfPair v w ∈ J`. | Definition, `noncomputable` |
| `adj_eq_one_iff` | 485-489 | Adjacency characterisation: `adj v w = 1 ↔ relOfPair v w ∈ J`. | — |
| `adj_eq_zero_iff` | 491-495 | Non-adjacency characterisation: `adj v w = 0 ↔ relOfPair v w ∉ J`. | — |
| `adj_self` | 497-500 | Loopless: `adj v v = 0`. | — |
| `adj_symm` | 502-506 | Symmetric: `adj v w = adj w v`. | — |
| `adj_eq_zero_or_one` | 508-513 | Adjacency takes values in `{0, 1}`. | — |
| `SchurianSchemeGraph` | 537-551 | §6 A `SchemeGraph` schurian w.r.t. graph automorphisms: `schurian_transitive` (orbits ⊇ relations) and `isAut_imp_isSchemeAut` (orbits ⊆ relations). | Structure |
| `relOfPair_aut_eq` | 557-562 | Graph automorphisms of a `SchurianSchemeGraph` preserve `relOfPair`. | — |
| `vProfile_aut_invariant` | 564-569 | A v-fixing graph automorphism of a `SchurianSchemeGraph` preserves `vProfile S v ·`. | — |
| `GraphOrbitFixing` | 586-590 | §7 The v-stabilized graph-Aut orbit relation: some `π ∈ Aut(adj)` with `π v = v` and `π w = u`. | Definition |
| `GraphOrbitFixing.refl` | 596-597 | Reflexivity of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.symm` | 599-606 | Symmetry of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.trans` | 608-615 | Transitivity of `GraphOrbitFixing`. | — |
| `vProfile_eq_imp_graphOrbit` | 623-632 | Step 1 (forward, graph-Aut terms): equal `vProfile` implies graph-orbit equivalence. | — |
| `graphOrbit_imp_vProfile_eq` | 634-642 | Step 1 (reverse, graph-Aut terms): graph-orbit equivalence implies equal `vProfile`. | — |
| `vProfile_iff_graphOrbit` | 644-652 | Step 1 (graph-Aut combined): `vProfile` equality iff v-stabilized graph-Aut orbit equivalence — the form bridging to `OrbitPartition adj P {v}` in T2.M4. | — |
| `refineStep_round1_pair_eq` | 709-757 | §8.a S2.a round-1 lemma: under `χ_v`, equal colour after one `refineStep` for non-`v` `w, u` forces `(adj w v, P w v) = (adj u v, P u v)`. | — |
| `refineStep_round1_adj_eq` | 759-767 | S2.a (adj-only): round-1 equality forces `adj w v = adj u v`. | — |
| `SchemeGraph.refineStep_round1_J_eq` | 769-799 | S2.a for scheme graphs: round-1 equality under `χ_v` forces matching J-class membership of `relOfPair v ·`. | — |
| `iterSignature` | 820-828 | §8.b The signature multiset of `w` computed against the `iter[k]` refinement of `χ_v`. | Definition |
| `iter_succ_eq_iff` | 830-841 | Round-by-round unfolding: `iter[k+1]` equality decomposes into `iter[k]` equality plus matching iter-k signatures. | — |
| `AssociationScheme.intersectionCount_via_w` | 843-869 | Scheme axiom in usable form: the count of `u'` with `(v,u') ∈ R_i` and `(w,u') ∈ R_l` equals `intersectionNumber i l (relOfPair v w)` — depends only on `vProfile w`. | — |
| `AssociationScheme.intersectionCount_eq_of_vProfile_eq` | 871-885 | Corollary: if `relOfPair v w = relOfPair v u`, the intersection counts at `(v,w)` and `(v,u)` coincide for every `(i, l)`. | — |
| `Step2_target` | 894-910 | §8.c Step 2 statement (target): for a `SchurianSchemeGraph` and compatible `P`, `warmRefine` cells refine `vProfile` classes. | Definition |
| `iter_succ_adj_eq` | 1047-1061 | §8.b.3 S2.a lifted to any depth ≥ 1: `iter[k+1]` equality between non-`v` vertices forces matching adj-to-`v`. | — |
| `warmRefine_adj_eq` | 1063-1078 | warmRefine form of S2.a: two non-`v` vertices in the same warmRefine cell share adjacency to `v`. | — |
| `SchurianSchemeGraph.warmRefine_J_eq` | 1080-1104 | Two non-`v` vertices in the same warmRefine cell share J-class membership of `relOfPair v ·` — the coarsest non-trivial Step 2 refinement. | — |
| `toSchemeProfile` | 1132-1165 | **T2.M4 assembly.** The `SchemeProfile` constructor: from a `SchurianSchemeGraph`, a P-invariance hypothesis, and a `Step2_target` witness, build the abstract `SchemeProfile G.adj P v`. | Definition, `noncomputable` |
| `schurian_scheme_profile_exists_of_step2` | 1167-1176 | Packages `toSchemeProfile` as the `Nonempty` existence result matching the `schurian_scheme_profile_exists` axiom. | — |
| `trivialPMatrix` | 1187-1188 | §9.1 The trivial `PMatrix`: every entry is `POE.unknown`. | Definition |
| `trivialPMatrix_invariant` | 1190-1194 | Every permutation preserves `trivialPMatrix`, discharging the P-invariance hypothesis automatically. | — |
| `SchurianSchemeGraph.toSchemeProfile_trivialP` | 1196-1203 | Specialisation of `toSchemeProfile` to trivial P: P-invariance is automatic, leaving only `Step2_target`. | Definition, `noncomputable` |
| `IsSchurianSchemeGraph'` | 1221-1227 | §9.2 Concrete schurian-scheme-graph predicate: `adj` arises as the derived adjacency of some `SchurianSchemeGraph`. | Structure |
| `theorem_2_HOR_concrete` | 1229-1256 | **Theorem 2 (HOR for schurian scheme graphs), concrete form.** From `IsSchurianSchemeGraph' adj` plus P-invariance plus a `Step2_target` witness, derive the `OrbitPartition ↔ warmRefine` equivalence. | — |
| `theorem_2_HOR_concrete_trivialP` | 1258-1271 | `theorem_2_HOR_concrete` for trivial P: P-invariance becomes automatic, leaving only `Step2_target`. | — |
| `trivialSchurianSchemeGraph` | 1285-1297 | §9.3 The trivial 1-vertex schurian scheme graph (empty edge set, identity automorphism only). | Definition |
| `trivialSchurianSchemeGraph_step2` | 1299-1305 | `Step2_target` holds trivially on the 1-vertex scheme: any two vertices in `Fin 1` are equal. | — |
| `theorem_2_HOR_trivial` | 1307-1325 | **First fully discharged Theorem 2 instance.** For the trivial 1-vertex scheme with trivial P, the `OrbitPartition ↔ warmRefine` equivalence holds unconditionally. | — |
| `step2_of_rank_le_one` | 1339-1378 | §9.4 Step 2 for rank ≤ 1 schurian scheme graphs: `vProfile` takes only `0` (at `v`) and `1` (elsewhere), so warmRefine separation suffices. | — |
| `theorem_2_HOR_concrete_rank_le_one` | 1380-1392 | **Theorem 2 unconditional for rank ≤ 1 schurian scheme graphs** (e.g. K_n). | — |
| `Step2_at_depth` | 1409-1418 | §10 Depth-parametrised Step 2: iter[k] equality implies `vProfile` equality; a depth-explicit version of `Step2_target`. | Definition |
| `step2_of_step2_at_depth` | 1420-1428 | `Step2_at_depth G P v k` for `k ≤ n` lifts to `Step2_target G P v`. | — |
| `ncard_setOf_eq_filter_card` | 1488-1495 | Bridge lemma: for `Fintype` and decidable `p`, `{x | p x}.ncard = (Finset.univ.filter p).card`. Bridges `Set.ncard`-based `schemePart_at` to `Finset.filter.card` outputs. | — |
| `schemePart_at` | 1497-1521 | §10.1 Recursive partition predicate at depth `k`: depth 0 is `χ_v`-equality; depth `k+1` adds matching (adj, P, depth-`k` class) counts over neighbours. | Definition |
| `iter_refines_schemePart_at` | 1581-1668 | §10.3 **Inductive refinement.** The `iter[k] χ_v` partition refines `schemePart_at G P v k`; the substantive intersection-number induction step of Step 2. | — |
| `Step2_converges_at` | 1686-1693 | §10.4 Step 2 convergence at depth `k`: `schemePart_at`-k equivalence implies `vProfile` equality. | Definition |
| `step2_of_converges_at` | 1695-1706 | Step 2 from convergence plus the inductive step: `Step2_converges_at G P v k` with `k ≤ n` gives `Step2_target G P v`. | — |
| `schemePart_at_one_to_v` | 1737-1787 | §10.5 **Depth-1 extraction.** For `w, u ≠ v`, `schemePart_at G P v 1 w u` forces `adj w v = adj u v ∧ P w v = P u v`. | — |
| `RelOfPairDetByAdjP` | 1816-1824 | §10.6 **Depth-1 separation hypothesis**: `(adj v ·, P v ·)` determines `relOfPair v ·` on non-`v` vertices. | Definition |
| `step2_converges_at_one_of_det` | 1826-1853 | **Step 2 convergence at depth 1 under depth-1 separation.** | — |
| `step2_of_det` | 1886-1896 | §10.7 `Step2_target G P v` from `RelOfPairDetByAdjP` (lifts depth-1 convergence). | — |
| `theorem_2_HOR_concrete_of_det` | 1898-1908 | **Theorem 2 unconditional under depth-1 separation** (Petersen-class). | — |
| `AdjSeparatesRelations` | 1931-1935 | §10.8 Cleaner reformulation of depth-1 separation: `(· ∈ J)` is injective on non-diagonal relations. P-free. | Definition |
| `relOfPairDetByAdjP_of_adjSeparates` | 1937-1953 | `AdjSeparatesRelations` implies `RelOfPairDetByAdjP`. | — |
| `adjSeparates_of_rank_two_J_singleton` | 1968-2012 | **`rank = 2` + `|J| = 1` ⇒ `AdjSeparatesRelations`.** The unique element of `J` distinguishes the two non-diagonal relations. | — |
| `relOfPairDetByAdjP_of_rank_two_J_singleton` | 2014-2021 | Combined: `rank = 2` + `|J| = 1` ⇒ `RelOfPairDetByAdjP`. | — |
| `theorem_2_HOR_concrete_rank_two_J_singleton` | 2023-2037 | **Theorem 2 unconditional for rank-2 + `|J| = 1` schurian scheme graphs** — covers Petersen, Kneser `K(5,2)`, Johnson `J(5,2)`. Axiom-clean. | — |
| `Depth2Det` | 2065-2081 | §10.9 **Depth-2 separation predicate**: the depth-2 invariant (adj/`P`-to-`v` plus the depth-1 block-degree vector) determines `relOfPair v ·`. Weaker than `RelOfPairDetByAdjP`. | Definition |
| `det2_of_det` | 2083-2090 | Depth-1 separation ⇒ depth-2 separation (ignores block-degrees). | — |
| `step2_converges_at_two_of_det2` | 2092-2121 | **Step 2 convergence at depth 2 under depth-2 separation.** | — |
| `step2_of_det2` | 2123-2138 | Lifts `Step2_converges_at … 2` to `Step2_target` (`n < 2` vacuous via `Fin` subsingleton). | — |
| `theorem_2_HOR_concrete_of_det2` | 2140-2152 | **Theorem 2 unconditional under depth-2 separation**; depth-2 analogue of `theorem_2_HOR_concrete_of_det`. | — |
| `schemePart_at_of_orbit` | 2185-2195 | A v-fixing `P`-preserving automorphism puts `w, u` in the same `schemePart_at k` class (`k ≤ n`). | — |
| `orbit_of_vProfile_eq` | 2197-2211 | `vProfile`-equality ⟹ `OrbitPartition` (schurian Step 1 plus P-invariance). | — |
| `ncard_eq_sum_POE` | 2213-2228 | P-value fibering of an `ncard`: the count splits over the finitely-many `POE` values of `P x ·`, dropping `P` from a block-degree count. | — |
| `IntersectionSeparates` | 2230-2239 | §10.10 **Intersection-number separation hypothesis**: `intersectionNumber j0 j0 ·` distinguishes the non-edge, non-diagonal relations (those adjacency cannot). | Definition |
| `depth2Det_of_intersectionSeparates` | 2241-2365 | **Discharges `Depth2Det`** for single-edge (`J = {j0}`) schurian scheme graphs with an edge-neighbour of `v` and intersection-number separation. | — |
| `theorem_2_HOR_concrete_intersectionSeparates` | 2367-2387 | **Theorem 2 unconditional for single-edge schurian scheme graphs with intersection-number separation** — first genuinely rank-≥-3 coverage (e.g. the 7-cycle). Strictly subsumes the rank-2/`|J|=1` case. Axiom-clean. | — |
| `RelIsolatedAt` | 2415-2422 | §10.11 **Relation-isolation predicate**: relation `l`'s `schemePart_at k` class is exactly `R_l` from `v`. The bootstrap's central object. | Definition |
| `vProfile_imp_schemePart_at` | 2424-2433 | The free ⊇ direction: same relation with `v` ⟹ same `schemePart_at k` class. | — |
| `schemePart_at_le` | 2435-2446 | `schemePart_at` is downward-monotone in the depth. | — |
| `relCommon_eq_intersectionNumber` | 2448-2463 | Common-neighbour count = structure constant: `#{u' : (v,u')∈R_l ∧ (z,u')∈R_m} = p^{relOfPair v z}_{l,m}`. | — |
| `isolatedCount_eq` | 2465-2521 | **The reusable counting heart**: a depth-`k`-isolated `l` lets `schemePart_at (k+1)` pin the intersection number `p^{·}_{l,j0}` (block-degree into `R_l`, summed over `P`). | — |
| `relIsolatedAt_one_j0` | 2523-2559 | **Base case**: the edge relation `j0` is isolated at depth 1. | — |
| `relIsolatedAt_zero` | 2561-2575 | The diagonal `R_0 = {v}` is isolated at every depth. | — |
| `relIsolatedAt_mono` | 2577-2592 | Isolation is upward-closed in depth (`k ≤ j ≤ n`). | — |
| `relIsolatedAt_succ` | 2594-2642 | **The bootstrap step**: a finset `Iso` of depth-`k`-isolated relations plus a separation pinning `i` by `(adjacency, counts into Iso)` ⟹ `i` is isolated at depth `k+1`. | — |
| `convergence_of_all_isolated` | 2644-2653 | All relations isolated at depth `k` ⟹ `Step2_converges_at G P v k` (`schemePart_at k` = `vProfile` partition). | — |
| `theorem_2_HOR_concrete_of_isolation` | 2655-2674 | **Theorem 2 from an isolation chain** — the general engine. Exhibiting that every relation isolates by depth `k ≤ n` gives Theorem 2 unconditionally. Axiom-clean. | — |
| `theorem_2_HOR_concrete_intersectionSeparates3` | 2676-2743 | **Theorem 2 for depth-3 single-anchor schemes** (e.g. the 9-cycle) — reaches rank-≥-4 schemes the depth-2 result cannot. Axiom-clean. | — |

## ChainDescent/CascadeOracle.lean

The a-priori cascade-oracle Lean contract (plan: `docs/Archive/ChainDescent/chain-descent-cascade-oracle-lean-brief.md`). Builds axiom-clean (only `refineStep`/`refineStep_iff` + Lean foundationals), no `sorry`. Phase A = soundness/validity, Phase B = the completeness reduction (wired to the axiom-free orbit-recovery theorems), Phase C = the residual obligations: verdict iso-invariance is *discharged conditionally* (`verdictIsoInvariant_of_complete` — it reduces to localisation), and localisation is *split* into (1a) bounded-depth recoverability — **proved** on the cascade class (`RecoverableByDepth` + `recoverableByDepth_cfi`/`_scheme`, anchored by `cellsAreOrbits_of_discrete`) — and (1b) intermediate-to-deep bridging, **open but not GI ∈ P** (cascade-class construction correctness). Only general-class completeness is the GI ∈ P obligation. §C.0 also proves the deferred-decisions foundation `real_stays_real`.

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `mono` | 59-68 | §C.0 Orbit monotonicity: an `Aut_{S'}`-orbit pair stays an orbit pair at every smaller individualized set `S ⊆ S'`, so a certified merge can be reused at shallower nodes. | — |
| `real_stays_real` | 70-78 | §C.0 Deferred-decisions foundation: a genuine decision (no orbit relation) at `S` is still genuine at every larger `S' ⊇ S`, so deferring a real decision never loses it. | — |
| `orbitPartition_of_support_disjoint` | 112-126 | §C.0.1 **Support backbone.** An automorphism that fixes the individualized set `S` pointwise and sends `v ↦ w` certifies that `v, w` share an `Aut_S`-orbit. | — |
| `exists_orbit_witness_of_aut` | 128-138 | §C.0.1 **Availability depth.** A symmetry of support size `s` keeps its orbit pair certifiable down to individualized sets of size `n − s` — full-support symmetries only at the root, transpositions almost to the leaves. | — |
| `CascadeOracleSpec` | 140-152 | The a-priori cascade-oracle interface: at an internal descent node, return either `none` or a verified automorphism merging two representatives. The cascade analogue of `LinearOracleSpec` (not leaf-gated). | Definition |
| `some_isAut` | 159-167 | Soundness: whatever permutation the oracle returns is guaranteed to be an automorphism of `adj`. | — |
| `OrbitMapSpec` | 169-181 | The oracle's soundness contract: every merge it returns is a genuine `Aut_D`-orbit pair — the property that makes pruning the merged branch safe. | Definition |
| `merged_sameCell` | 183-194 | A sound oracle only ever merges vertices that 1-WL already left in the same cell, so it never collapses across cells. | — |
| `OrbitRecoverableAt` | 216-225 | The orbit-recovery target at `S`: the `Aut_S`-orbit relation equals the 1-WL cell relation, so refinement computes orbits and a complete oracle exists. | Definition |
| `orbitRecoverable_of_cascade` | 227-235 | On the cascade class, orbits are recoverable at some set of size ≤ `k` — the general foundation behind every cascade-class oracle instance. | — |
| `orbitRecoverable_cfi` | 237-245 | Odd-degree CFI graphs are orbit-recoverable at depth ≤ `cfi_depth_bound h` (axiom-free). | — |
| `orbitRecoverable_scheme` | 247-257 | Rank-2, single-edge-class schurian scheme graphs are orbit-recoverable at depth 1 (axiom-free). | — |
| `CellsAreOrbits` | 259-272 | The genuinely-open half of orbit recovery: every same-cell pair is a real `Aut_S`-orbit pair. Holds at cascade and discretizing depth, fails at generic intermediate nodes — this predicate names the open localisation content. | Definition |
| `orbitRecoverableAt_iff_cellsAreOrbits` | 274-283 | Orbit recoverability is exactly `CellsAreOrbits` (the other half is unconditional), pinning localisation to a single implication. | — |
| `cellsAreOrbits_of_discrete` | 285-297 | **Recursion-bottom anchor.** At any discretizing depth `CellsAreOrbits` holds for free, so localisation is never GI-hard — the descent can always deepen to where cells = orbits. | — |
| `isAut_swap_of_twin` | 326-360 | A twin pair's transposition is an automorphism: if `v, w` have identical adjacency to every other vertex of a simple graph, `swap v w` preserves `adj`. Shared with the linear oracle's twin `ConfigSwap`. | — |
| `orbitPartition_swap_of_twin` | 362-427 | An order-undecided twin pair `v, w ∉ S` is an `Aut_S`-orbit pair at **any** individualized set, witnessed by the transposition `(v w)`. The reconstruction core behind the twin-endpoint and twin-cells results. | — |
| `cellsAreOrbits_of_compl_card_le_two` | 429-543 | **Twin endpoint of the support spectrum.** When at most two vertices stay un-individualized (`|Sᶜ| ≤ 2`), `CellsAreOrbits` holds via the omitted pair's transposition; with `cellsAreOrbits_of_discrete` it pins both ends. | — |
| `cellsAreOrbits_of_twin_cells` | 545-601 | `CellsAreOrbits` at **arbitrary** support whenever every same-cell pair is an order-undecided twin — the genuine-twin / module abelian regime (not CFI, which has no twins). The twin-reconstructible slice of the open localisation obligation. | — |
| `orbitRecoverableAt_of_twin_cells` | 603-622 | Oracle-vocabulary form of `cellsAreOrbits_of_twin_cells`: on the twin regime refinement computes the orbit partition at any node, with no depth bound. | — |
| `RecoverableByDepth` | 624-633 | Cascade-class membership for the oracle contract: there is a polynomially-bounded depth at which cells = orbits (the bound carries all the content). | Definition |
| `recoverableByDepth_of_cascade` | 635-641 | Cascading at depth `k` gives `RecoverableByDepth … k` — the cascade-class foundation in oracle-contract form. | — |
| `recoverableByDepth_cfi` | 643-649 | **(1a), proved for CFI** (axiom-free, odd-degree): recoverable by depth `cfi_depth_bound h` (≤ baseSize ≤ n/6). | — |
| `recoverableByDepth_scheme` | 651-663 | **(1a), proved for schemes** (axiom-free, rank 2 / `|J| = 1`): recoverable by depth 1, at the very node the oracle acts on. | — |
| `recoverableByDepth_univ` | 665-672 | Every graph is trivially recoverable by depth `n` (individualize everything), so only the *polynomial* depth bound is cascade-class content. | — |
| `CascadeComplete` | 679-686 | Completeness contract: the oracle certifies every genuine `Aut_D`-orbit pair; with soundness it then computes the orbit relation exactly. | Definition |
| `certifies_iff_orbit` | 688-702 | For a sound and complete cascade oracle, it returns `some` exactly on the pairs sharing an `Aut_D`-orbit. | — |
| `CellComplete` | 704-711 | The polynomial completeness contract: the oracle certifies every pair sharing a 1-WL cell (refinement-decidable). | Definition |
| `complete_of_cellComplete_recoverable` | 713-726 | **Key theorem.** At an orbit-recoverable node, certifying every same-cell pair already certifies every orbit — reducing orbit-completeness to a polynomial check. | — |
| `VerdictIsoInvariant` | 773-786 | Iso-invariance contract (strategy §15 gap 2): the oracle's verdict depends only on the iso-invariant 1-WL partition. Derivable — see `verdictIsoInvariant_of_complete`. | Definition |
| `cascadeComplete_of_localization` | 788-799 | Capstone: cell-completeness plus all-nodes recoverability yields `CascadeComplete`, naming the open localisation obligation as its hypotheses. | — |
| `cascadeComplete_of_cellsAreOrbits` | 801-812 | Capstone stated against the single open implication: cell-completeness plus `CellsAreOrbits` at every node yields `CascadeComplete`. | — |
| `verdictIsoInvariant_of_complete` | 814-829 | **Key theorem.** A sound, complete oracle at orbit-recoverable nodes is automatically iso-invariant, so iso-invariance is part of localisation rather than a separate obligation. | — |
| `computes_orbits_of_complete` | 831-843 | Capstone: a sound and complete cascade oracle computes the `Aut_D`-orbit relation exactly (program-level correctness, given the completeness obligation). | — |

## ChainDescent/LinearOracle.lean

The linear-oracle / abelian-stripping work (tractable-buildout B2; plan + status in `docs/chain-descent-linear-oracle.md` §8.2). Built on the §15.8 scaffolding (`DirAssignment`/`flipPair`/`LinearOracleSpec`/`LeafTwistSpec`/`canonAdj`). Builds axiom-clean (`refineStep`/`refineStep_iff` + foundationals), no `sorry`. **B2 soundness core DONE 2026-05-30:** §L.1 soundness anchor, §L.2 the *forced* candidate twist (rank rebasing — the construction is determined, not searched; the `canonAdj_rebase` bridge), §L.3 abelian `Z₂^d` structure. Remaining: `canonForm` lex-min tie (needs descent-with-pruning model), completeness, lifting twists to subgroup `N` (Part A).

### §L.1 — Soundness anchor (B2.1)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `RealizesFlip` | 52-61 | **Soundness anchor.** The relation "twist `t` relabels branch `σ`'s leaf to the flipped branch `flipPair σ a b`'s leaf" — the `LeafTwistSpec` conclusion with the partner branch pinned to the flip, i.e. the pruning justification. | Definition |
| `TwistWitness` | 63-83 | The verified data a twist discovery returns: the decided pair `(a,b)`, the candidate permutation `t`, its `IsAut` proof (the §4.5 edge-check, sole soundness anchor), and a `RealizesFlip` proof. | Structure |
| `twistOracle` | 85-95 | A concrete `LinearOracleSpec` parameterised by an abstracted `discover` function (C#-side canonical-id matching); returns the verified automorphism from a `TwistWitness`, `none` otherwise. Verification lives inside the witness, so every output is a genuine automorphism. | Definition |
| `twistOracle_leafTwist` | 97-116 | **Key theorem (B2.1 discharge).** `twistOracle` satisfies `LeafTwistSpec`, with the flipped branch as the explicit witness `σ' = flipPair σ` (sharper than the bare existential) — closing the pruning-justification contract for any sound discovery. | — |

### §L.2 — The forced candidate twist (B2.2 + most of B2.3)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `relabelMatrix_labelledAdj` | 141-150 | Relabelling composes: `relabelMatrix t (labelledAdj s adj) = labelledAdj (t * s) adj` — the `Equiv.Perm` group action on labelled matrices. | — |
| `canonAdj_eq_labelledAdj` | 152-157 | `canonAdj σ = labelledAdj (rankPerm π_σ) adj` for any discreteness proof; holds by `rfl`. | — |
| `canonAdj_rebase` | 159-174 | **The rebasing bridge.** Relabelling `σ`'s canonical leaf by the rank rebasing `rankPerm π_{σ'} * (rankPerm π_σ)⁻¹` yields `σ'`'s leaf; the flip is the `σ' = flipPair σ` instance. | — |
| `branch_discrete` | 176-182 | A branch's warm-refined colouring is discrete at a leaf, derived exactly as `canonAdj` derives it so the rank permutations match definitionally. | — |
| `candidateTwist` | 184-192 | **The forced candidate twist** for decision `(a,b)`: the rank rebasing `rankPerm π_flip * (rankPerm π_σ)⁻¹`. Always realises the flip; the twist is determined, not searched. | Definition, `noncomputable` |
| `candidateTwist_realizesFlip` | 194-201 | The forced candidate always realises the flip — the construction is forced, with no ambiguity. | — |
| `candidateTwist_unique` | 203-215 | **Determinacy.** The candidate is the unique permutation rank-aligning `σ` to the flipped branch — the leaf-level iso-invariance gate, making twist discovery deterministic in iso-invariant rank data. | — |
| `twistWitness_of_isAut` | 217-234 | The oracle reduces to one check: a verified-automorphism forced candidate yields a complete `TwistWitness`. Discovery is a single decidable edge-check. | Definition, `noncomputable` |
| `canonicalTwistOracle` | 235-249 | **The canonical twist oracle.** A fully concrete `LinearOracleSpec`: for the selected pair, compute the forced candidate and return it iff it verifies as an automorphism. The only abstracted piece is pair selection (soundness-irrelevant). | Definition, `noncomputable` |
| `canonicalTwistOracle_leafTwist` | 251-259 | **Key theorem.** `canonicalTwistOracle` satisfies `LeafTwistSpec` (it is a `twistOracle`) — a concrete verified linear oracle, sound by construction. | — |

### §L.3 — Abelian structure (B2.4, partial)

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `candidateTwist_flip_inv` | 282-291 | **`Z₂` involution.** The forced candidate for the flip-back is the inverse of the candidate for the flip; with `flipPair_comm` this is the elementary-abelian `Z₂^d` structure of the residual. | — |

### §L.4 — Completeness / effectiveness (when the oracle fires)

Characterizes *when* the oracle fires and proves firing is semantically justified. The
oracle is complete exactly on the **abelian regime** (forced candidate ∈ Aut) — the
calculator §6 boundary; the general converse fails (conjugation gap). The
abelian-sufficiency lemma (forced candidate IsAut for genuine abelian flips, via
`warm_6_2` rank machinery) is the open core scoped in the §L.4 doc-comment.

| Name | Description | Notes |
|------|-------------|-------|
| `candidateTwist_mul_rankPerm` | 319-327 | The forced candidate satisfies the rank-alignment equation `candidate · π_σ = π_flip` (the inverse cancels). | — |
| `isAut_candidateTwist_iff_aligned` | 329-344 | **Firing characterisation.** The forced candidate is an automorphism iff some automorphism is rank-aligned (`g · π_σ = π_flip`) — so the whole completeness question is "does a rank-aligned automorphism exist?" | — |
| `RealizableFlip` | 346-352 | The decision is a genuine `Aut(adj)` symmetry: some automorphism realises the flip (the two branches are isomorphic) — what pruning should require. | Definition |
| `realizableFlip_of_isAut_candidateTwist` | 354-365 | **Firing is semantically justified.** When the forced candidate verifies, the branches are genuinely `Aut(adj)`-equivalent (the candidate is the witness) — pruning reflects a real symmetry. | — |
| `canonicalTwistOracle_isSome_iff` | 367-383 | **Key theorem.** Given the pair selector returns `(a,b)`, the oracle fires iff the forced candidate is an automorphism — the entire completeness question is one decidable edge-check. | — |
| `candidateTwist_flipBack_isAut` | 385-396 | **`Z₂`-direction consistency.** If the forced candidate for `σ → flip` verifies, so does the candidate for the flip-back — the oracle prunes both directions of a genuine `Z₂` decision consistently. | — |

### §L.5 — Toward abelian sufficiency (partial)

The open core of completeness — *forced candidate ∈ Aut for abelian decisions* — needs
gadget-level rank-alignment (at a leaf both branches are discrete, so `warm_6_2`'s
partition equality is vacuous; the content is in the rank order). Provable progress:

| Name | Description | Notes |
|------|-------------|-------|
| `rankPerm_comp` | 421-441 | **Rank reindexing.** `rankPerm (χ ∘ e) = rankPerm χ · e` — relabelling conjugate-shifts the rank permutation, the precise reason colouring-alignment yields a conjugate of the realizing automorphism rather than the forced candidate (the conjugation gap). | — |
| `candidateTwist_eq_one_of_rankPerm_eq` | 443-454 | **Absorbed decision.** Equal leaf rank permutations force the candidate to be the identity — the degenerate end of the abelian regime. | — |
| `isAut_candidateTwist_of_rankPerm_eq` | 456-464 | The absorbed decision fires: the forced candidate (the identity) is an automorphism. | — |

### §L.7 — The CFI bridge (M1b): candidate as a conjugate of a graph automorphism

Now that `refineStep` is concrete, the cross-config transport (`§16.2b` in ChainDescent.lean)
lets us express the forced candidate via a *real* automorphism. A **config-swap** `g` carries the
σ-branch config onto the flip-branch config; it forces `π_σ = π_flip · g`, so the candidate is the
`π_σ`-conjugate of `g⁻¹`. This reduces the opaque `IsAut candidate adj` to the structural gadget
rank-alignment, isolating the genuine CFI nut (shared with Tier-3a B1 `hwit`): (1) a config-swap
exists, (2) its `π_σ`-conjugate is an automorphism.

| Name | Description | Notes |
|------|-------------|-------|
| `vertexRank_comp` | 603-621 | `vertexRank (χ ∘ g) v = vertexRank χ (g v)` — a pure `Finset.card` reindex along `g`. | — |
| `ConfigSwap` | 623-635 | A config-swap for decision `(a,b)`: a graph automorphism carrying the σ-branch configuration onto the flip-branch configuration (fixes `χι`, sends `σ.σ` to `(flipPair σ).σ`). For CFI, the gadget twist swapping the decided pair. | Structure |
| `configSwap_rankPerm` / `_flip` | The leaf rank perms differ by `g`: `π_σ = π_flip · g` (resp. `π_flip = π_σ · g⁻¹`), from transport + `vertexRank_comp`. | axiom-light |
| `configSwap_rankPerm_flip` | 654-661 | `π_flip = π_σ · g⁻¹` — the rearrangement of `configSwap_rankPerm`. | — |
| `candidateTwist_eq_conjugate` | 663-673 | **The rank-space reduction.** Given a config-swap `g`, the forced candidate is the `π_σ`-conjugate of `g⁻¹` (`candidateTwist = π_σ · g⁻¹ · π_σ⁻¹`) — the opaque rebasing exposed as a conjugate of a genuine automorphism. | — |
| `isAut_candidateTwist_iff_conjugate` | 675-686 | **The reduction.** `IsAut candidate adj ↔ IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj` — the rank-space firing obligation is exactly the gadget rank-alignment, the concrete nut shared with Tier-3a B1. | — |

**§L.7b — vertex-model soundness (Approach C, the faithful C# model).** A config-swap is a real
graph automorphism, so both branches give the *same canonical leaf* — no rank-alignment needed. This
is the soundness the C# `TwistConstruction` actually uses (it verifies a vertex automorphism, not the
rank rebasing).

| Name | Description | Notes |
|------|-------------|-------|
| `canonAdj_eq_of_configSwap` | 697-712 | **Equal canonical leaves.** A config-swap implies both branches produce the identical canonical leaf — the vertex-model soundness statement (pruning the flip branch loses nothing), needing no rank-alignment. | — |
| `realizableFlip_of_configSwap` | 714-728 | A config-swap implies `RealizableFlip` (identity witness, since the leaves coincide) — the decision is a genuine `Aut(adj)` symmetry with no rank-alignment obligation. | — |

**§L.8 — CFI completeness: config-swap from a swapping automorphism (M1c step 3, the cascade-1b bridge).**
*Where a config-swap comes from.* A swapping automorphism `g` (`g a = b`, `g b = a`) is exactly an
`OrbitPartition adj P S a b` witness specialised to the size-2 decision cell — the cascade oracle's
currency. So linear-oracle CFI completeness reduces to the **shared cascade-1b** obligation
(bounded-depth half `recoverableByDepth_cfi` proved; decision-node-depth bridge open, *not* `GI∈P`).

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_aut` | 760-803 | **General constructor (the `hwit` entry point).** *Any* swapping automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and preserves `σ.σ` *off the flip pair* (`σ.σ (g v)(g u) = σ.σ v u` for `(v,u) ∉ {(a,b),(b,a)}`) is a `ConfigSwap` — `g` need **not** be a transposition (may move the whole coupled component). Removes the config-swap *packaging* from the open content: once the CFI gadget twist `g` and its off-pair `σ`-action are known, the `ConfigSwap` is built with no rank-alignment. | Definition |
| `configSwap_of_swap` | 805-856 | **Closed instance (the `Z₂` twin-swap).** A σ-cell-coherent transposition automorphism (`g` swaps `a,b`, fixes the rest and `χι`) is a `ConfigSwap` — the simplest genuine abelian decision. Now a thin specialisation of `configSwap_of_aut` (transposition ⇒ off-pair preservation = σ-cell-coherence). | Definition |
| `configSwap_of_twin` | 858-886 | **The twin → config-swap bridge.** An (adj, σ)-twin decision pair (adjacency-twin on a simple graph plus σ-cell-coherent, `χι a = χι b`) admits a `ConfigSwap` via the transposition `(a b)` — the linear-oracle analog of `cellsAreOrbits_of_twin_cells`, both oracles firing on the same twin/module class through one shared lemma. Not CFI (which has no twins). | Definition |
| `ConfigSwapRecoverable` | 888-898 | **Decision-node recoverability** (the named cascade-1b obligation for the linear oracle): every leaf decision admits a config-swap. The graph-level analog of `AbelianSufficiencyHolds`; open discharge `configSwapRecoverable_of_cfi` is downstream. | Definition |
| `canonAdj_eq_of_configSwapRecoverable` | 900-911 | **Capstone (pruning soundness).** Config-swap-recoverability implies both branches give the identical canonical leaf at every decision — reducing the oracle's effectiveness to the single `ConfigSwapRecoverable` hypothesis. | — |
| `realizableFlip_of_configSwapRecoverable` | 913-924 | **Capstone (real symmetry).** Config-swap-recoverability implies every leaf decision is a genuine `Aut(adj)` symmetry — vertex-model completeness, no rank-alignment needed. | — |

**§L.9 — CFI gadget twist fires the oracle (Phase 6a: wiring the Stage-3 cycle-space flip).** The
Stage-3 gadget flip (`CFI.lean §15`, `IsCFI'.cfiFlipAut`) is now constructed; this section wires it into
`configSwap_of_aut` and reduces `ConfigSwapRecoverable` for CFI to the existence of the right cycle `F`
per decision.

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_cfiFlipAut` | **The CFI gadget twist is a config-swap** (unconditional bridge). `configSwap_of_aut` instantiated with `g := cfiFlipAut F` (an `Aut(adj)` involution by `isAut_cfiFlipAut`): if the flip swaps `(a,b)`, fixes `χι`, and carries `σ` off the pair, it is a `ConfigSwap`. The concrete soundness — the vertex-space gadget twist (the C#'s witness) fires the oracle, no rank-alignment. | Definition |
| `CFIGadgetFlippable` | **The named cascade-1b residual.** Every leaf decision admits an even-symmetric cycle `F` whose gadget flip swaps `(a,b)`, fixes `χι`, carries `σ` off the pair. Commits the CFI witness to the gadget-flip mechanism (matching the C#); the open content is purely `F`'s existence per decision (cascade-1b). | Definition |
| `configSwapRecoverable_of_cfi` | **`ConfigSwapRecoverable` for CFI via the gadget flip.** `CFIGadgetFlippable h → ConfigSwapRecoverable` — the discharge reduced to its irreducible combinatorial core (the decision-local even cycle's existence). Feeds the capstones ⟹ oracle fires on every CFI decision. | — |

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
| `swapsConfig_off_pair_of_local` | **The σ-off-pair reduction (general `g`, reusable).** Any `g` swapping `(a,b)`, fixing decided vertices off `{a,b}`, preserving the decided set and `P₀`, satisfies the off-pair condition given only **σ-cell-coherence** at `(a,b)`. Off-D via `agrees_off` + P₀-invariance; on-D via the coherence case-analysis. | — |
| `preserves_D_of_involutive_local` | Decided-set preservation for an involutive local swap (`g x ∈ D ↔ x ∈ D` from `g²=id` + swap + fix-off-`{a,b}`). The `hgD` input above, discharged for the gadget flip. | — |
| `cfiFlipAut_fixesχι_of_support` | **The `hgχ` reduction.** The flip fixes `χι` once it does on the F-touched gadgets — Phase-4 locality fixes every `F`-free gadget outright. Reduces global `hgχ` to χι-coherence on the (small) F-support. | — |
| `configSwap_of_cfiFlipAut_local` | **The reduced bridge.** A `ConfigSwap` from {`F` even+symmetric, swap, **F is D-local**, σ-cell-coherent, `P₀` Aut-invariant, χι-coherent on F-support} — the three `configSwap_of_aut` conditions discharged via the reductions above. | Definition |
| `CFIGadgetFlippableLocal` | The reduced per-decision predicate: an even-symmetric **D-local** `F` whose flip swaps `(a,b)`, with σ cell-coherent and χι coherent on the F-support. The conditions are now the descent-coherence / cycle-locality (cascade-1b) facts. | Definition |
| `configSwapRecoverable_of_cfi_local` | `ConfigSwapRecoverable` from `CFIGadgetFlippableLocal` (+ `P₀` Aut-invariance) — the discharge via the decoupled hypotheses. | — |

**§L.9 (C1b.1) — the CFI glue: parity-pair decisions.** Reduces `CFIGadgetFlippableLocal` to the
explicit-edge form, discharging the swap obligation in advance (via C1b.0).

| Name | Description | Notes |
|------|-------------|-------|
| `CFIParityDecisionFlippable` | The reduced cascade-1b hypothesis: every decision `(a,b)` is the parity-pair of a base edge `{v,w}` (`a = e^{b₀}_{v→w}`, `b = e^{¬b₀}`) admitting an even-symmetric cycle `F` with `{v,w} ∈ F`, D-local, σ/χι cell-coherent. The swap is no longer an obligation (it's `cfiFlipAut_swaps_endpointVertex`); only cycle existence + coherence remain. | Definition |
| `cfiGadgetFlippableLocal_of_parity` | **The C1b.1 glue.** `CFIParityDecisionFlippable → CFIGadgetFlippableLocal` — the body's two swap conjuncts from `cfiFlipAut_endpointVertex` + `F v w = true`; the rest passes through. Open content narrows to C1b.2 (cycle exists) + C1b.3 (decisions are parity-pairs + coherence). | — |

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
| `RankAligned` | 501-509 | The algebraic firing condition: a rank-aligned automorphism exists (`∃ g ∈ Aut(adj), g · π_σ = π_flip`). The oracle fires exactly when this holds. | Definition |
| `isAut_candidateTwist_iff_rankAligned` | 511-519 | **Interface.** The forced candidate is an automorphism iff `RankAligned` — the completeness question restated against the named predicate. | — |
| `AbelianSufficiency` | 521-531 | **The per-decision relativized completeness target.** `RealizableFlip → IsAut candidate`: if the flip is a real symmetry then the forced candidate verifies. False in the non-abelian regime (the wall); the claim to discharge on the abelian/cascade class. | Definition |
| `oracleFires_of_abelianSufficiency` | 533-548 | **Capstone (what suffices).** `AbelianSufficiency` plus a real symmetry implies the oracle fires — the linear-oracle analog of cascade's `cascadeComplete_of_localization`. | — |
| `abelianSufficiency_of_rankPerm_eq` | 550-561 | **Non-vacuous closed instance.** The absorbed decision is abelian-sufficient (candidate `= 1 ∈ Aut` outright) — validates the scaffold against a real instance. | — |
| `AbelianSufficiencyHolds` | 563-571 | The graph-level discharge target: every leaf decision is abelian-sufficient. Open obligation `abelianSufficiencyHolds_of_cfi` is downstream (via `theorem_1_HOR_cfi_oddDeg`, the same nut as Tier-3a B1's `hwit`). | Definition |
| `oracleFires_of_abelianSufficiencyHolds` | 573-587 | **Graph-level capstone.** `AbelianSufficiencyHolds` implies the oracle fires at every leaf decision that is a real symmetry — relativized completeness on the abelian class. | — |

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
| `LayerChain.trivial` | §A3 **The trivial chain** `AutGroup adj ⊵ ⊥` (length 1); witnesses `LayerChain` is inhabited. | Definition |

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
| `IsBase adj P T` | **Phase A interface.** `T` is a *base* of the `P`-preserving automorphism group: its pointwise stabilizer is trivial, so the `Aut_T`-orbit relation is equality — the chain's bottom `H_k = {1}`. | Definition |
| `LayerStep adj P T S` | **Phase A interface — the per-layer transfer obligation.** `CellsAreOrbits T → CellsAreOrbits (T ∪ S)`: individualizing the increment `S` brings cells down to `Aut_{T∪S}`-orbits (paper §4.2.5 transferred to `G`). The contract the composition induction consumes; discharged in Phase D. | Definition |
| (cascade-class predicate) | `RecoverableByDepth adj P bound` (in `CascadeOracle.lean`) — Tier-1 (`recoverableByDepth_cfi`) / Tier-2 (`recoverableByDepth_scheme`) instances already proved. | (existing) |

### Phase C — composition theorem

| Name | Description | Notes |
|------|-------------|-------|
| `discrete_of_cellsAreOrbits_base` | 69-76 | **(C1) Finish.** At a base `T` where cells already coincide with `Aut_T`-orbits, warm refinement at `T` is `Discrete` — the cascade reaching full canonization. | — |
| `cellsAreOrbits_compose` | 78-91 | **(C2) Composition induction.** From layer 1's unconditional `CellsAreOrbits` at `T 0` and a `LayerStep` at each subsequent layer, `CellsAreOrbits` holds at the final cumulative set `T k`. | — |
| `cumulative_card_le` | 93-99 | **Depths add (cardinality).** The cumulative individualization set `⋃_{i≤k} S i` has size at most `Σ_{i≤k} f i` when each layer is bounded by its depth `f i`. | — |
| `cascadeComposition` | 101-113 | **Theorem 3a (cascade composition) — headline, conditional form.** Cumulative sets with layer-1 recoverability, per-layer transfer steps, and the final set a base ⟹ warm refinement at `T k` reaches the discrete partition; with `cumulative_card_le` the cascade depth is `≤ Σ fᵢ`. Conditional on the `hstep` obligations (= §4.2.5, Phase D). | — |
| `cascadeComposition_single` | 121-124 | **Single-layer sanity check (k = 0).** One cascade-class layer that is a base reaches discreteness — recovers the Tier-1/Tier-2 orbit-recovery theorems as the composition's base case. | — |

### Phase D — discharging `LayerStep` (the §4.2.5 transfer), intrinsic route

Approach B (build-plan §3): stay on `Fin n`, reduce `LayerStep` to a witness-upgrade via
**set-monotonicity** of warm refinement (reusing `refineStep_iff`); the materialized-quotient
route was rejected (`refineStep` axiomatic, no cross-size API).

| Name | Description | Notes |
|------|-------------|-------|
| `Refines χ₁ χ₂` | `χ₁` refines `χ₂`: the partition of `χ₁` is finer (`χ₁ a = χ₁ b → χ₂ a = χ₂ b`). The partition order used for warm-refinement monotonicity. | Definition |
| `signature_refines` | 142-163 | **Crux of warm-refinement monotonicity.** If `χ₁` refines `χ₂`, equal `χ₁`-signatures give equal `χ₂`-signatures, since `signature χ₂` is the coarsening of `signature χ₁`. | — |
| `iterate_refineStep_refines` / `warmRefine_refines_initial` | warm refinement monotone in the initial colouring's partition order. | axiom-light |
| `individualizedColouring_refines` | 189-201 | Individualizing a superset gives a finer initial colouring: `T ⊆ T'` ⟹ `individualizedColouring n T'` refines `individualizedColouring n T`. | — |
| `warmRefine_indiv_mono` | 203-211 | **Set-monotonicity (the payoff).** Same `(T ∪ S)`-cell ⟹ same `T`-cell: 1-WL is monotone in the individualization set. The load-bearing lemma the docs had mis-cited as `warmRefine_refines`. | — |
| `WitnessUpgrade adj P T S` | **The genuine §4.2.5 content.** For `v, w` in the same `Aut_T`-orbit and the same `(T ∪ S)`-cell, the orbit relation upgrades to `Aut_{T∪S}`. The Phase-D interface predicate. | Definition |
| `layerStep_of_witnessUpgrade` | 225-232 | **The reduction — where Phase C meets the per-layer content.** A `WitnessUpgrade` discharges a `LayerStep`, via set-monotonicity then `CellsAreOrbits T` then the upgrade. | — |
| `layerStep_empty` / `layerStep_subset` / `layerStep_of_cellsAreOrbits` / `layerStep_of_discrete` | Trivial real instances: no-op layer (`S = ∅`), `S ⊆ T`, independently-recoverable target, and the discretizing recursion-bottom. | axiom-light |
| `witnessUpgrade_of_pathFixing` | 257-272 | **Bridge to harvested generators.** If every same-orbit, same-cell pair admits a `P`-preserving automorphism whose support avoids `T ∪ S` (fixes the committed path) and sends `v ↦ w`, the witness-upgrade holds — exactly what the cascade/linear oracles produce. | — |

### Step 5 — the synthesis (Theorem 3a reduced to harvested generators)

| Name | Description | Notes |
|------|-------------|-------|
| `cascadeComposition_pathFixing` | 291-312 | **Theorem 3a, reduced to harvested path-fixing generators.** Cumulative sets by increments, layer-1 recoverable, every layer's residual symmetry realized by path-fixing automorphisms (`hwit`), and the final set a base ⟹ discrete warm refinement at `T k`. Reduces all of Theorem 3a to the single hypothesis of per-layer path-fixing witness existence. | — |
| `cascadeComposition_twoLayer` | 314-329 | **Smallest genuine composition.** An outer cascade-class layer at `T₀`, an inner path-fixing layer with increment `S`, and the union a base ⟹ discreteness — the `CFI(scheme)` / `Scheme(CFI)` shape. | — |

**Phase 6b — CFI gadget flips discharge the Tier-3a `hwit`.** The Stage-3 gadget flip (`CFI.lean §15`)
discharges `cascadeComposition_pathFixing`'s `hwit` for a CFI layering, conditional only on the per-layer
existence of committed-set-avoiding gadget flips (the cascade-1b content).

| Name | Description | Notes |
|------|-------------|-------|
| `CFILayerGadgetFlippable` | Per-layer CFI gadget-flip existence: for each layer and same-orbit/same-cell pair `(v,w)`, an even-symmetric cycle `F` whose flip maps `v ↦ w` with `T i ∪ S i` in `F`-free gadgets. The `hwit` analog of the linear oracle's `CFIGadgetFlippableLocal`. | Definition |
| `cfiLayer_pathFixing_hwit` | **The `hwit` drop-in.** `CFILayerGadgetFlippable` (+ `P` Aut-invariant) ⟹ the Tier-3a `hwit` hypothesis, directly via `cfiFlipAut_pathFixing_witness`. | — |
| `cascadeComposition_cfi` | **Theorem 3a for CFI layers.** A CFI layering whose residual orbit maps are realised by committed-set-avoiding gadget flips reaches the discrete partition — `cascadeComposition_pathFixing` with `hwit` discharged by the Stage-3 flips (conditional only on the cascade-1b cycle existence). | — |
| `recoverableByDepth_of_pathFixing_layers` | 399-417 | **The harvest-window connector.** Lands `cascadeComposition_pathFixing`'s `Discrete` output onto the harvest `RecoverableByDepth` conclusion: a layer chain with per-layer path-fixing `hwit` and a base endpoint gives `RecoverableByDepth adj P b` at the chain-length bound. | — |
| `recoverableByDepth_of_cascadeComposition_cfi` | 419-432 | **CFI corollary of the connector.** `RecoverableByDepth` for a CFI layering via `cascadeComposition_cfi` — the connector with `hwit` discharged by the Stage-3 gadget flips. | — |
| `ResidualAut` | 447-453 | **Residual automorphism.** A `P`-preserving automorphism of `adj` fixing `S` pointwise — an element of the residual group `Aut_S^P`; the building block of the screen predicates. `OrbitPartition adj P S v w ↔ ∃ π, ResidualAut π ∧ π v = w`. | Definition |
| `ResidualAbelian` | 455-460 | **D2 — abelian residual.** The residual group `Aut_S^P` is abelian (any two residual automorphisms commute) — the screen's hidden-abelian / linear leg (calculator §6); the `¬IsBase`-guarded form is the D2 disjunct. | Definition |
| `orbitPartition_iff_residualAut` | 462-468 | `OrbitPartition adj P S v w` unfolds to a `ResidualAut` carrying `v ↦ w`. | — |
| `residualAut_eq_one_of_isBase` | 470-477 | Under a base (`IsBase`), every residual automorphism is the identity — it can move no point. | — |
| `residualAbelian_of_isBase` | 479-484 | **Trichotomy base case.** A trivial residual (under `IsBase`) is vacuously abelian, so `ResidualAbelian` holds at any base. | — |
| `residualAbelian_mono` | 486-493 | **D2 inherited down the descent.** `ResidualAbelian` passes from `S` to any `S' ⊇ S` (the residual shrinks to a subgroup of an abelian group). | — |
| `VisiblyRecoverable` | 516-532 | **D1 (explicit-chain form).** A single-vertex, per-step symmetry-only chain from `S₀` reaching `CellsAreOrbits` within a depth bound — the unconditional/cascade leg's structural witness, retained alongside the inductive `Findable`. | Definition |
| `recoverableByDepth_of_visiblyRecoverable` | 534-539 | **D1 leg (free).** `VisiblyRecoverable ⟹ RecoverableByDepth` — the chain ends on a `CellsAreOrbits` set within the bound. | — |
| `visiblyRecoverable_bound_mono` | 541-545 | `VisiblyRecoverable` is monotone in the depth bound (a looser bound is easier). | — |
| `cellsAreOrbits_empty_of_schurian` | 547-560 | **Schurian scheme graphs are vertex-transitive: `CellsAreOrbits adj P ∅`.** The `Aut`-orbit relation at `∅` is total (witness from `schurian_transitive` at the diagonal `R₀`), unblocking the symmetry-only first step. | — |
| `visiblyRecoverable_of_cellsAreOrbits_singleton` | 562-575 | **`CellsAreOrbits` at a singleton + vertex-transitivity ⟹ D1 at depth 1.** The one-step chain `∅ → {v}` is symmetry-only with `CellsAreOrbits {v}` as endpoint recovery. | — |
| `visiblyRecoverable_scheme` | 577-587 | **D1 instance — rank-2, `|J|=1` schurian scheme is visibly recoverable.** Validates `VisiblyRecoverable` against the proved depth-1 scheme orbit recovery (`orbitRecoverable_scheme`). | — |
| `SymmetryOnlyStep` | 591-604 | **D1 per-decision primitive (§6.10).** Individualizing `v` commits no real decision: `v`'s 1-WL cell is non-singleton and a single `Aut_S`-orbit. The non-singleton conjunct is load-bearing (forces `v ∉ S`); lifted out of `VisiblyRecoverable`. | Definition |
| `symmetryOnlyStep_of_cellsAreOrbits` | 606-616 | `CellsAreOrbits` upgrades any non-singleton cell to a `SymmetryOnlyStep` — the bridge from the recovery predicate to the screen primitive, and why `Discrete` (not bare `CellsAreOrbits`) is a non-false-walling stop (§6.11 F1). | — |
| `symmetryOnlyStep_empty_scheme` | 618-639 | **Scheme validation of the primitive.** A vertex-transitive schurian scheme is one orbit at `∅`, so individualizing any `v` (with `n ≥ 2`) is a `SymmetryOnlyStep`. | — |
| `Findable` | 658-670 | **The harvest-window screen (sequential D1/D2, §6.10+§6.11).** Least-fixed-point inductive: `recovered` (`Discrete` — the F1-correct stop), `abelian` (`ResidualAbelian ∧ ¬IsBase` — guarded D2), `step` (`SymmetryOnlyStep` + recurse). Bound-free classification; `¬Findable` is the seal's wall (IR-blind-spot / Cameron by residual order). | Inductive |
| `FindableWithin` | 681-699 | **`Findable` with its recovery depth (Phase 0).** Bound-indexed companion: `recovered`→`b=S.card`, `step` propagates `b`, `abelian` carries `RecoverableByDepth adj P b` as a field (the D2-bridge interface). De-vacuates the `∃ b` conclusion (`recoverableByDepth_univ`). | Inductive |
| `recoverableByDepth_of_findableWithin` | 701-711 | **Screen soundness — non-vacuous.** `FindableWithin adj P S b ⟹ RecoverableByDepth adj P b` at the carried bound: `recovered`/`step` free, `abelian` returns its carried recoverability field. | — |
| `findable_of_findableWithin` | 713-722 | Forgetting the bound (and the abelian recoverability witness) collapses `FindableWithin` to the bound-free `Findable` classification; the reverse needs the D2 bridge, so `FindableWithin` is strictly stronger. | — |
