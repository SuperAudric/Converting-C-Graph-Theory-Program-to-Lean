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
| `POE` | 76-80 | Partial-order entries: the three values `less`, `unknown`, `greater` that populate a `PMatrix`. | Inductive |
| `neg` | 93-97 | Antisymmetric reverse on one entry: swaps `less`/`greater`, fixes `unknown`. | Definition |
| `neg_neg` | 99-100 | `neg` is an involution: `neg (neg e) = e`. | `@[simp]` |
| `POE.swap` | 102-105 | σ-swap on one entry (the matrix-wide relabelling of the direction-symmetry argument); coincides with `neg`. | Definition |
| `POE.swap_swap` | 107 | σ-swap is an involution: `swap (swap e) = e`. | `@[simp]` |
| `swap_less` | 109 | `swap .less = .greater`. | `@[simp]` |
| `swap_greater` | 110 | `swap .greater = .less`. | `@[simp]` |
| `swap_unknown` | 111 | `swap .unknown = .unknown`. | `@[simp]` |
| `PMatrix` | 117-118 | The partial-order matrix type `Fin n → Fin n → POE`. | Definition |
| `swap` | 124-125 | Pointwise σ-swap of a `PMatrix`: swap `less` with `greater` at every entry. | Definition |
| `swap_swap` | 127-128 | σ-swap is an involution on `PMatrix`: `swap (swap P) = P`. | `@[simp]` |
| `Antisymmetric` | 130-132 | A `PMatrix` is antisymmetric when `P i j = POE.neg (P j i)` for all `i, j`. | Definition |
| `AdjMatrix` | 141-142 | Self-contained adjacency matrix on `Fin n`, wrapping a `Fin n → Fin n → Nat` field. | Structure |
| `applyGuess` | 146-153 | Apply a single guess `(a, b, dir)` to `P`: set `P a b := dir`, `P b a := neg dir`, leaving every other entry unchanged. Does not transitively close. | Definition |
| `applyGuess_swap` | 155-176 | Applying `(a, b, swap dir)` to the σ-swapped matrix equals σ-swapping after `applyGuess P a b dir` (needs `a ≠ b`); links the two guess directions through σ. | — |
| `closeStep` | 180-193 | Single-step transitive closure: derive `P i j` from a uniform chain `i → k → j`, with `less`-chains taking priority over `greater`-chains at ties. | Definition |
| `transitiveClose` | 195-199 | Transitive closure of a `PMatrix` by iterating `closeStep` `n*n` times — enough rounds to reach fixpoint. | Definition |
| `conflictMatrix` | 230-243 | Concrete 4-vertex witness with a conflicted pair `(0,1)` carrying both a `less`-chain and a `greater`-chain; refutes σ-swap commutation. | Definition |
| `closeStep_swap_false` | 262-271 | **Refutation:** `closeStep` does not commute with σ-swap unconditionally — the `less`-first tie-break is not σ-symmetric (fails on `conflictMatrix`). | — |
| `transitiveClose_swap_false` | 292-306 | **Refutation:** `transitiveClose` does not commute with σ-swap unconditionally (witnessed by `conflictMatrix`). | — |
| `Colouring` | 310-311 | A vertex colouring `Fin n → Nat`. | Definition |
| `signature` | 313-319 | Multiset signature of vertex `v` under colouring `χ` and state `(adj, P)`: the `(χ u, adj.adj v u, P v u)` tuples over all `u ≠ v`. | Definition |
| `POE.toNat` | 321-326 | Numeric code for a `POE` entry matching the C# packing: `less ↦ 0`, `unknown ↦ 1`, `greater ↦ 2`. | Definition |
| `encTuple` | 332-338 | Canonical injection of a signature tuple `(colour, edge-label, POE)` into `Nat` (Cantor pairing); mirrors the C# neighbour-tuple packing. | Definition |
| `sigKey` | 347-354 | Canonical refinement key of a vertex: its old colour followed by the sorted encoded signature multiset (the C# `[own-colour, sorted neighbour-tuples]`). | Definition |
| `sigKey_eq_iff` | 356-370 | Two vertices share a `sigKey` iff they have the same old colour and the same signature. | — |
| `warmRefine` | 399-409 | Warm 1-WL refinement: iterate `refineStep` `n` times from `initial`; concrete and computable. | Definition |
| `refineStep` / `refineStep_iff` | ~320-417 | **Concrete (2026-05-30, no longer axioms):** `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)` (own colour + sorted encoded signature = the C# `WarmPartition.RefineRound`); `refineStep_iff` (same colour ⟺ same old colour + same signature) is now a **theorem**. Removes `refineStep`/`refineStep_iff` from the axiom basis project-wide. Helpers: `POE.toNat`(_injective), `encTuple`(_injective), `sigKey`, `sigKey_eq_iff`. | Def + theorem |
| `samePartition` | 413-416 | Two colourings induce the same partition: `χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j` for every `i, j`. | Definition |
| `samePartition.refl` | 422 | `samePartition` is reflexive. | — |
| `samePartition.symm` | 424-425 | `samePartition` is symmetric. | — |
| `samePartition.trans` | 427-429 | `samePartition` is transitive. | — |
| `refineStep_refines` | 435-440 | **Refinement is split-only (one round).** Equal refined colour implies equal old colour. | — |
| `warmRefine_refines` | 442-468 | Warm refinement is split-only: equal warm-refined colour implies equal starting colour. | — |
| `iterate_closeStep_fix` | 500-506 | Iterating `closeStep` from a fixpoint of itself stays at that fixpoint. | — |
| `cell_split_uniform_false` | 571-596 | **Refutation:** cell-mates do not in general keep equal signatures after a guess plus TC (witnessed by `witnessP0`, the gap fixed only by singleton-cell `a`, `b`). | — |
| `refineStep_preserves_singleton` | 618-625 | One refinement round preserves a singleton: if no vertex shares `a`'s colour, none does after `refineStep`. | — |
| `iterate_refineStep_preserves_singleton` | 627-640 | Iterating refinement preserves a singleton for any number of rounds. | — |
| `signature_applyGuess_off` | 642-656 | Off the guessed pair, the guess is invisible: for `x ∉ {a,b}` the signature under `applyGuess P₀ a b dir` equals the signature under `P₀`. | — |
| `signature_eq_of_samePartition` | 658-685 | **Signature equality is a partition invariant of the colouring:** partition-equal colourings induce the same signature-equality relation between vertices. | — |
| `warm_6_2` | 687-764 | **§6.2 direction invariance.** With `a, b` `χι`-singletons, warm refinement after `a < b` and after `b < a` induce the same partition. | — |
| `signature_swap` | 768-778 | σ-swapping `P` relabels each signature's `POE` component by `POE.swap`, leaving colour and adjacency components untouched. | — |
| `warmRefine_swap` | 780-822 | **Direction-blindness (Q1).** Warm refinement on `P` and on its σ-swap induce the same partition. | — |
| `warmRefine_applyGuess_swap` | 824-834 | Warm refinement after `a < b` on `P₀` and after `b < a` on the σ-swapped `P₀` induce the same partition. | — |
| `applyGuess_comm` | 836-854 | **Q2 — guesses commute.** Guessing on `{a,b}` then `{b,c}` (pairwise-distinct vertices) gives the same `(adj, P)` as the reverse order, since the writes touch disjoint matrix entries. | — |
| `signature_agree_off` | 862-873 | If `P` and `Q` agree on every entry with an endpoint outside `D`, then off `D` they yield the same signature. | — |
| `warmRefine_agree_off'` | 875-922 | **§6.2 — composable cross-branch sharing.** Matrices agreeing off `D` and `samePartition`-equal starting colourings (with `D` all `χ`-singletons) yield the same warm-refined partition; the cross-level form that chains across descent levels. | — |
| `warmRefine_agree_off` | 924-958 | **§6.2 — the cell partition depends only on the matrix off the decision set `D`.** Matrices agreeing off `D` (its vertices `χι`-singletoned) yield the same partition; the same-`χι` specialisation of `warmRefine_agree_off'`. | — |
| `PartitionInvariant` | 975-979 | A target-cell selector is partition-invariant when it depends only on the partition a colouring induces, not on raw colour values. | Definition |
| `target_direction_blind` | 981-990 | **§6.2 spine — base case.** For a partition-invariant selector, the target cell chosen after `a < b` equals the one after `b < a`. | — |
| `target_agree_off` | 992-1005 | **§6.2 spine — inductive step.** For a partition-invariant selector and matrices agreeing off a singletoned decision set `D`, the target cell is the same even when the start colourings only agree up to partition. | — |
| `Egnd` | 1034-1035 | **§13.** The canonical ground set on `Fin n`: ordered pairs `(i, j)` with `i < j`. | Definition |
| `mem_Egnd` | 1037-1038 | Membership in `Egnd n` is exactly `p.1 < p.2`. | — |
| `Egnd_ne` | 1040-1041 | Pairs in `Egnd n` have distinct endpoints: `p.1 ≠ p.2`. | — |
| `Pof` | 1043-1056 | **§13.** Commit a set `S ⊆ Egnd n` of pair-guesses into a P-matrix: write `less` at `(u,v) ∈ S`, `greater` at `(v,u)`, leaving other entries unchanged. | Definition, `noncomputable` |
| `cl` | 1058-1063 | **§13.** Propagation closure on pair-guesses: the canonical pairs whose endpoints get separated by warm refinement after committing `S`. | Definition |
| `SingletonAt` | 1073-1075 | The fresh-colour hypothesis at a pair `p`: both `p.1` and `p.2` are `χι`-singletons. | Definition |
| `cl_extensive` | 1077-1092 | **§13 M1 — extensiveness of `cl`.** For canonical `S` whose vertices are all `χι`-singletons, every pair in `S` lies in `cl S`. | — |
| `Pof_mono_entry_of_unknown` | 1122-1146 | Entry-wise monotonicity of `Pof` from the all-unknown base: for canonical `S ⊆ T`, each entry of `Pof _ S` is either `unknown` or equal to the corresponding `Pof _ T` entry (does not lift to a `cl` monotonicity result). | — |
| `FullyDiscrete` | 1158-1160 | A colouring is fully discrete when every vertex is its own `χι`-singleton. | Definition |
| `cl_monotone_discrete` | 1162-1179 | **§13 M0, vacuous case.** Under `FullyDiscrete`, every canonical pair lies in every `cl S`, so `cl S = Egnd n` and monotonicity carries no structural information. | — |
| `TVerticesSingletons` | 1192-1194 | Every endpoint of every pair in `T` is a `χι`-singleton. | Definition |
| `warmRefine_samePartition_T_individualised` | 1196-1281 | **§13 M0, strong form.** Warm refinement under `Pof P₀ S` and `Pof P₀ T` induces the *same* partition when `S ⊆ T` and every endpoint of every `T`-pair is a `χι`-singleton. | — |
| `cl_monotone_T_individualised` | 1283-1294 | **§13 M0 — monotonicity of `cl`** under the T-individualised hypothesis: `S ⊆ T` implies `cl S ⊆ cl T`. | — |
| `cl_idempotent` | 1320-1334 | **§13 M2 — idempotence of `cl`** under fresh-colour individualisation of `S ∪ cl S`: `cl (cl S) = cl S`. | — |
| `Pof_fs` | 1406-1412 | **§14.** Finset-based computable analogue of `Pof`, enabling `decide`-checkable refutations. | Definition |
| `commitsToP` | 1414-1416 | **§14.** All-unknown-base commits-to-matrix shortcut: `Pof_fs (fun _ _ => .unknown) S`. | Definition |
| `cl_prov` | 1418-1423 | **§14.** Provenance closure (TC-based): the canonical pair-guesses whose direction is decided by `transitiveClose` of `commitsToP S`. | Definition |
| `closeStep_unknown` | 1427-1431 | `closeStep` returns `.unknown` at every entry of the all-unknown matrix. | — |
| `closeStep_unknown_fixpoint` | 1433-1436 | The all-unknown matrix is a fixpoint of `closeStep`. | — |
| `transitiveClose_unknown` | 1438-1450 | `transitiveClose` of the all-unknown matrix is the all-unknown matrix. | — |
| `cl_prov_empty` | 1454-1463 | **§14 CL0 for `cl_prov`:** `cl_prov ∅ = ∅`. | — |
| `cl_prov_extensive` | 1465-1479 | **§14 CL1 for `cl_prov`:** for canonical `S`, every commit's direct `less` write survives transitive closure, so `S ⊆ cl_prov S`. | — |
| `cl_prov_M3_false` | 1497-1507 | **§14 — refutes matroid M3 exchange for `cl_prov`.** A concrete `n=5, S={(1,2),(3,4)}, x=(2,3), y=(1,4)` counterexample where the M3 premise holds but the conclusion fails; machine-checked by `decide`. | — |
| `hasLessChain` | 1521-1524 | Existence of a `.less`-chain in `P` from `i` to `j` via some intermediate `k` with both edges `.less`. | Definition |
| `hasGreaterChain` | 1526-1528 | Existence of a `.greater`-chain in `P` from `i` to `j` via some intermediate `k`. | Definition |
| `CanConsistent` | 1530-1534 | A `PMatrix` is canonical-consistent when every `.less` entry sits at `i.val < j.val` and every `.greater` entry at `i.val > j.val`. | Definition |
| `LessMono` | 1536-1539 | One-sided `.less`-direction entry-wise monotonicity between two matrices: `P i j = .less → Q i j = .less`. | Definition |
| `canConsistent_no_conflict` | 1541-1551 | Under canonical-consistency, no pair simultaneously hosts both a `.less`-chain and a `.greater`-chain. | — |
| `commitsToP_classify` | 1553-1570 | Three-way classification of `commitsToP S i j` by `S`-membership of `(i,j)` and `(j,i)`. | — |
| `commitsToP_canConsistent` | 1572-1586 | `commitsToP` of a canonical `S` is canonical-consistent. | — |
| `closeStep_keeps_greater` | 1590-1593 | `closeStep` never demotes a decided `.greater` entry. | — |
| `iterate_closeStep_keeps_greater` | 1595-1605 | Iterating `closeStep` preserves any `.greater` entry — once decided, frozen. | — |
| `closeStep_decided` | 1607-1613 | `closeStep` preserves any decided entry (`.less` or `.greater`). | — |
| `closeStep_eq_less_iff` | 1629-1663 | `closeStep P i j = .less` iff `P i j` was already `.less`, or it was `.unknown` with a `.less`-chain through some intermediate vertex. | — |
| `closeStep_eq_greater_iff` | 1665-1717 | `closeStep P i j = .greater` iff `P i j` was already `.greater`, or it was `.unknown` with no `.less`-chain but a `.greater`-chain. | — |
| `closeStep_canConsistent` | 1719-1730 | `closeStep` preserves canonical-consistency. | — |
| `iterate_closeStep_canConsistent` | 1732-1740 | Iterating `closeStep` preserves canonical-consistency. | — |
| `transitiveClose_canConsistent` | 1742-1745 | `transitiveClose` preserves canonical-consistency. | — |
| `closeStep_lessMono` | 1747-1773 | Joint inductive step: under canonical-consistency of `Q` and `LessMono P Q`, `closeStep` preserves `.less`-mono. | — |
| `iterate_closeStep_lessMono` | 1775-1784 | Iterating `closeStep` preserves `.less`-mono under joint canonical-consistency. | — |
| `transitiveClose_lessMono` | 1786-1790 | `transitiveClose` preserves `.less`-mono under joint canonical-consistency. | — |
| `commitsToP_lessMono` | 1792-1805 | Base case for CL3: canonical `S ⊆ T` gives `LessMono (commitsToP S) (commitsToP T)`. | — |
| `cl_prov_monotone` | 1809-1834 | **§14 CL3 — monotonicity for `cl_prov`:** canonical `S ⊆ T` implies `cl_prov S ⊆ cl_prov T`. | — |
| `numUnknown` | 1843-1846 | Number of `.unknown` entries in a `PMatrix` — the strictly-decreasing potential bounding TC iteration. | Definition |
| `numUnknown_le` | 1848-1853 | `numUnknown P ≤ n * n`. | — |
| `closeStep_numUnknown_lt` | 1866-1891 | If `closeStep P ≠ P`, then `numUnknown` strictly drops under one closure round. | — |
| `iterate_closeStep_progress` | 1893-1920 | After `k` `closeStep` iterations, either a fixpoint has been reached at some step `≤ k`, or `numUnknown` has dropped by at least `k`. | — |
| `transitiveClose_is_fixpoint` | 1922-1972 | After `n*n` iterations of `closeStep`, the result is a fixpoint: `closeStep (transitiveClose P) = transitiveClose P`. | — |
| `transitiveClose_idempotent` | 1974-1980 | **TC idempotence.** `transitiveClose (transitiveClose M) = transitiveClose M`. | — |
| `cl_prov_idempotent` | 2011-2041 | **CL2 — idempotence.** `cl_prov (cl_prov S) = cl_prov S` for canonical `S`. | — |
| `IndivStep` | 2128-2152 | Existential witness of one descent-step individualisation: a colouring `χ'` that singletons every vertex in target `T` and refines `χ` outside `T`. Data, not a function — the trace carries one per step. | Structure |
| `singletons_union` | 2156-2177 | **D-singletons preserved.** If `χ` singletons every `v ∈ D`, an `IndivStep` with target `T` singletons every `v ∈ D ∪ T`. | — |
| `samePartition_of_samePartition` | 2179-2209 | Two `IndivStep`s applied to `samePartition`-equal colourings with the same target `T` produce `samePartition`-equal results — the inductive engine of the spine theorem. | — |
| `IndivStep.default` | 2211-2262 | **Concrete `IndivStep` witness.** A constructive individualisation step (parity-tagged base-`n` encoding), proving traces exist at every level so the spine theorem is non-vacuous. | Definition |
| `DescentTrace` | 2271-2309 | Inductive predicate: `(D, P, χι)` is reachable by `k` descent steps from `(P₀, χι₀)` under selector `sel`, each step carrying an `IndivStep` witness and a matrix agreeing with `P₀` off the enlarged decision set. | Inductive |
| `singletons` | 2313-2330 | **Trace invariant.** A trace's colouring singletons its whole decision set `D`. | — |
| `P_agrees` | 2332-2342 | **Trace invariant.** A trace's matrix agrees with `P₀` on every entry with an endpoint outside `D`. | — |
| `SpineChain` | 2346-2354 | Bundle of a `DescentTrace` with its derived state `(D, P, χι)`. The spine theorem is branch-independence of two such chains. | Structure |
| `partition` | 2361-2365 | The chain's level-`k` partition: warm refinement of its accumulated `(P, χι)`. | Definition |
| `IndivStep.samePartition_het` | 2371-2384 | Heterogeneous `samePartition_of_samePartition`: accepts separate targets `T₁, T₂` with an equality hypothesis. Used at the spine induction's level-`k+1` step. | — |
| `spine_branch_independent` | 2386-2460 | **The spine theorem (branch independence).** Any two `DescentTrace`s through `k` levels agree on the accumulated `D` (literal) and the level-`k` partition (`samePartition`) — handing the oracle one fixed partition instead of `2^d` refinement worlds. | — |
| `SpineChain.branch_independent` | 2462-2471 | **The spine theorem, `SpineChain` wrapper.** Two chains at level `k` share `D` and level-`k` partition. | — |
| `defaultColouring` | 2492-2502 | The level-`k` colouring of the default reference chain: iterate refine-then-individualise (via `IndivStep.default`) from `χι₀`, with the matrix held fixed at `P₀`. | Definition |
| `defaultD` | 2504-2513 | The level-`k` decision set of the default chain: accumulate `sel (warmRefine adj P₀ (defaultColouring k))` across all levels. | Definition |
| `defaultTrace` | 2515-2528 | The concrete `DescentTrace` realising the default construction, using `IndivStep.default` at every level and `P = P₀` throughout. | Definition |
| `defaultSpineChain` | 2530-2538 | The concrete reference `SpineChain` at every level, bundling `defaultD`/`P₀`/`defaultColouring`/`defaultTrace`. | Definition |
| `SpineChain.eq_default` | 2540-2551 | **Reference corollary.** Every `SpineChain` at level `k` shares `D` and level-`k` partition with `defaultSpineChain` — there is a canonical level-`k` partition, computable by one deterministic descent. | — |
| `Discrete` | 2575-2578 | A colouring is discrete when every cell is a singleton — equivalently, `χ : Fin n → Nat` is injective. | Definition |
| `of_samePartition` | 2582-2586 | Discreteness is `samePartition`-invariant: equal partitions transport `Discrete`. | — |
| `warmRefine_preserves` | 2588-2597 | Warm refinement preserves discreteness: if `χ` is injective, so is `warmRefine adj P χ`. | — |
| `SpineChain.IsLeaf` | 2601-2607 | A `SpineChain` reaches a leaf when its level-`k` partition is discrete (every vertex a singleton). | Definition |
| `SpineChain.isLeaf_iff_default` | 2609-2618 | `IsLeaf` is spine-invariant: a chain is a leaf iff `defaultSpineChain` at the same level is. | — |
| `TargetsNonsingletonCell` | 2622-2628 | Selector hypothesis: every returned vertex has a same-colour partner (`sel` only picks from non-singleton cells). | Definition |
| `NonemptyOnNonDiscrete` | 2630-2635 | Selector hypothesis: `sel χ` is non-empty whenever `χ` is not yet discrete. | Definition |
| `defaultD_univ_isLeaf` | 2637-2652 | **`D` covers all vertices ⇒ leaf.** When the accumulated decision set is the full vertex set, the default chain's spine partition is discrete. | — |
| `defaultD_grows_if_not_leaf` | 2654-2693 | **`D` strictly grows on every non-leaf step.** Under the two selector hypotheses, a non-leaf level-`k` chain has `|defaultD k| < |defaultD (k+1)|`. | — |
| `defaultSpineChain_reaches_leaf` | 2695-2734 | **Leaf existence.** Under `TargetsNonsingletonCell` and `NonemptyOnNonDiscrete`, the default descent reaches a leaf within `n` levels. | — |
| `DirAssignment` | 2757-2763 | Order assignment relative to `(P₀, D)`: an antisymmetric matrix agreeing with `P₀` on every entry with an endpoint outside `D`. The linear oracle's input shape — a point in the order-label residual. | Structure |
| `default` | 2769-2776 | **Trivial `DirAssignment`.** When `P₀` is antisymmetric, `P₀` itself is a valid order assignment for any `D` (witnesses non-emptiness). | Definition |
| `samePartition_pair` | 2778-2790 | Any two `DirAssignment`s over the same `(P₀, D)`, refined against a `D`-singletoning colouring, induce the same partition. | — |
| `samePartition_chain` | 2792-2805 | **Spine equivalence.** A `DirAssignment` over a chain's `D`, refined against the chain's colouring, induces the chain's partition — the residual is exactly the choice of `DirAssignment`, partition fixed. | — |
| `flipPair` | 2809-2853 | **Single-pair direction flip.** Negate the `(a, b)` and `(b, a)` entries of a `DirAssignment` via `POE.neg`. The generator of the `Z₂` group action on direction choices. | Definition |
| `eq_of_σ_eq` | 2855-2865 | `DirAssignment` equality is determined by the matrix field — propositional fields subsumed by proof irrelevance. | — |
| `flipPair_idempotent` | 2867-2876 | **Flip is an involution.** Two applications of `flipPair` to the same pair return the original `DirAssignment` — the `Z₂` generator squares to identity. | — |
| `flipPair_partition_invariant` | 2878-2888 | **Flipping preserves the partition.** `σ` and `σ.flipPair a b` share the spine partition — the order labels move, the partition doesn't. | — |
| `flipPair_comm` | 2890-2914 | **Flips on disjoint pairs commute** — the abelian-ness of the `Z₂^d` action: distinct decisions don't interfere. | — |
| `IsAut` | 2942-2945 | A `Fin n`-permutation `π` is a graph automorphism of `adj` when it preserves adjacency edge-by-edge: `adj.adj (π v) (π w) = adj.adj v w`. | Definition |
| `IsAut.refl` | 2951-2952 | The identity permutation is an automorphism. | — |
| `IsAut.trans` | 2954-2959 | Composition of automorphisms is an automorphism. | — |
| `IsAut.symm` | 2961-2967 | The inverse of an automorphism is an automorphism. | — |
| `labelledAdj` | 2971-2977 | **Labelled adjacency.** Adjacency matrix relabelled by `π`: entry `(i, j)` is the original adjacency between `π⁻¹ i` and `π⁻¹ j`. | Definition |
| `labelledAdj_eq_of_isAut` | 2979-2992 | **Automorphisms fix the labelled adjacency.** `IsAut π adj` implies `labelledAdj π adj = adj.adj` — an automorphism is invisible at the labelled level. | — |
| `isAut_of_labelledAdj_eq` | 2994-3004 | **Converse.** A permutation preserving the labelled adjacency is an automorphism. | — |
| `vertexRankNat` | 3017-3019 | Strict rank of vertex `v`: the count of vertices `u` with `χ u < χ v`. | Definition |
| `vertexRank` | 3037-3039 | Vertex rank packaged as `Fin n` via `vertexRankNat_lt_n`. | Definition |
| `vertexRank_strict_mono` | 3041-3060 | `vertexRank` is strictly monotonic in the colour value: `χ v < χ w` implies `vertexRank χ v < vertexRank χ w`. | — |
| `vertexRank_injective` | 3062-3072 | On a `Discrete` colouring, `vertexRank` is injective. | — |
| `vertexRank_bijective` | 3074-3077 | On a `Discrete` colouring, `vertexRank` is bijective. | — |
| `rankPerm` | 3079-3083 | **The rank permutation.** Bijection `Fin n ≃ Fin n` mapping each vertex to its colour-rank on a `Discrete` colouring. | Definition, `noncomputable` |
| `rankPerm_apply` | 3085-3086 | Unfolding lemma: `rankPerm χ h v = vertexRank χ v`. | `@[simp]` |
| `vertexRank_comp` | 3090-3109 | `vertexRank (χ ∘ g) v = vertexRank χ (g v)` — a pure `Finset.card` reindex along `g`. *(Relocated from `LinearOracle.lean` for the cascade oracle's `colourMatchPerm` (M-B).)* | — |
| `rankPerm_comp` | 3111-3131 | **Rank reindexing.** `rankPerm (χ ∘ e) = rankPerm χ · e` — relabelling conjugate-shifts the rank permutation (the §L.5 conjugation gap). *(Relocated from `LinearOracle.lean`.)* | — |
| `SpineChain.canonAdj` | 3147-3173 | **Leaf canonical adjacency.** Given a leaf `SpineChain` and a `DirAssignment σ` over its `D`, relabel `adj` by the rank permutation of the warm-refined partition. | Definition, `noncomputable` |
| `matrixLT` | 3177-3184 | **Row-major lex strict less-than on `n × n` matrices.** The first disagreeing cell `(i, j)` (row-then-column order) has `M₁ i j < M₂ i j`. | Definition |
| `matrixLT_irrefl` | 3186-3189 | `matrixLT` is irreflexive: no matrix is `<` itself. | — |
| `matrixLT_asymm` | 3191-3212 | `matrixLT` is asymmetric: `M₁ < M₂` implies `¬ M₂ < M₁` (strict-order fact). | — |
| `PMatrix.fintype` | 3216-3221 | `Fintype` instance for `PMatrix n`, stated explicitly since `PMatrix` is a `def` and so does not inherit the `Pi` instance transparently. | Instance |
| `DirAssignment.fintype` | 3227-3237 | **`Fintype` on `DirAssignment P₀ D`.** Obtained by injecting the σ-field into the `Fintype` `PMatrix n`. | Instance, `noncomputable` |
| `relabelMatrix` | 3241-3248 | **Relabel a bare matrix** `Fin n → Fin n → Nat` by a permutation `π`: entry `(i,j)` becomes `M (π⁻¹ i) (π⁻¹ j)`. Lets `LeafTwistSpec` state the leaf-relabelling property without re-wrapping as an `AdjMatrix`. | Definition |
| `MatrixLex` | 3250-3255 | `Fin n → Fin n → Nat` viewed under the row-major lex order via nested `Pi.Lex`. | `abbrev` |
| `toMatrixLex` | 3257-3260 | Wrap a matrix into its Lex'd form (identity at runtime — `Lex` is a type synonym). | Definition |
| `ofMatrixLex` | 3262-3264 | Unwrap a Lex'd matrix back to a plain `Fin n → Fin n → Nat`. | Definition |
| `ofMatrixLex_toMatrixLex` | 3266-3267 | `ofMatrixLex (toMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_ofMatrixLex` | 3269-3270 | `toMatrixLex (ofMatrixLex M) = M`. | `@[simp]` |
| `toMatrixLex_injective` | 3272-3276 | `toMatrixLex` is injective. | — |
| `canonFormImages` | 3278-3287 | The Finset of Lex-wrapped `canonAdj` images over all `DirAssignment`s for a leaf chain — the candidate set `canonForm` minimises over. | Definition, `noncomputable` |
| `canonFormImages_nonempty` | 3289-3295 | `canonFormImages chain isLeaf` is non-empty when `DirAssignment P₀ chain.D` is. | — |
| `canonForm` | 3297-3317 | **The canonical leaf adjacency matrix:** the lex-min `canonAdj` over all `DirAssignment`s (row-major lex). Requires `Nonempty (DirAssignment P₀ chain.D)`. | Definition, `noncomputable` |
| `canonForm_mem_image` | 3319-3334 | **`canonForm` comes from some `DirAssignment`:** it equals `canonAdj σ` for some `σ`. | — |
| `canonForm_le_canonAdj` | 3336-3352 | **`canonForm` is the lex-minimum:** `toMatrixLex (canonForm) ≤ toMatrixLex (canonAdj σ)` for every `DirAssignment σ`. | — |
| `LinearOracleSpec` | 3356-3372 | **The linear-oracle interface type:** given a leaf chain and a current-branch `DirAssignment`, return either `none` or a verified automorphism of `adj` (bundled as a subtype). | Definition |
| `some_isAut` | 3379-3391 | **Soundness (subtype-level):** when the oracle returns `some result`, the returned permutation is automatically an automorphism. | — |
| `LeafTwistSpec` | 3393-3410 | **Leaf-twist validity spec:** when the oracle returns `some result`, the returned `π` relabels the input branch's canonical adjacency to that of some other `DirAssignment σ'` — the property justifying pruning. | Definition |
| `individualizedColouring` | 3448-3452 | **Fresh-colour individualisation** of a vertex set `S`: each `v ∈ S` gets unique colour `v.val + 1`; vertices outside `S` share colour `0`. | Definition |
| `FixesPointwise` | 3454-3457 | Predicate: permutation `π` fixes every vertex in `S` pointwise (`π v = v` for `v ∈ S`). | Definition |
| `complement` | 3463-3471 | A pointwise-fixing permutation stabilises the complement setwise: `v ∉ S` implies `π v ∉ S`. | — |
| `individualizedColouring_invariant` | 3475-3484 | An automorphism fixing `S` pointwise preserves the individualised colouring: `χ_S (π v) = χ_S v` for every `v`. | — |
| `signature_invariant_of_isAut` | 3488-3525 | An automorphism preserving `(adj, P, χ)` pointwise preserves the signature multiset at every vertex. | — |
| `refineStep_invariant_of_isAut` | 3527-3540 | An automorphism preserving `(adj, P, χ)` pointwise preserves one round of `refineStep`. | — |
| `iterate_refineStep_invariant_of_isAut` | 3542-3558 | Iterated refinement preserves automorphism invariance for any number of rounds. | — |
| `warmRefine_invariant_of_isAut` | 3560-3569 | Warm refinement preserves automorphism invariance: if `(adj, P, χ_init)` are all `π`-invariant, so is `warmRefine adj P χ_init`. | — |
| `signature_transport` | 3583-3608 | **Signature transport.** An automorphism `g` carrying `(P₁, χ₁)` to `(P₂, χ₂)` maps the `(P₂, χ₂)`-signature at `g v` to the `(P₁, χ₁)`-signature at `v`. Cross-config form of `signature_invariant_of_isAut`. | — |
| `sigKey_transport` | 3610-3617 | **`sigKey` transport** — cross-config: `sigKey adj P₂ χ₂ (g v) = sigKey adj P₁ χ₁ v`. | — |
| `refineStep_transport` | 3619-3627 | **`refineStep` transport** — one round, cross-config: `refineStep adj P₂ χ₂ (g v) = refineStep adj P₁ χ₁ v`. | — |
| `iterate_refineStep_transport` | 3629-3643 | **Iterated `refineStep` transport** across any number of rounds, cross-config. | — |
| `warmRefine_transport` | 3645-3654 | **Warm-refinement transport.** An automorphism carrying `(P₁, χ₁)` to `(P₂, χ₂)` carries the warm refinement of the first onto the second. | — |
| `OrbitPartition` | 3670-3676 | **Aut_S orbit relation** on vertices: `v ~ w` iff some automorphism of `adj` preserving `P` and fixing `S` pointwise sends `v` to `w`. | Definition |
| `refl` | 3682-3685 | Reflexivity of `OrbitPartition` (via the identity permutation). | — |
| `symm` | 3687-3702 | Symmetry of `OrbitPartition` (via permutation inverse). | — |
| `trans` | 3704-3719 | Transitivity of `OrbitPartition` (via permutation composition). | — |
| `subset_warmRefine` | 3721-3736 | **Trivial direction of the squeeze:** orbits refine 1-WL cells — `OrbitPartition v w` implies `warmRefine` colours of `v` and `w` agree. | — |
| `refineStep_iter_le_eq` | 3749-3767 | Refinement is split-only across iterations: equality at iterate `k + d` implies equality at iterate `k`. | — |
| `warmRefine_eq_iter_eq` | 3769-3783 | `warmRefine` equality implies iterate-`r` equality for any `r ≤ n`; the bridge from the fixpoint partition to any earlier-round partition. | — |
| `id_of_discrete_invariant` | 3808-3817 | **Fact B (pointwise):** a `π`-invariant discrete colouring forces `π` to be the identity. | — |
| `aut_trivial_of_discrete_warmRefine` | 3819-3835 | **Fact B (CFI):** if `warmRefine adj P χ_S` is discrete, every automorphism preserving `(adj, P)` and fixing `S` pointwise is the identity. | — |
| `orbit_iff_eq_of_discrete_warmRefine` | 3837-3855 | **Fact B (partition):** at discrete depth, `OrbitPartition adj P S v w ↔ v = w`. | — |
| `CascadesAt` | 3877-3884 | **Cascade-at-depth-`k` predicate:** some `S` with `S.card ≤ k` makes `warmRefine adj P (individualizedColouring n S)` discrete. | Definition |
| `cascadesAt_univ` | 3886-3905 | **Trivial cascade at depth `n`:** taking `S = univ` gives a discrete starting colouring preserved by warm refinement — the every-graph fallback. | — |
| `CascadesAt.mono` | 3907-3912 | Monotonicity: a cascade at depth `k₁` is a cascade at every depth `k₂ ≥ k₁`. | — |
| `theorem_1_HOR_at_depth` | 3925-3948 | **Key theorem (Tier 1 HOR).** If `adj` cascades at depth `k`, some `S` with `S.card ≤ k` makes `warmRefine` discrete and the `Aut_S`-orbit partition equal to the `warmRefine` partition. | — |
| `theorem_1_HOR_at_n` | 3970-3981 | **Theorem 1, trivial-bound corollary:** every graph admits orbit recovery at depth `n`. Axiom-free specialisation to `cascadesAt_univ`. | — |
| `theorem_1_HOR` | 3983-3994 | **Theorem 1 (legacy existential form):** some `S` makes `warmRefine` discrete and orbits equal cells. | — |
| `theorem_1_HOR_pointwise` | 3996-4008 | **Theorem 1, pointwise corollary:** at the cascade depth, every automorphism preserving `(adj, P)` and fixing `S` is the identity. | — |
| `SchemeProfile` | 4061-4077 | **Key structure (Tier 2).** Bundles a v-profile colouring with its structural facts: profile classes equal `Aut_v` orbits (schurian Step 1) and 1-WL refines the profile partition (intersection-number Step 2). | Structure |
| `warm_iff_profile` | 4083-4096 | **Squeeze for `SchemeProfile`:** the 1-WL fixpoint partition equals the profile partition. | — |
| `theorem_2_HOR_of_profile` | 4112-4128 | **Theorem 2 (assembly form):** given a `SchemeProfile` witness at `v`, the 1-WL fixpoint partition at depth 1 equals the `Aut_v`-orbit partition. The axiom-free assembly lemma `Scheme.lean`'s `theorem_2_HOR_concrete` consumes (the placeholder axioms `IsSchurianSchemeGraph` / `schurian_scheme_profile_exists` and the conditional `theorem_2_HOR` were retired 2026-06-05). | — |

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
| `cfi_depth_bound` | 550-564 | §10 **Cascade-depth function for CFI graphs**, concretely `h.baseSize` (discharges the former axiom in Stage-4 M1). | Definition |
| `cfi_depth_bound_le` | 566-581 | **The CFI depth bound is `≤ baseSize`**, trivial after the M1 concretization. | — |
| `card_CFIVertex` | 695-702 | §11 **The cardinality identity**: `Fintype.card H.CFIVertex = H.cfiVertexCount` — the abstract vertex type matches the gadget-size sum formula. | — |
| `IsCFI'.six_baseSize_le` | 720-754 | §12 **Connector**: a CFI graph has at least `6 * baseSize` vertices (each gadget contributes ≥ 6) — yields the `n/6` depth bound. | — |
| `aEmpty` | 773-778 | §13.1 The canonical seed vertex `a_∅^v` of `CFI(H)`: the subset vertex at gadget `v` with the empty subset, individualized by the M2-M4 cascade. | Definition |
| `endpoint` | 780-783 | §13.1 The endpoint vertex `e^b_{v→w}` of `CFI(H)` at gadget `v`, pointing toward `w ∈ N(v)` with parity bit `b`. | Definition |
| `cfiAdj_aEmpty_endpoint_false` | 792-797 | §13.2 `cfiAdj (a_∅^v) (e^0_{v→w}) = 0` — the b=false endpoint is not adjacent to the empty-subset seed. | — |
| `cfiAdj_aEmpty_endpoint_true` | 799-804 | §13.2 `cfiAdj (a_∅^v) (e^1_{v→w}) = 1` — the b=true endpoint is adjacent to the empty-subset seed. | — |
| `aEmpty_ne_endpoint` | 806-813 | `H.aEmpty v ≠ H.endpoint hw b`: subset and endpoint vertices are distinct (different `Sum` tags). | — |
| `cfiAdj_aEmpty_endpoint_diff_gadget` | 815-828 | **Cross-gadget non-adjacency**: `cfiAdj (a_∅^v) (e^b_{v'→w}) = 0` when `v ≠ v'`. | — |
| `cfiAdj_bridge` | 830-846 | **The bridge edge**: `cfiAdj (e^b_{v→w}) (e^b_{w→v}) = 1` — same-parity endpoints at neighbouring gadgets pointing toward each other. | — |
| `IsCFI'.seedVertex` | 859-863 | §13.3 The `Fin n` vertex corresponding to the seed `a_∅^v` for an `IsCFI'` witness — what the cascade individualizes. | Definition |
| `IsCFI'.endpointVertex` | 865-869 | §13.3 The `Fin n` vertex corresponding to `e^b_{v→w}` for an `IsCFI'` witness — the endpoints the cascade probes. | Definition |
| `e_seedVertex` | 875-879 | Bijection round-trip: `h.e (h.seedVertex v) = h.H.aEmpty v`. | `@[simp]` |
| `e_endpointVertex` | 881-886 | Bijection round-trip: `h.e (h.endpointVertex hw b) = h.H.endpoint hw b`. | `@[simp]` |
| `seedVertex_ne_endpointVertex` | 888-898 | Seed and endpoint vertices are distinct in `Fin n` (their abstract counterparts have different `Sum` tags). | — |
| `adj_seed_endpoint_false` | 913-919 | §13.4 Fin-n: `adj (seedVertex v) (endpointVertex v w false) = 0`. | — |
| `adj_seed_endpoint_true` | 921-927 | §13.4 Fin-n: `adj (seedVertex v) (endpointVertex v w true) = 1`. | — |
| `adj_endpoint_seed_false` | 929-935 | §13.4 Symmetric Fin-n form: `adj (endpointVertex v w false) (seedVertex v) = 0`. | — |
| `adj_endpoint_seed_true` | 937-943 | §13.4 Symmetric Fin-n form: `adj (endpointVertex v w true) (seedVertex v) = 1`. | — |
| `individualizedColouring_singleton_self` | 1009-1012 | Individualizing a single seed gives it colour `seed.val + 1`. | `@[simp]` |
| `individualizedColouring_singleton_other` | 1014-1018 | Under a singleton individualization, every non-seed vertex gets colour `0`. | `@[simp]` |
| `individualizedColouring_eq_iff_of_mem` | 1145-1161 | Multi-seed uniqueness: under `individualizedColouring n S`, for `v ∈ S` a vertex shares v's colour iff it equals v. Generalises the singleton form to arbitrary S. | — |
| `allSeeds` | 1167-1174 | §13.8 The cascade individualization set `{seedVertex v : v ∈ Fin m}` — one seed per base vertex; the witness used in `cfi_cascades_polynomially`. | Definition |
| `seedVertex_injective` | 1176-1194 | `seedVertex` is injective: distinct base vertices map to distinct `Fin n` indices. | — |
| `seedVertex_mem_allSeeds` | 1196-1199 | Every `seedVertex v` lies in `allSeeds`. | — |
| `allSeeds_card` | 1201-1207 | `|allSeeds| = h.baseSize`; with `six_baseSize_le` the cascade individualization has at most n/6 vertices. | `@[simp]` |
| `adj_endpointVertex_eq_one_iff` | 1506-1528 | §13.12 Endpoint-endpoint adjacency characterisation: two endpoints are adjacent iff they form a bridge pair (`v_a = w_b ∧ w_a = v_b ∧ b_a = b_b`). | — |
| `adj_seedVertex_eq_one_iff` | 1530-1605 | §13.12 Seed-adjacency characterisation: a vertex is adjacent to `seedVertex w` iff it is a b=true endpoint in gadget w. Key structural fact for the cascade's no-match preconditions. | — |
| `subset` | 1727-1732 | §13.14 The CFI vertex `a_S^v`: the subset vertex at gadget v with even subset S ⊆ N(v). Generalises `aEmpty v` (the S = ∅ case). | Definition |
| `IsCFI'.subsetVertex` | 1785-1791 | §13.14 The `Fin n` vertex for `a_S^v`. Generalises `seedVertex v` (the empty-subset case). | Definition |
| `e_subsetVertex` | 1797-1803 | Bijection round-trip: `h.e (subsetVertex hS) = subset hS`. | `@[simp]` |
| `adj_subsetVertex_eq_one_iff` | 1851-1904 | §13.14 Subset-adjacency characterisation: `adj u (subsetVertex_{v'} hS') = 1` iff u is an endpoint at v' whose parity satisfies `(w' ∈ S') ⊕ b`. Generalises `adj_seedVertex_eq_one_iff` (S' = ∅). | — |
| `IsCFI'.adj_symm` | 2103-2107 | §13.16.5 CFI adjacency is symmetric at the `Fin n` level: `adj.adj i j = adj.adj j i`. | — |
| `OddDegree` | 2633-2636 | §13.21 Odd-degree CFI base: every base vertex has odd degree, ensuring no even subset of N(v) is saturated. Hypothesis for the axiom-free cascade (covers K₄, K₃,₃, Petersen). | Definition |
| `exists_witness_of_oddDegree` | 2638-2659 | §13.21 Under `OddDegree`, every even subset of N(v) has a strict non-element y ∈ N(v) \ S — the subset-distinction witness. | — |
| `cfi_cascades_polynomially_oddDeg` | 2971-3175 | §13.24 M4 — for OddDegree CFI graphs, `warmRefine adj P χ_{allSeeds}` is `Discrete`; discharges `CascadesAt` (the cascade axiom) axiom-free at depth `cfi_depth_bound h`. | — |
| `theorem_1_HOR_cfi_oddDeg` | 3177-3196 | **Tier-1 CFI orbit recovery.** Theorem 1 for OddDegree CFI graphs, axiom-free: orbit partition coincides with the warm-refined colouring at depth ≤ baseSize, conditional only on `OddDegree`. | — |

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

| `CFIBase.flipSet_subset` | 3257-3260 | The flip set is a set of neighbours: `flipSet F v ⊆ N(v)`. | — |
| `CFIBase.mem_flipSet` | 3262-3265 | Membership in the flip set: `w ∈ flipSet F v ↔ w ∈ N(v) ∧ F v w`. | `@[simp]` |
| `CFIBase.xorF` | 3293-3295 | **(CFI-cov.2)** Pointwise XOR of two flip-edge indicators — the cycle-space `Z₂` sum. | Definition |
| `CFIBase.flipSet_xorF` | 3297-3305 | **(CFI-cov.2)** The flip-set of an XOR is the symmetric difference of the flip-sets: `flipSet (xorF F F') v = flipSet F v ∆ flipSet F' v`. The reusable core of the cycle-space sum. | — |
| `CFIBase.even_xorF` | 3307-3314 | **(CFI-cov.2)** Even flip-subgraphs stay even under `xorF` (symmetric-difference preserves even cardinality, via `card_symmDiff_mod_two`). | — |
| `CFIBase.CycleSpace` | 3316-3319 | **(CFI-cov.2) The cycle space `Z₂^β`**: symmetric, even flip-subgraphs `F` — the index set of the gauge flips `cfiFlip F` (the `Z₂^β` factor of `Aut(CFI(H))`). | Definition |
| `CFIBase.cycleSpace_xorF` | 3321-3324 | **(CFI-cov.2)** The cycle space is closed under the `Z₂` sum `xorF` (symmetric + even both preserved). | — |
| `CFIBase.cycleSpace_const_false` | 3326-3330 | **(CFI-cov.2)** The empty flip-subgraph (zero) lies in the cycle space. | — |
| `CFIBase.cfiFlip_endpoint_swap` | 3451-3460 | **C1b.0.** The flip swaps the parity-pair `e^0_{v→w}/e^1_{v→w}` iff `F v w = true` (the swap companion of `cfiFlip_endpoint`). | — |
| `CFIBase.cfiFlip_xorF` | 3478-3493 | **(CFI-cov.3) Gauge flip is a homomorphism on the cycle space:** `cfiFlip (xorF F F') = cfiFlip F ∘ cfiFlip F'` (endpoint: Bool-xor assoc/comm; subset: symmDiff assoc/comm via `flipSet_xorF`). The `Z₂^β`-factor group structure. | — |
| `CFIBase.cfiFlip_const_false` | 3495-3506 | **(CFI-cov.3)** The zero subgraph is the identity flip: `cfiFlip (fun _ _ => false) = id` (cycle-space zero ↦ identity). | — |
| `CFIBase.triEdge_symm` | 3533-3535 | The triangle even-subgraph indicator is symmetric in its edge endpoints: `triEdge v w u p q = triEdge v w u q p`. | — |
| `CFIBase.triEdge_apex` | 3537-3539 | The decision edge lies in its triangle: `triEdge v w u v w = true`. | — |
| `CFIBase.triEdge_cyclic` | 3541-3543 | Cyclic invariance of the triangle even-subgraph: `triEdge v w u = triEdge w u v` (so `{v,w,u}` is unordered). | — |
| `CFIBase.triEdge_iff` | 3545-3549 | Membership characterisation of the triangle even-subgraph indicator `triEdge v w u`. | — |
| `CFIBase.flipSet_triEdge_other` | 3568-3578 | **D-locality.** Off the triangle `{v,w,u}` the triangle's flip set is empty, so the triangle flip fixes every other gadget. | — |
| `CFIBase.evenPermEdge_symm` | 3631-3634 | The permutation-cycle even-subgraph indicator is symmetric: `evenPermEdge σ p q = evenPermEdge σ q p`. | — |
| `CFIBase.evenPermEdge_iff_of_mem` | 3636-3650 | At a moved vertex (`σ p ≠ p`), the cycle's F-neighbours are exactly `{σ p, σ⁻¹ p}` — degree 2, no list arithmetic. | — |
| `CFIBase.flipSet_evenPermEdge_of_fixed` | 3664-3673 | **D-locality (triangle-free bases).** At a `σ`-fixed vertex the permutation-cycle flip set is empty, so the cycle flip avoids every fixed gadget. | — |
| `IsCFI'.cfiFlipAut_swaps_endpointVertex` | 3837-3849 | **C1b.0 (lifted to `Fin n`).** `cfiFlipAut F` swaps `endpointVertex hw false ↔ true` iff `F v w = true` — the foundational decision-pair swap C1b.1 keys on. | — |
| `IsCFI'.cfiFlipAut_xorF` | 3853-3861 | **(CFI-cov.3) The lifted gauge-flip homomorphism:** `cfiFlipAut (xorF F F') = cfiFlipAut F * cfiFlipAut F'` (the `Fin n` form of `cfiFlip_xorF` via `e_cfiFlipAut`). So `F ↦ cfiFlipAut F` is a group homomorphism `(Z₂^β, xorF) → Equiv.Perm (Fin n)`, image the gauge group. | — |
| `IsCFI'.cfiFlipAut_one` | 3863-3869 | **(CFI-cov.3)** The zero gauge flip is the identity: `cfiFlipAut (fun _ _ => false) = 1` — the homomorphism preserves the unit. | — |
## ChainDescent/Scheme.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `AssociationScheme` | 47-91 | A symmetric association scheme on `Fin n`: a partition of `Fin n × Fin n` into `rank + 1` symmetric relations `R_0, …, R_rank` (`R_0` the diagonal) with well-defined intersection numbers `p^k_{ij}`. | Structure |
| `relOfPair` | 107-109 | §1.1 The unique relation index `i : Fin (S.rank + 1)` for which `rel i v w = true`. | Definition, `noncomputable` |
| `rel_relOfPair` | 111-114 | The pair `(v, w)` lies in `R_{relOfPair v w}`. | — |
| `relOfPair_unique` | 116-119 | Uniqueness: any relation containing `(v, w)` is `relOfPair v w`. | — |
| `rel_iff_relOfPair` | 121-124 | Characterisation: `rel i v w = true ↔ i = relOfPair v w`. | — |
| `relOfPair_symm` | 126-131 | `relOfPair v w = relOfPair w v`. | — |
| `relOfPair_self` | 133-137 | `relOfPair v v = 0`: the diagonal sits in `R_0`. | — |
| `relOfPair_eq_zero_iff` | 139-147 | Diagonal characterisation: `relOfPair v w = 0 ↔ v = w`. | — |
| `AssociationScheme.ClosedSubset` | 161-166 | **(EOL scheme leg) Closed relation subset = block system.** `I` contains the diagonal `R_0` and is closed under the complex product (`R_i,R_j ∈ I` and `intersectionNumber i j k ≠ 0` ⟹ `R_k ∈ I`). The association-scheme form of a block system / sub-equivalence; on a schurian scheme graph it is a union of scheme relations, hence refinement-visible. | Definition |
| `AssociationScheme.schemeEquiv` | 168-171 | **(EOL scheme leg) The equivalence induced by a relation subset:** `v ~ w` iff `relOfPair v w ∈ I`. Under `ClosedSubset` it is a genuine equivalence (the block system). | Definition |
| `AssociationScheme.schemeEquiv_refl` | 173-175 | Reflexivity of `schemeEquiv I` (needs `0 ∈ I`, via `relOfPair_self`). | — |
| `AssociationScheme.schemeEquiv_symm` | 177-179 | Symmetry of `schemeEquiv I` (free, via `relOfPair_symm` — relations are symmetric). | — |
| `AssociationScheme.schemeEquiv_trans` | 181-198 | **Transitivity from closure under the complex product.** `w` witnesses `intersectionNumber (relOfPair v w)(relOfPair w x)(relOfPair v x) ≠ 0`, so the `ClosedSubset` closure clause forces `relOfPair v x ∈ I`. Where the scheme's intersection numbers do the work a raw partition could not. | — |
| `AssociationScheme.schemeEquiv_equivalence` | 200-203 | A `ClosedSubset`'s induced relation is an `Equivalence` — the block system as a genuine equivalence relation. | — |
| `AssociationScheme.closedSubset_univ` | 205-207 | The whole relation set is always closed (the trivial "one block" system). | — |
| `AssociationScheme.IsPrimitive` | 209-214 | **(EOL scheme leg) Scheme primitivity:** the only closed subsets are the diagonal `{R_0}` and the whole relation set — no non-trivial block system. The Cameron-free, scheme-theoretic primitivity for the Exhaustive-Obstruction Lemma's leg C on coherent-configuration residuals. | Definition |
| `IsSchemeAut` | 236-241 | §2 Scheme automorphism: a permutation of `Fin n` preserving every relation index of `S`. | Definition |
| `IsSchemeAut.refl` | 247-248 | The identity is a scheme automorphism. | — |
| `IsSchemeAut.trans` | 250-256 | Scheme automorphisms compose. | — |
| `IsSchemeAut.symm` | 258-264 | The inverse of a scheme automorphism is a scheme automorphism. | — |
| `relOfPair_eq` | 266-275 | Scheme automorphisms preserve `relOfPair`: `relOfPair (π v) (π w) = relOfPair v w`. | — |
| `SchurianScheme` | 279-290 | An `AssociationScheme` whose relations are exactly the diagonal orbits of `IsSchemeAut`: any two pairs in a relation are connected by some scheme automorphism. | Structure |
| `trivialScheme` | 302-318 | §3 The trivial scheme on `Fin 1` (rank 0, single relation `R_0`); smoke test confirming `AssociationScheme` is inhabited. | Definition |
| `trivialSchurianScheme` | 320-328 | §3 The trivial `Fin 1` scheme is schurian (only the identity is needed). | Definition |
| `vProfile` | 347-356 | T2.2 The v-profile colouring `w ↦ (relOfPair v w).val`: a vertex invariant relative to a fixed individualized `v`. | Definition, `noncomputable` |
| `vProfile_self` | 362-366 | `vProfile S v v = 0`. | — |
| `vProfile_eq_iff` | 368-371 | `vProfile S v w = vProfile S v u ↔ relOfPair v w = relOfPair v u`. | — |
| `vProfile_eq_zero_iff` | 373-385 | `vProfile S v w = 0 ↔ w = v`: the diagonal-relation form. | — |
| `vProfile_ne_self_of_ne` | 387-394 | `v` is a singleton in `vProfile S v ·`: for `w ≠ v`, `vProfile S v w ≠ vProfile S v v`. Matches the `SchemeProfile.v_singleton` field. | — |
| `SchemeOrbitPartition` | 409-413 | §4.1 The v-stabilized scheme-Aut orbit relation: some scheme automorphism with `π v = v` sends `w` to `u`. | Definition |
| `SchemeOrbitPartition.refl` | 419-421 | Reflexivity of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.symm` | 423-431 | Symmetry of `SchemeOrbitPartition`. | — |
| `SchemeOrbitPartition.trans` | 433-443 | Transitivity of `SchemeOrbitPartition`. | — |
| `AssociationScheme.vProfile_aut_invariant` | 464-474 | §4.2 S1.a — a v-stabilizing scheme automorphism preserves `vProfile`: `vProfile S v (π w) = vProfile S v w`. | — |
| `vProfile_eq_of_schemeOrbit` | 478-486 | Trivial direction: `SchemeOrbitPartition` refines `vProfile`-equality. | — |
| `schemeEquiv_isSchemeAut` | 498-505 | **(EOL scheme leg, bridge) The block system is scheme-automorphism-invariant:** `schemeEquiv I (π v)(π w) ↔ schemeEquiv I v w` for a scheme automorphism `π`. The closed subset's partition is preserved by the symmetry — a genuine system of imprimitivity. From `IsSchemeAut.relOfPair_eq`. | — |
| `schemeEquiv_schemeOrbit` | 507-520 | **(EOL scheme leg, bridge) The block of `v` is a union of v-stabilized scheme-Aut orbits** (block system coarser than the orbit partition): same `v`-orbit ⟹ same `schemeEquiv I` block. With orbit recovery (v-orbits = `warmRefine` cells) this makes the block refinement-visible — scheme-imprimitivity ⟹ cascade. | — |
| `vProfile_eq_imp_schemeOrbit` | 526-539 | S1.b — under the schurian axiom, equal `vProfile` implies a v-fixing scheme automorphism connecting the two vertices. | — |
| `vProfile_iff_schemeOrbit` | 541-550 | Step 1 of Theorem 2 (combined): for a schurian scheme, profile equality at `v` is exactly v-stabilized scheme-Aut orbit equivalence. | — |
| `SchemeGraph` | 569-578 | §5 A graph derived from a scheme by marking a set `J ⊆ Fin (rank + 1)` of relations as edges (`0 ∉ J`, so loopless). | Structure |
| `adj` | 584-587 | The derived adjacency matrix: `(v, w)` is an edge iff `relOfPair v w ∈ J`. | Definition, `noncomputable` |
| `adj_eq_one_iff` | 589-593 | Adjacency characterisation: `adj v w = 1 ↔ relOfPair v w ∈ J`. | — |
| `adj_eq_zero_iff` | 595-599 | Non-adjacency characterisation: `adj v w = 0 ↔ relOfPair v w ∉ J`. | — |
| `adj_self` | 601-604 | Loopless: `adj v v = 0`. | — |
| `adj_symm` | 606-610 | Symmetric: `adj v w = adj w v`. | — |
| `adj_eq_zero_or_one` | 612-617 | Adjacency takes values in `{0, 1}`. | — |
| `SchurianSchemeGraph` | 641-655 | §6 A `SchemeGraph` schurian w.r.t. graph automorphisms: `schurian_transitive` (orbits ⊇ relations) and `isAut_imp_isSchemeAut` (orbits ⊆ relations). | Structure |
| `relOfPair_aut_eq` | 661-666 | Graph automorphisms of a `SchurianSchemeGraph` preserve `relOfPair`. | — |
| `vProfile_aut_invariant` | 668-673 | A v-fixing graph automorphism of a `SchurianSchemeGraph` preserves `vProfile S v ·`. | — |
| `GraphOrbitFixing` | 690-694 | §7 The v-stabilized graph-Aut orbit relation: some `π ∈ Aut(adj)` with `π v = v` and `π w = u`. | Definition |
| `GraphOrbitFixing.refl` | 700-701 | Reflexivity of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.symm` | 703-710 | Symmetry of `GraphOrbitFixing`. | — |
| `GraphOrbitFixing.trans` | 712-719 | Transitivity of `GraphOrbitFixing`. | — |
| `vProfile_eq_imp_graphOrbit` | 727-736 | Step 1 (forward, graph-Aut terms): equal `vProfile` implies graph-orbit equivalence. | — |
| `graphOrbit_imp_vProfile_eq` | 738-746 | Step 1 (reverse, graph-Aut terms): graph-orbit equivalence implies equal `vProfile`. | — |
| `vProfile_iff_graphOrbit` | 748-756 | Step 1 (graph-Aut combined): `vProfile` equality iff v-stabilized graph-Aut orbit equivalence — the form bridging to `OrbitPartition adj P {v}` in T2.M4. | — |
| `SchurianSchemeGraph.schemeEquiv_graphOrbit` | 758-767 | **(EOL scheme leg, bridge) The block of `v` is a union of graph-Aut orbits.** Graph version of `schemeEquiv_schemeOrbit`: a graph automorphism fixing `v` (`GraphOrbitFixing`) preserves the `schemeEquiv I` block, since on a schurian scheme graph every graph aut is a scheme aut (`isAut_imp_isSchemeAut`). Block system coarser than the v-stabilized graph-orbit partition — ready to compose with recovery. | — |
| `refineStep_round1_pair_eq` | 824-872 | §8.a S2.a round-1 lemma: under `χ_v`, equal colour after one `refineStep` for non-`v` `w, u` forces `(adj w v, P w v) = (adj u v, P u v)`. | — |
| `refineStep_round1_adj_eq` | 874-882 | S2.a (adj-only): round-1 equality forces `adj w v = adj u v`. | — |
| `SchemeGraph.refineStep_round1_J_eq` | 884-914 | S2.a for scheme graphs: round-1 equality under `χ_v` forces matching J-class membership of `relOfPair v ·`. | — |
| `iterSignature` | 935-943 | §8.b The signature multiset of `w` computed against the `iter[k]` refinement of `χ_v`. | Definition |
| `iter_succ_eq_iff` | 945-956 | Round-by-round unfolding: `iter[k+1]` equality decomposes into `iter[k]` equality plus matching iter-k signatures. | — |
| `AssociationScheme.intersectionCount_via_w` | 958-984 | Scheme axiom in usable form: the count of `u'` with `(v,u') ∈ R_i` and `(w,u') ∈ R_l` equals `intersectionNumber i l (relOfPair v w)` — depends only on `vProfile w`. | — |
| `AssociationScheme.intersectionCount_eq_of_vProfile_eq` | 986-1000 | Corollary: if `relOfPair v w = relOfPair v u`, the intersection counts at `(v,w)` and `(v,u)` coincide for every `(i, l)`. | — |
| `Step2_target` | 1009-1025 | §8.c Step 2 statement (target): for a `SchurianSchemeGraph` and compatible `P`, `warmRefine` cells refine `vProfile` classes. | Definition |
| `iter_succ_adj_eq` | 1162-1176 | §8.b.3 S2.a lifted to any depth ≥ 1: `iter[k+1]` equality between non-`v` vertices forces matching adj-to-`v`. | — |
| `warmRefine_adj_eq` | 1178-1193 | warmRefine form of S2.a: two non-`v` vertices in the same warmRefine cell share adjacency to `v`. | — |
| `SchurianSchemeGraph.warmRefine_J_eq` | 1195-1219 | Two non-`v` vertices in the same warmRefine cell share J-class membership of `relOfPair v ·` — the coarsest non-trivial Step 2 refinement. | — |
| `toSchemeProfile` | 1247-1280 | **T2.M4 assembly.** The `SchemeProfile` constructor: from a `SchurianSchemeGraph`, a P-invariance hypothesis, and a `Step2_target` witness, build the abstract `SchemeProfile G.adj P v`. | Definition, `noncomputable` |
| `schurian_scheme_profile_exists_of_step2` | 1282-1292 | Packages `toSchemeProfile` as the `Nonempty` existence result matching the `schurian_scheme_profile_exists` axiom. | — |
| `trivialPMatrix` | 1303-1304 | §9.1 The trivial `PMatrix`: every entry is `POE.unknown`. | Definition |
| `trivialPMatrix_invariant` | 1306-1310 | Every permutation preserves `trivialPMatrix`, discharging the P-invariance hypothesis automatically. | — |
| `SchurianSchemeGraph.toSchemeProfile_trivialP` | 1312-1319 | Specialisation of `toSchemeProfile` to trivial P: P-invariance is automatic, leaving only `Step2_target`. | Definition, `noncomputable` |
| `IsSchurianSchemeGraph'` | 1338-1344 | §9.2 Concrete schurian-scheme-graph predicate: `adj` arises as the derived adjacency of some `SchurianSchemeGraph`. | Structure |
| `theorem_2_HOR_concrete` | 1346-1373 | **Theorem 2 (HOR for schurian scheme graphs), concrete form.** From `IsSchurianSchemeGraph' adj` plus P-invariance plus a `Step2_target` witness, derive the `OrbitPartition ↔ warmRefine` equivalence. | — |
| `theorem_2_HOR_concrete_trivialP` | 1375-1388 | `theorem_2_HOR_concrete` for trivial P: P-invariance becomes automatic, leaving only `Step2_target`. | — |
| `trivialSchurianSchemeGraph` | 1402-1414 | §9.3 The trivial 1-vertex schurian scheme graph (empty edge set, identity automorphism only). | Definition |
| `trivialSchurianSchemeGraph_step2` | 1416-1422 | `Step2_target` holds trivially on the 1-vertex scheme: any two vertices in `Fin 1` are equal. | — |
| `theorem_2_HOR_trivial` | 1424-1442 | **First fully discharged Theorem 2 instance.** For the trivial 1-vertex scheme with trivial P, the `OrbitPartition ↔ warmRefine` equivalence holds unconditionally. | — |
| `step2_of_rank_le_one` | 1456-1495 | §9.4 Step 2 for rank ≤ 1 schurian scheme graphs: `vProfile` takes only `0` (at `v`) and `1` (elsewhere), so warmRefine separation suffices. | — |
| `theorem_2_HOR_concrete_rank_le_one` | 1497-1509 | **Theorem 2 unconditional for rank ≤ 1 schurian scheme graphs** (e.g. K_n). | — |
| `Step2_at_depth` | 1526-1535 | §10 Depth-parametrised Step 2: iter[k] equality implies `vProfile` equality; a depth-explicit version of `Step2_target`. | Definition |
| `step2_of_step2_at_depth` | 1537-1545 | `Step2_at_depth G P v k` for `k ≤ n` lifts to `Step2_target G P v`. | — |
| `ncard_setOf_eq_filter_card` | 1605-1612 | Bridge lemma: for `Fintype` and decidable `p`, `{x | p x}.ncard = (Finset.univ.filter p).card`. Bridges `Set.ncard`-based `schemePart_at` to `Finset.filter.card` outputs. | — |
| `schemePart_at` | 1614-1638 | §10.1 Recursive partition predicate at depth `k`: depth 0 is `χ_v`-equality; depth `k+1` adds matching (adj, P, depth-`k` class) counts over neighbours. | Definition |
| `iter_refines_schemePart_at` | 1698-1785 | §10.3 **Inductive refinement.** The `iter[k] χ_v` partition refines `schemePart_at G P v k`; the substantive intersection-number induction step of Step 2. | — |
| `Step2_converges_at` | 1803-1810 | §10.4 Step 2 convergence at depth `k`: `schemePart_at`-k equivalence implies `vProfile` equality. | Definition |
| `step2_of_converges_at` | 1812-1823 | Step 2 from convergence plus the inductive step: `Step2_converges_at G P v k` with `k ≤ n` gives `Step2_target G P v`. | — |
| `schemePart_at_one_to_v` | 1854-1904 | §10.5 **Depth-1 extraction.** For `w, u ≠ v`, `schemePart_at G P v 1 w u` forces `adj w v = adj u v ∧ P w v = P u v`. | — |
| `RelOfPairDetByAdjP` | 1933-1941 | §10.6 **Depth-1 separation hypothesis**: `(adj v ·, P v ·)` determines `relOfPair v ·` on non-`v` vertices. | Definition |
| `step2_converges_at_one_of_det` | 1943-1970 | **Step 2 convergence at depth 1 under depth-1 separation.** | — |
| `step2_of_det` | 2003-2013 | §10.7 `Step2_target G P v` from `RelOfPairDetByAdjP` (lifts depth-1 convergence). | — |
| `theorem_2_HOR_concrete_of_det` | 2015-2025 | **Theorem 2 unconditional under depth-1 separation** (Petersen-class). | — |
| `AdjSeparatesRelations` | 2048-2052 | §10.8 Cleaner reformulation of depth-1 separation: `(· ∈ J)` is injective on non-diagonal relations. P-free. | Definition |
| `relOfPairDetByAdjP_of_adjSeparates` | 2054-2070 | `AdjSeparatesRelations` implies `RelOfPairDetByAdjP`. | — |
| `adjSeparates_of_rank_two_J_singleton` | 2085-2129 | **`rank = 2` + `|J| = 1` ⇒ `AdjSeparatesRelations`.** The unique element of `J` distinguishes the two non-diagonal relations. | — |
| `relOfPairDetByAdjP_of_rank_two_J_singleton` | 2131-2138 | Combined: `rank = 2` + `|J| = 1` ⇒ `RelOfPairDetByAdjP`. | — |
| `theorem_2_HOR_concrete_rank_two_J_singleton` | 2140-2154 | **Theorem 2 unconditional for rank-2 + `|J| = 1` schurian scheme graphs** — covers Petersen, Kneser `K(5,2)`, Johnson `J(5,2)`. Axiom-clean. | — |
| `Depth2Det` | 2182-2198 | §10.9 **Depth-2 separation predicate**: the depth-2 invariant (adj/`P`-to-`v` plus the depth-1 block-degree vector) determines `relOfPair v ·`. Weaker than `RelOfPairDetByAdjP`. | Definition |
| `det2_of_det` | 2200-2207 | Depth-1 separation ⇒ depth-2 separation (ignores block-degrees). | — |
| `step2_converges_at_two_of_det2` | 2209-2238 | **Step 2 convergence at depth 2 under depth-2 separation.** | — |
| `step2_of_det2` | 2240-2255 | Lifts `Step2_converges_at … 2` to `Step2_target` (`n < 2` vacuous via `Fin` subsingleton). | — |
| `theorem_2_HOR_concrete_of_det2` | 2257-2269 | **Theorem 2 unconditional under depth-2 separation**; depth-2 analogue of `theorem_2_HOR_concrete_of_det`. | — |
| `schemePart_at_of_orbit` | 2302-2312 | A v-fixing `P`-preserving automorphism puts `w, u` in the same `schemePart_at k` class (`k ≤ n`). | — |
| `orbit_of_vProfile_eq` | 2314-2328 | `vProfile`-equality ⟹ `OrbitPartition` (schurian Step 1 plus P-invariance). | — |
| `ncard_eq_sum_POE` | 2330-2345 | P-value fibering of an `ncard`: the count splits over the finitely-many `POE` values of `P x ·`, dropping `P` from a block-degree count. | — |
| `IntersectionSeparates` | 2347-2356 | §10.10 **Intersection-number separation hypothesis**: `intersectionNumber j0 j0 ·` distinguishes the non-edge, non-diagonal relations (those adjacency cannot). | Definition |
| `depth2Det_of_intersectionSeparates` | 2358-2482 | **Discharges `Depth2Det`** for single-edge (`J = {j0}`) schurian scheme graphs with an edge-neighbour of `v` and intersection-number separation. | — |
| `theorem_2_HOR_concrete_intersectionSeparates` | 2484-2504 | **Theorem 2 unconditional for single-edge schurian scheme graphs with intersection-number separation** — first genuinely rank-≥-3 coverage (e.g. the 7-cycle). Strictly subsumes the rank-2/`|J|=1` case. Axiom-clean. | — |
| `RelIsolatedAt` | 2532-2539 | §10.11 **Relation-isolation predicate**: relation `l`'s `schemePart_at k` class is exactly `R_l` from `v`. The bootstrap's central object. | Definition |
| `vProfile_imp_schemePart_at` | 2541-2550 | The free ⊇ direction: same relation with `v` ⟹ same `schemePart_at k` class. | — |
| `schemePart_at_le` | 2552-2563 | `schemePart_at` is downward-monotone in the depth. | — |
| `relCommon_eq_intersectionNumber` | 2565-2580 | Common-neighbour count = structure constant: `#{u' : (v,u')∈R_l ∧ (z,u')∈R_m} = p^{relOfPair v z}_{l,m}`. | — |
| `isolatedCount_eq` | 2582-2638 | **The reusable counting heart**: a depth-`k`-isolated `l` lets `schemePart_at (k+1)` pin the intersection number `p^{·}_{l,j0}` (block-degree into `R_l`, summed over `P`). | — |
| `relIsolatedAt_one_j0` | 2640-2676 | **Base case**: the edge relation `j0` is isolated at depth 1. | — |
| `relIsolatedAt_zero` | 2678-2692 | The diagonal `R_0 = {v}` is isolated at every depth. | — |
| `relIsolatedAt_mono` | 2694-2709 | Isolation is upward-closed in depth (`k ≤ j ≤ n`). | — |
| `relIsolatedAt_succ` | 2711-2759 | **The bootstrap step**: a finset `Iso` of depth-`k`-isolated relations plus a separation pinning `i` by `(adjacency, counts into Iso)` ⟹ `i` is isolated at depth `k+1`. | — |
| `convergence_of_all_isolated` | 2761-2770 | All relations isolated at depth `k` ⟹ `Step2_converges_at G P v k` (`schemePart_at k` = `vProfile` partition). | — |
| `theorem_2_HOR_concrete_of_isolation` | 2772-2791 | **Theorem 2 from an isolation chain** — the general engine. Exhibiting that every relation isolates by depth `k ≤ n` gives Theorem 2 unconditionally. Axiom-clean. | — |
| `theorem_2_HOR_concrete_intersectionSeparates3` | 2793-2860 | **Theorem 2 for depth-3 single-anchor schemes** (e.g. the 9-cycle) — reaches rank-≥-4 schemes the depth-2 result cannot. Axiom-clean. | — |

| `occursFromV` | 2880-2886 | §10.12 — The relations that actually occur from `v` (non-empty blocks `R_l`); the honest carrier for the isolation closure, keeping its saturation depth `≤ n`. | Definition, `noncomputable` |
| `mem_occursFromV` | 2888-2891 | Membership criterion: `l` occurs from `v` iff some `w` has `relOfPair v w = l`. | — |
| `zero_mem_occursFromV` | 2893-2895 | The diagonal relation `R₀` always occurs from `v`. | — |
| `occursFromV_card_le` | 2897-2900 | At most `n` relations occur from `v` — the bound that holds the closure depth at `≤ n`. | — |
| `IsoPinned` | 2902-2910 | §10.12 — `i` is uniquely pinned by `Iso`: the only non-diagonal relation with its `(edge-membership, intersection-counts into Iso)` signature, exactly the `hsep` hypothesis of `relIsolatedAt_succ`. | Definition |
| `isolationStep` | 2912-2918 | §10.12 — One round of the isolation closure: keep `Iso` and add every relation occurring from `v` that is pinned by `Iso`. The extensive operator driving the saturation engine. | Definition, `noncomputable` |
| `mem_isolationStep` | 2920-2927 | Membership in one closure round: already isolated, or occurring from `v` and newly pinned. | — |
| `subset_isolationStep` | 2929-2933 | The closure round is extensive (`Iso ⊆ isolationStep`), feeding the generic saturation engine. | — |
| `isolationStep_subset_occursFromV` | 2935-2943 | The closure round preserves the `occursFromV` bound, so the engine saturates within `≤ n` steps. | — |
| `relIsolatedAt_of_not_occurs` | 2945-2951 | Relations that never occur from `v` are vacuously isolated at any depth. | — |
| `stage_relIsolatedAt` | 2953-2990 | **Stage lemma (closure ⇒ isolation engine).** Every relation in the `m`-th closure round `isolationStep^[m] {0, j0}` is isolated at depth `m + 1`, turning the saturated closure into full isolation. | — |
| `EdgeGenerates` | 2992-2999 | §10.12 — The one structural hypothesis replacing the rank ladder: the isolation closure of `{R₀, R_{j0}}` reaches every relation occurring from `v`. The scheme-graph realisation of the seal's **D1**. | Definition |
| `theorem_2_HOR_of_edgeGenerates` | 3001-3052 | **General convergence — Theorem 2 from `EdgeGenerates`.** Covers every single-edge schurian scheme graph whose edge relation generates the scheme, with no per-rank separation data: the saturation engine plus stage lemma yield orbit recovery at depth `≤ n`. | — |
| `IsoPinned.mono` | 3077-3086 | Pinning is monotone in the isolated set: a uniquely-pinned relation stays pinned under any larger `Iso ⊇ Iso1`, letting a graded chain feed the closure's growing fixpoint. | — |
| `PPolynomial` | 3088-3113 | §10.13 — A P-polynomial (metric / distance-regular) schurian scheme w.r.t. edge `j0`: relations form a distance ladder `R 0,…,R rank` with a tridiagonal intersection array and nonzero subdiagonal. The abstract form of "distance-regular". | Structure |
| `pPolynomial_pinned` | 3115-3147 | The metric pinning lemma: in a P-polynomial scheme, distance `R k` (`k ≥ 2`) is uniquely pinned among non-diagonal relations by its counts into the strictly-closer distances `{R 0,…,R (k−1)}`. | — |
| `edgeGenerates_of_pPolynomial` | 3149-3201 | **EdgeGenerates for every P-polynomial scheme.** The distance ladder walks out the isolation closure (each `R k` lands once all closer distances do), so the closure contains every relation. | — |
| `theorem_2_HOR_of_pPolynomial` | 3203-3224 | **General convergence for the metric class — Theorem 2 for every P-polynomial schurian scheme graph.** One theorem covering the entire distance-regular family (cycles, Johnson, Hamming, all DRGs) with no per-scheme separation data; the P-polynomial structure discharges `EdgeGenerates`, which the engine turns into orbit recovery. | — |
| `schemeEquiv_warmRefine_of_pPolynomial` | 3226-3249 | **(EOL scheme leg — bridge CLOSED) The block of `v` is refinement-visible.** On a P-polynomial schurian scheme graph, same `warmRefine` cell (after individualizing `v`) ⟹ same `schemeEquiv I` block. Composes recovery (`theorem_2_HOR_of_pPolynomial`: cell ⟹ `OrbitPartition adj P {v}`) with `schemeEquiv_graphOrbit` (drop the P-clause via `h.matching`). So a `ClosedSubset`'s block is a **union of `warmRefine` cells** — scheme-imprimitivity ⟹ refinement-visible split, the ingredient for "non-cascade ⟹ primitive". | — |
| `AssociationScheme.SchemeAutGroup` | 3274-3288 | §11 — The **scheme automorphism group** as a `Subgroup` of `Equiv.Perm (Fin n)` (carrier `IsSchemeAut`); mirrors `AutGroup`. The group object whose `MulAction` blocks/primitivity ground the EOL scheme leg. | Definition |
| `AssociationScheme.mem_schemeAutGroup` | 3290-3291 | Membership: `π ∈ SchemeAutGroup S ↔ IsSchemeAut S π`. | `@[simp]` |
| `AssociationScheme.schemeAutGroup_smul` | 3293-3294 | The subgroup action's `smul` is application of the underlying permutation: `g • v = (↑g) v`. | `@[simp]` |
| `AssociationScheme.smul_schemeEquiv_class` | 3296-3311 | A `schemeEquiv I`-class moves under `g ∈ SchemeAutGroup` to the class of `g • a`: `g • {y | schemeEquiv I a y} = {y | schemeEquiv I (g•a) y}` (via `schemeEquiv_isSchemeAut`). | — |
| `AssociationScheme.isBlock_schemeEquiv` | 3313-3333 | **A closed subset's `schemeEquiv I`-class is a Mathlib `IsBlock`** for the scheme-Aut action: translates are classes, and distinct classes (`schemeEquiv_equivalence`) are disjoint. The combinatorial→group block bridge. | — |
| `schemeAutGroup_isPretransitive` | 3339-3346 | **Pretransitivity is free on a schurian scheme** — the diagonal `R_0` is a single relation, so the schurian axiom at `i = 0` connects any two points by a scheme automorphism. | — |
| `exists_relOfPair_from` | 3348-3362 | **Every relation is realized from any fixed point** (schurian + every relation occurs): `∃ u, relOfPair a u = j`. The non-degeneracy companion for the primitivity correspondence. | — |
| `isPrimitive_of_isPreprimitive` | 3364-3400 | **Group-primitive ⟹ scheme-primitive** (every relation occurs): if the scheme-Aut action is `IsPreprimitive`, the only closed subsets are `{R_0}`/`univ` (a closed subset's class is a block, hence trivial, forcing the subset trivial). | — |
| `isPreprimitive_of_isPrimitive` | 3402-3486 | **Scheme-primitive ⟹ group-primitive** (the leg-C-useful direction, every relation occurs): a block `B ∋ a` is `Aut_a`-invariant ⟹ a union of `vProfile` classes ⟹ `B = schemeEquiv I_B`; the intersection numbers make `I_B` closed, so primitivity forces `B` trivial. | — |
| `isPreprimitive_iff_isPrimitive` | 3488-3509 | **(EOL scheme leg, group side) Scheme primitivity = group-action preprimitivity.** On a schurian scheme where every relation occurs, combinatorial `IsPrimitive` ⟺ Mathlib `IsPreprimitive` of `SchemeAutGroup` — the standard primitive-permutation-group notion the cited Babai/Sun–Wilmes classification is stated against. | — |
| `PrimitiveCCClassification` | 3549-3563 | §12 **(EOL scheme leg) The cited classification** (Babai 1981 / Sun–Wilmes 2015 on primitive coherent configurations), a named `Prop` parametrized by the largeness + Cameron-scheme predicates — carried as an explicit hypothesis, **never a fresh `axiom`**: every group-preprimitive, CC-rank-≥-3, **large** schurian scheme (every relation occurring) is a Cameron scheme. Largeness is essential (excludes the small/cascading `C₇`). | Definition |
| `exhaustiveObstruction_scheme` | 3565-3582 | §12 **(EOL scheme leg, capstone) Exhaustive-Obstruction Lemma on scheme residuals, modulo the cited classification.** A **primitive** (`IsPrimitive`), **large** (`IsLargeScheme` = non-cascade / super-poly Aut), CC-rank-≥-3 schurian scheme residual is a Cameron section. The content is the landed bridge `isPreprimitive_of_isPrimitive` turning the descent's combinatorial primitivity into the group preprimitivity `hClassify` consumes; the Cameron case still flags (classification half — Cameron-hard, **not** GI-hard). Largeness is the genuine driver (not non-abelian — plan §4 R3). | — |
| `exhaustiveObstruction_scheme_trichotomy` | 3584-3603 | §12 **(EOL scheme leg) EOL trichotomy (doc §1 disjunction form).** Given the cited classification and rank ≥ 3, every schurian scheme residual is one of: **not primitive** (cascade-recoverable), **not large** (small Aut — recoverable/abelian region), or a **Cameron scheme** — the negation-complete tiling (primitive? large?) faithfully excluding the small-but-primitive `C₇`-type schemes from the Cameron branch. | — |
| `BlockRefinementVisible` | 3617-3625 | §13 **(EOL Step 3a, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** The block of `v` from a closed subset `I` is **refinement-visible**: same `warmRefine` cell ⟹ same `schemeEquiv I` block. Quarantines Step 3a's WL-dimension boundary into one predicate (implied by orbit recovery; broader validity = the open A2 probe). | Definition |
| `schemeEquiv_warmRefine_of_edgeGenerates` | 3627-3646 | §13 **(EOL Step 3a)** The block-visibility bridge on the `EdgeGenerates` class — widens `schemeEquiv_warmRefine_of_pPolynomial` from metric/`PPolynomial` to every edge-generating schurian scheme graph (recovery via `theorem_2_HOR_of_edgeGenerates`, then the general `schemeEquiv_graphOrbit`). | — |
| `blockRefinementVisible_of_edgeGenerates` | 3648-3657 | §13 **(EOL Step 3a)** Discharges `BlockRefinementVisible` on the orbit-recovery (`EdgeGenerates`) class — every closed-subset block of `v` is refinement-visible where the edge relation generates the scheme. | — |
| `cell_splits_of_imprimitive` | 3659-3697 | §13 **(EOL Step 3a — the reduction)** Imprimitive (non-trivial closed subset `I`) + block-visibility ⟹ `warmRefine` separates two **non-`v`** vertices (one in `v`'s block, one out): genuine refinement progress on an imprimitive scheme, the ingredient feeding the (3b) decomposition recursion toward the primitive base case (§12 capstone). | — |
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
| `colourMatch_eq_aut` | 317-332 | §C.2 **Leg-(a) linchpin (harvest-window).** At a **discrete** footprint, any colour-match permutation `t` (`warmRefine χ₂ ∘ t = warmRefine χ₁`) carried by an orbit automorphism `g` *equals* `g` — forced by `warmRefine_transport` + injectivity. The harvest *argument* ("harvest window ⟹ harvested"), class-agnostic; no σ-coherence / cycle / rank rebasing. | — |
| `colourMatch_isAut` | 334-345 | §C.2 **Leg-(a) deliverable.** The colour-match candidate `t` is an automorphism (`t = g`) — the harvest's verification succeeds whenever the orbit pair is genuine, given a discrete footprint. | — |
| `indivWithRep` | 347-354 | §C.2 Uniform-colour individualization: committed set `S` by index **plus** one explored rep `r` with a single fresh colour `n+1`. The uniform colour is what lets the orbit automorphism transport branch-`r₁` onto branch-`r₂` (index colours would split the swapped pair). | Definition |
| `indivWithRep_transport` | 356-373 | §C.2 The transport hypothesis discharged for `indivWithRep`: an orbit automorphism fixing `S` and sending `r₁ ↦ r₂` (`r₂ ∉ S`) carries the branch-`r₁` colouring onto the branch-`r₂` colouring (`χ₂ ∘ g = χ₁`). | — |
| `harvest_isAut_of_discrete` | 375-389 | §C.2 **Leg-(a), grounded.** Orbit automorphism exists (fixes path `S`, `g r₁ = r₂`, `r₂ ∉ S`) + **discrete** branch-`r₂` footprint ⟹ the colour-match candidate verifies. The remaining input — discreteness within a bounded depth — is the (class-specific, leg-B-only) depth witness, not the harvest. | — |
| `IsColourMatch` | 391-397 | §C.2 The cascade harvest's construction relation: `t` matches branch-`w`'s refined colours to branch-`v`'s (`warmRefine χ_w ∘ t = warmRefine χ_v`, `χ_v = indivWithRep D v`). The interface the `colourMatchPerm` / `matchOracle` of M-B (open) builds and verifies. | Definition |
| `colourMatch_complete` | 399-409 | §C.2 **Completeness brick.** An `Aut_D` witness `g` (fixes `D`, `g v = w`, `w ∉ D`) *is* a colour-match (`warmRefine_transport` ∘ `indivWithRep_transport`), so at a recoverable node the construction is non-empty. Leg-(a)'s completeness direction. | — |
| `colourMatch_unique` | 411-424 | §C.2 **Uniqueness brick.** `colourMatch_eq_aut` against `IsColourMatch`: at a discrete footprint any colour-match equals the orbit automorphism `g`. With `colourMatch_complete`, the colour-match at a discrete recoverable node exists, is unique, and is `g`. | — |
| `colourMatch_exists_of_cellsAreOrbits` | 440-453 | **§C.2 The firing certificate exists.** At an orbit-recoverable node the orbit automorphism *is* a verifying colour-match (`colourMatch_complete`), so the harvest's construction target is non-empty with no order/σ data and no discreteness — the existence half of folding Leg B's firing into the colour-model recovery. | — |
| `harvest_fires_of_cellsAreOrbits_discrete` | 455-470 | **§C.2 Leg B fires in the colour model.** At an orbit-recoverable + discrete footprint any constructed colour-match for the decision pair verifies as an automorphism — the order-free, class-agnostic firing that folds the hidden-abelian (linear-oracle) case into the same harvest as the cascade oracle. | — |
| `isAut_swap_of_twin` | 499-533 | A twin pair's transposition is an automorphism: if `v, w` have identical adjacency to every other vertex of a simple graph, `swap v w` preserves `adj`. Shared with the linear oracle's twin `ConfigSwap`. | — |
| `orbitPartition_swap_of_twin` | 535-600 | An order-undecided twin pair `v, w ∉ S` is an `Aut_S`-orbit pair at **any** individualized set, witnessed by the transposition `(v w)`. The reconstruction core behind the twin-endpoint and twin-cells results. | — |
| `cellsAreOrbits_of_compl_card_le_two` | 602-716 | **Twin endpoint of the support spectrum.** When at most two vertices stay un-individualized (`|Sᶜ| ≤ 2`), `CellsAreOrbits` holds via the omitted pair's transposition; with `cellsAreOrbits_of_discrete` it pins both ends. | — |
| `cellsAreOrbits_of_twin_cells` | 718-774 | `CellsAreOrbits` at **arbitrary** support whenever every same-cell pair is an order-undecided twin — the genuine-twin / module abelian regime (not CFI, which has no twins). The twin-reconstructible slice of the open localisation obligation. | — |
| `orbitRecoverableAt_of_twin_cells` | 776-795 | Oracle-vocabulary form of `cellsAreOrbits_of_twin_cells`: on the twin regime refinement computes the orbit partition at any node, with no depth bound. | — |
| `RecoverableByDepth` | 797-806 | Cascade-class membership for the oracle contract: there is a polynomially-bounded depth at which cells = orbits (the bound carries all the content). | Definition |
| `recoverableByDepth_of_cascade` | 808-814 | Cascading at depth `k` gives `RecoverableByDepth … k` — the cascade-class foundation in oracle-contract form. | — |
| `recoverableByDepth_cfi` | 816-822 | **(1a), proved for CFI** (axiom-free, odd-degree): recoverable by depth `cfi_depth_bound h` (≤ baseSize ≤ n/6). | — |
| `recoverableByDepth_scheme` | 824-836 | **(1a), proved for schemes** (axiom-free, rank 2 / `|J| = 1`): recoverable by depth 1, at the very node the oracle acts on. | — |
| `recoverableByDepth_pPolynomial` | 838-855 | **(1a), proved for the whole metric/DRG family** (axiom-free, P-polynomial / `|J|=1`): recoverable by depth 1, via `theorem_2_HOR_of_pPolynomial`. Generalizes `recoverableByDepth_scheme` (rank-2 only) to every P-polynomial schurian scheme graph — cycles, Johnson, Hamming, all DRGs — in one oracle-vocabulary export; depth-1 cells non-singleton (genuine recovery at the structural oracle's node). | — |
| `recoverableByDepth_univ` | 857-864 | Every graph is trivially recoverable by depth `n` (individualize everything), so only the *polynomial* depth bound is cascade-class content. | — |
| `CascadeComplete` | 871-878 | Completeness contract: the oracle certifies every genuine `Aut_D`-orbit pair; with soundness it then computes the orbit relation exactly. | Definition |
| `certifies_iff_orbit` | 880-894 | For a sound and complete cascade oracle, it returns `some` exactly on the pairs sharing an `Aut_D`-orbit. | — |
| `CellComplete` | 896-903 | The polynomial completeness contract: the oracle certifies every pair sharing a 1-WL cell (refinement-decidable). | Definition |
| `complete_of_cellComplete_recoverable` | 905-918 | **Key theorem.** At an orbit-recoverable node, certifying every same-cell pair already certifies every orbit — reducing orbit-completeness to a polynomial check. | — |
| `VerdictIsoInvariant` | 965-978 | Iso-invariance contract (strategy §15 gap 2): the oracle's verdict depends only on the iso-invariant 1-WL partition. Derivable — see `verdictIsoInvariant_of_complete`. | Definition |
| `cascadeComplete_of_localization` | 980-991 | Capstone: cell-completeness plus all-nodes recoverability yields `CascadeComplete`, naming the open localisation obligation as its hypotheses. | — |
| `cascadeComplete_of_cellsAreOrbits` | 993-1004 | Capstone stated against the single open implication: cell-completeness plus `CellsAreOrbits` at every node yields `CascadeComplete`. | — |
| `verdictIsoInvariant_of_complete` | 1006-1021 | **Key theorem.** A sound, complete oracle at orbit-recoverable nodes is automatically iso-invariant, so iso-invariance is part of localisation rather than a separate obligation. | — |
| `computes_orbits_of_complete` | 1023-1035 | Capstone: a sound and complete cascade oracle computes the `Aut_D`-orbit relation exactly (program-level correctness, given the completeness obligation). | — |

| `rankPerm_inv_mul_eq_of_match` | 1052-1064 | §C.4 M-B — the rank-composition identity behind `colourMatchPerm = g`: if `g` value-matches the two colourings (`χ₂ ∘ g = χ₁`), then `(rankPerm χ₂)⁻¹ * rankPerm χ₁ = g`. Pure `vertexRank_comp` reindexing, no graph structure. | — |
| `colourMatchPerm` | 1066-1076 | §C.4 **M-B — the colour-match permutation.** The explicit `Equiv.Perm` from the two *discrete* branch colourings, as the rank composition `(rankPerm χ_w)⁻¹ * (rankPerm χ_v)` (`χ_r = warmRefine adj P (indivWithRep n D r)`). Always well-defined given discreteness; `= g` at a recoverable node. | Definition, `noncomputable` |
| `colourMatchPerm_eq_of_orbit` | 1078-1091 | §C.4 **M-B completeness linchpin.** An `Aut_D` witness `g` (`g v = w`, `w ∉ D`) value-matches the two branch colourings (`colourMatch_complete`), so `colourMatchPerm = g` — built from the colours, not assumed. | — |
| `matchOracle` | 1092-1110 | §C.4 **M-B — the colour-match cascade oracle.** Constructs `colourMatchPerm` (when both footprints discrete) and returns it **iff** it verifies as an `Aut_D` orbit map (`IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`). Construct-and-check, not the existential shortcut. | Definition, `noncomputable` |
| `matchOracle_fires` | 1112-1133 | §C.4 Evaluation lemma: given discreteness + the four verification facts about `colourMatchPerm`, `matchOracle` returns `some`. The engine of the completeness proof. | — |
| `matchOracle_orbitMapSpec` | 1135-1145 | §C.4 **M-B soundness — `OrbitMapSpec`, unconditional.** When `matchOracle` fires, its four checks *are* the `OrbitPartition` witness conditions, so the returned perm certifies a genuine `Aut_D` orbit pair. No discreteness/recoverability hypothesis. | — |
| `matchOracle_cellComplete` | 1147-1183 | §C.4 **M-B completeness — `CellComplete`.** Conditional on every node one-step-discretizing (`hdisc`, = the exposure-depth witness / M-C / "B's core") and `CellsAreOrbits` everywhere (`hco`, = localisation): at a same-cell pair the orbit automorphism exists, `colourMatchPerm = g`, so the oracle fires. | — |
| `matchOracle_cascadeComplete` | 1185-1196 | §C.4 **M-B capstone — `CascadeComplete`.** `matchOracle` computes the orbit relation exactly, reduced to the two named-open hypotheses (discretizing depth + `CellsAreOrbits`); soundness is already unconditional. | — |
| `matchOracle_verdictIsoInvariant` | 1198-1212 | §C.4 **M-B — flag iso-invariance, free.** With soundness + completeness, `verdictIsoInvariant_of_complete` gives the verdict as a function of the iso-invariant 1-WL partition (strategy §15 gap 2) for `matchOracle` on the recoverable class. | — |
| `discrete_of_samePartition` | 1231-1234 | §C.4b Discreteness transfers across `samePartition`: `samePartition χ₁ χ₂ → Discrete χ₁ → Discrete χ₂`. | — |
| `warmRefine_samePartition` | 1236-1241 | §C.4b `warmRefine` respects `samePartition` (specialization of `warmRefine_agree_off'`, `D = ∅`): equal-partition starts warm-refine to equal-partition results. | — |
| `samePartition_indivWithRep_insert` | 1243-1284 | §C.4b **Single-rep footprint = indexed `insert`.** For `r ∉ D`, `indivWithRep n D r` and `individualizedColouring n (insert r D)` induce the same partition (`r` globally unique either way). | — |
| `discrete_indivWithRep_of_discrete_insert` | 1286-1295 | §C.4b **The M-B depth-witness bridge.** M-B's `hdisc` follows from discreteness of the *indexed* `individualizedColouring (insert r D)` — connecting the depth witness to the `RecoverableByDepth` framework, class-agnostically. | — |
| `indivWithSet` | 1312-1317 | §C.5 **M-C — multi-step uniform individualization.** Individualize the committed set `S` by index, plus an explored *set* `R` with a single uniform fresh colour `n+1`. Generalizes `indivWithRep` (`R = {r}`); uniform on `R` is forced by transport (an orbit aut moves `R`). | Definition |
| `indivWithRep_eq_indivWithSet` | 1319-1322 | §C.5 `indivWithRep n S r = indivWithSet n S {r}` — the singleton bridge to M-B. | — |
| `indivWithSet_transport` | 1324-1343 | §C.5 **M-C transport.** An orbit aut `g` fixing `S` with `R₂ = R₁.image g` carries the branch-`R₁` colouring onto branch-`R₂` (`χ₂ ∘ g = χ₁`); the `indivWithRep_transport` generalization (uniform colour on the moved set is what makes it hold). | — |
| `IsColourMatchSet` | 1345-1349 | §C.5 The multi-step colour-match relation: `t` matches branch-`R₂`'s refined colours to branch-`R₁`'s. The `IsColourMatch` generalization. | Definition |
| `colourMatchSet_complete` | 1351-1358 | §C.5 **M-C completeness brick.** The orbit aut `g` (fixing `S`, `R₂ = R₁.image g`) *is* a colour-match (`warmRefine_transport ∘ indivWithSet_transport`). | — |
| `colourMatchSet_unique` | 1360-1370 | §C.5 **M-C uniqueness brick.** At a discrete branch-`R₂` footprint any colour-match `= g`, via the colouring-generic `colourMatch_eq_aut`. | — |
| `harvestSet_isAut_of_discrete` | 1372-1382 | §C.5 **M-C harvest brick.** At a discrete branch-`R₂` footprint the colour-match candidate verifies (`= g`) — the harvest now fires at a footprint discretized by an explored *set* (a sequence), not just one rep. | — |
| `colourMatchPermSet` | 1384-1391 | §C.5 **M-C — the multi-step colour-match permutation.** The rank composition `(rankPerm χ_{R₂})⁻¹ * (rankPerm χ_{R₁})` for set footprints; `colourMatchPerm` is the `R₁={v}, R₂={w}` case. | Definition, `noncomputable` |
| `colourMatchPermSet_eq_of_orbit` | 1393-1403 | §C.5 `colourMatchPermSet = g` at a recoverable set-footprint (`rankPerm_inv_mul_eq_of_match` ← `vertexRank_comp` + `colourMatchSet_complete`); the multi-step `colourMatchPerm_eq_of_orbit`. | — |
| `colourMatchSet_exists_of_cellsAreOrbits` | 1405-1418 | §C.5 **The multi-step firing certificate exists.** From `CellsAreOrbits` at a same-cell pair, for *any* exploration set `R₁` the orbit aut `g`, partner `R₂ = R₁.image g`, and the colour-match all exist. The open piece (M-D) is that the oracle's branch-`w` set *is* `R₁.image g` (lockstep). | — |
| `matchOracleSet` | 1431-1451 | §C.6 **M-D — the multi-step colour-match oracle.** Like `matchOracle` but individualizes a whole explored *set* `expand chain r` (per an exploration selector) on top of the committed path; constructs `colourMatchPermSet`, returns it **iff** it verifies `IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`. | Definition, `noncomputable` |
| `matchOracleSet_fires` | 1453-1478 | §C.6 Evaluation lemma: discreteness + the four checks on `colourMatchPermSet` ⟹ `matchOracleSet` fires. | — |
| `matchOracleSet_orbitMapSpec` | 1480-1490 | §C.6 **M-D soundness — `OrbitMapSpec`, unconditional.** When it fires the four checks *are* the `OrbitPartition` witness; no discreteness/recoverability/lockstep hypothesis. | — |
| `LockstepExpand` | 1492-1502 | §C.6 **The lockstep correspondence** as equivariance of the exploration rule: any `P`-preserving automorphism fixing the committed path carries one branch's exploration set onto the other's (`expand chain (g v) = (expand chain v).image g`). Discharged for `forcedExpand` (`Cascade.lean`). | Definition |
| `matchOracleSet_cellComplete` | 1504-1544 | §C.6 **M-D completeness — `CellComplete`.** Reduced to set-footprint discreteness (the multi-step depth witness) + `CellsAreOrbits` + `LockstepExpand`: the lockstep supplies `R₂ = R₁.image g`, so `colourMatchPermSet = g` and the oracle fires. | — |
| `matchOracleSet_cascadeComplete` | 1546-1558 | §C.6 **M-D capstone — `CascadeComplete`** (the multi-step oracle computes the orbit relation exactly), reduced to the three named-open hypotheses. | — |
| `matchOracleSet_verdictIsoInvariant` | 1560-1573 | §C.6 **M-D — flag iso-invariance, free** (via `verdictIsoInvariant_of_complete`). | — |
| `matchOracle_fires_of_insertDiscrete` | 1606-1629 | §C.7 **Honest per-node firing (`hco`-free).** At a node where committing the path plus the query rep discretizes (the indexed `RecoverableByDepth` form, bridged by §C.4b), `matchOracle` fires on **any** genuine `Aut_D` orbit pair `(v,w)` (`v,w ∉ D`) — the orbit witness is consumed directly, so no `CellsAreOrbits`. | — |
| `matchOracle_orbit_of_fire_mono` | 1631-1645 | §C.7 **Propagate via `mono`.** A merge certified at a node holds at every shallower committed set `S ⊆ chain.D` (`OrbitPartition.mono`) — the "fire deep, prune shallow" step. | — |
| `matchOracle_certifies_iff_orbit_of_insertDiscrete` | 1647-1673 | §C.7 **Exact orbit decider at the discretizing depth.** At a footprint-discretizing node, `matchOracle` fires on `(v,w)` **iff** they are a genuine `Aut_D` orbit pair (`hco`-free). Limits: holds only under the discreteness hypotheses (cascade depth), and decides the *path-fixing* `Aut_D`, not global `Aut`. | — |
| `indivWithSeq` | 1694-1699 | §C.8 **Level-coloured exploration sequence (Leg 1).** Committed `S` by index plus the `i`-th element of `rs` by its *position* colour `n+1+i`; the position colouring (not vertex index) is what transports under an orbit automorphism. | Definition |
| `indivWithRep_eq_indivWithSeq_singleton` | 1701-1708 | §C.8 `indivWithRep n S r = indivWithSeq n S [r]` — the singleton-sequence case (`n+1+0 = n+1`). | — |
| `samePartition_indivWithSeq` | 1710-1778 | §C.8 **A1: level-coloured sequence = indexed union.** `indivWithSeq n S rs` and the indexed `individualizedColouring n (S ∪ rs.toFinset)` induce the same partition (each `rs`-vertex globally unique); unconditional. | — |
| `discrete_indivWithSeq_of_discrete_union` | 1780-1791 | §C.8 **The Leg-1 depth-witness bridge (sequence).** Sequence-footprint discreteness follows from discreteness of the indexed `individualizedColouring n (S ∪ rs.toFinset)`, so `hdiscSeq ⟸ recoverableByDepth`. Sequence generalization of `discrete_indivWithRep_of_discrete_insert`. | — |
| `idxOf_map_of_injective` | 1805-1817 | §C.8 **Position preserved by `map`.** `(l.map g).idxOf (g a) = l.idxOf a` for a permutation `g` — the pure-list core of sequence transport. | — |
| `indivWithSeq_transport` | 1819-1840 | §C.8 **A2 transport.** An orbit aut `g` fixing `S` with `rs₂ = rs₁.map g` carries the branch-`rs₁` level colouring onto branch-`rs₂` (`χ₂ ∘ g = χ₁`) — position via `idxOf_map_of_injective`, off-sequence via `individualizedColouring` invariance. | — |
| `IsColourMatchSeq` | 1842-1845 | §C.8 The sequence colour-match relation (`IsColourMatchSet` analogue): `t` matches branch-`rs₂`'s refined colours to branch-`rs₁`'s. | Definition |
| `colourMatchSeq_complete` | 1847-1854 | §C.8 **Sequence completeness brick.** The orbit aut `g` (fixing `S`, `rs₂ = rs₁.map g`) *is* a colour-match (`warmRefine_transport ∘ indivWithSeq_transport`). | — |
| `colourMatchPermSeq` | 1856-1863 | §C.8 **The sequence colour-match permutation.** Rank composition `(rankPerm χ_{rs₂})⁻¹ * rankPerm χ_{rs₁}` for level-coloured footprints; `colourMatchPermSet` with the uniform set replaced by the sequence. | Definition, `noncomputable` |
| `colourMatchPermSeq_eq_of_orbit` | 1865-1875 | §C.8 `colourMatchPermSeq = g` at a recoverable level-coloured footprint (`rankPerm_inv_mul_eq_of_match` + `colourMatchSeq_complete`). | — |
| `colourMatchSeq_exists_of_cellsAreOrbits` | 1877-1890 | §C.8 **The level-coloured firing certificate exists.** From `CellsAreOrbits`, for any sequence `rs₁` the orbit aut `g`, partner `rs₂ = rs₁.map g`, and the colour-match exist. The open piece is the ordered lockstep (A2b). | — |
| `matchOracleSeq` | 1903-1923 | §C.8 **The multi-step sequence colour-match oracle.** Like `matchOracleSet` but individualizes the ordered sequence `expand chain r` via `indivWithSeq` (so its depth witness is A1-reducible); construct-and-check on `colourMatchPermSeq`. | Definition, `noncomputable` |
| `matchOracleSeq_fires` | 1925-1949 | §C.8 Evaluation lemma: discreteness + the four checks on `colourMatchPermSeq` ⟹ `matchOracleSeq` fires. | — |
| `matchOracleSeq_orbitMapSpec` | 1951-1960 | §C.8 **Sequence soundness — `OrbitMapSpec`, unconditional.** When it fires the four checks *are* the `OrbitPartition` witness. | — |
| `LockstepExpandSeq` | 1962-1973 | §C.8 **The sequence lockstep.** The ordered (`map`, not `image`) `LockstepExpand` analogue: `expand chain (g v) = (expand chain v).map g`. Strictly stronger than the set lockstep; provably false in the multi-step regime (`lockstep_disc_imp_stab_trivial`). | Definition |
| `matchOracleSeq_cellComplete` | 1975-2014 | §C.8 **Sequence completeness — `CellComplete`.** Reduced to `hdiscSeq` (A1-reducible) + `hco` + `LockstepExpandSeq`. | — |
| `matchOracleSeq_cascadeComplete` | 2016-2028 | §C.8 **Sequence capstone — `CascadeComplete`**, reduced to the same three hypotheses (the last jointly unsatisfiable with `hdiscSeq` for multi-step — see `lockstep_disc_imp_stab_trivial`). | — |
| `matchOracleSeq_verdictIsoInvariant` | 2030-2043 | §C.8 **Sequence flag iso-invariance, free** (via `verdictIsoInvariant_of_complete`). | — |
| `fixedPointwise_of_map_self` | 2065-2073 | §C.8 A list equal to its own image under `g` is fixed pointwise by `g`: `l.map g = l → ∀ x ∈ l, g x = x`. | — |
| `lockstep_disc_imp_stab_trivial` | 2075-2109 | §C.8 **The discretizing-oracle limit (conservation of obstruction).** `LockstepExpandSeq ∧ hdiscSeq ⟹ stab_{Aut_D}(v) = 1`: the sequence oracle's completeness hypotheses hold jointly only in the single-rep regime, so the discretizing colour-match cannot harvest a multi-step moved orbit (→ cross-branch / Schreier–Sims). | — |
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
| `candidateTwist_eq_one_of_rankPerm_eq` | 424-435 | **Absorbed decision.** Equal leaf rank permutations force the candidate to be the identity — the degenerate end of the abelian regime. | — |
| `isAut_candidateTwist_of_rankPerm_eq` | 437-445 | The absorbed decision fires: the forced candidate (the identity) is an automorphism. | — |

### §L.7 — The CFI bridge (M1b): candidate as a conjugate of a graph automorphism

Now that `refineStep` is concrete, the cross-config transport (`§16.2b` in ChainDescent.lean)
lets us express the forced candidate via a *real* automorphism. A **config-swap** `g` carries the
σ-branch config onto the flip-branch config; it forces `π_σ = π_flip · g`, so the candidate is the
`π_σ`-conjugate of `g⁻¹`. This reduces the opaque `IsAut candidate adj` to the structural gadget
rank-alignment, isolating the genuine CFI nut (shared with Tier-3a B1 `hwit`): (1) a config-swap
exists, (2) its `π_σ`-conjugate is an automorphism.

| Name | Description | Notes |
|------|-------------|-------|
| `ConfigSwap` | 587-599 | A config-swap for decision `(a,b)`: a graph automorphism carrying the σ-branch configuration onto the flip-branch configuration (fixes `χι`, sends `σ.σ` to `(flipPair σ).σ`). For CFI, the gadget twist swapping the decided pair. | Structure |
| `configSwap_rankPerm` / `_flip` | The leaf rank perms differ by `g`: `π_σ = π_flip · g` (resp. `π_flip = π_σ · g⁻¹`), from transport + `vertexRank_comp`. | axiom-light |
| `configSwap_rankPerm_flip` | 618-625 | `π_flip = π_σ · g⁻¹` — the rearrangement of `configSwap_rankPerm`. | — |
| `candidateTwist_eq_conjugate` | 627-637 | **The rank-space reduction.** Given a config-swap `g`, the forced candidate is the `π_σ`-conjugate of `g⁻¹` (`candidateTwist = π_σ · g⁻¹ · π_σ⁻¹`) — the opaque rebasing exposed as a conjugate of a genuine automorphism. | — |
| `isAut_candidateTwist_iff_conjugate` | 639-650 | **The reduction.** `IsAut candidate adj ↔ IsAut (π_σ · g⁻¹ · π_σ⁻¹) adj` — the rank-space firing obligation is exactly the gadget rank-alignment, the concrete nut shared with Tier-3a B1. | — |

**§L.7b — vertex-model soundness (Approach C, the faithful C# model).** A config-swap is a real
graph automorphism, so both branches give the *same canonical leaf* — no rank-alignment needed. This
is the soundness the C# `TwistConstruction` actually uses (it verifies a vertex automorphism, not the
rank rebasing).

| Name | Description | Notes |
|------|-------------|-------|
| `canonAdj_eq_of_configSwap` | 661-676 | **Equal canonical leaves.** A config-swap implies both branches produce the identical canonical leaf — the vertex-model soundness statement (pruning the flip branch loses nothing), needing no rank-alignment. | — |
| `realizableFlip_of_configSwap` | 678-692 | A config-swap implies `RealizableFlip` (identity witness, since the leaves coincide) — the decision is a genuine `Aut(adj)` symmetry with no rank-alignment obligation. | — |

**§L.8 — CFI completeness: config-swap from a swapping automorphism (M1c step 3, the cascade-1b bridge).**
*Where a config-swap comes from.* A swapping automorphism `g` (`g a = b`, `g b = a`) is exactly an
`OrbitPartition adj P S a b` witness specialised to the size-2 decision cell — the cascade oracle's
currency. So linear-oracle CFI completeness reduces to the **shared cascade-1b** obligation
(bounded-depth half `recoverableByDepth_cfi` proved; decision-node-depth bridge open, *not* `GI∈P`).

| Name | Description | Notes |
|------|-------------|-------|
| `configSwap_of_aut` | 724-767 | **General constructor (the `hwit` entry point).** *Any* swapping automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and preserves `σ.σ` *off the flip pair* (`σ.σ (g v)(g u) = σ.σ v u` for `(v,u) ∉ {(a,b),(b,a)}`) is a `ConfigSwap` — `g` need **not** be a transposition (may move the whole coupled component). Removes the config-swap *packaging* from the open content: once the CFI gadget twist `g` and its off-pair `σ`-action are known, the `ConfigSwap` is built with no rank-alignment. | Definition |
| `configSwap_of_swap` | 769-820 | **Closed instance (the `Z₂` twin-swap).** A σ-cell-coherent transposition automorphism (`g` swaps `a,b`, fixes the rest and `χι`) is a `ConfigSwap` — the simplest genuine abelian decision. Now a thin specialisation of `configSwap_of_aut` (transposition ⇒ off-pair preservation = σ-cell-coherence). | Definition |
| `configSwap_of_twin` | 822-850 | **The twin → config-swap bridge.** An (adj, σ)-twin decision pair (adjacency-twin on a simple graph plus σ-cell-coherent, `χι a = χι b`) admits a `ConfigSwap` via the transposition `(a b)` — the linear-oracle analog of `cellsAreOrbits_of_twin_cells`, both oracles firing on the same twin/module class through one shared lemma. Not CFI (which has no twins). | Definition |
| `ConfigSwapRecoverable` | 852-862 | **Decision-node recoverability** (the named cascade-1b obligation for the linear oracle): every leaf decision admits a config-swap. The graph-level analog of `AbelianSufficiencyHolds`; open discharge `configSwapRecoverable_of_cfi` is downstream. | Definition |
| `canonAdj_eq_of_configSwapRecoverable` | 864-875 | **Capstone (pruning soundness).** Config-swap-recoverability implies both branches give the identical canonical leaf at every decision — reducing the oracle's effectiveness to the single `ConfigSwapRecoverable` hypothesis. | — |
| `realizableFlip_of_configSwapRecoverable` | 877-888 | **Capstone (real symmetry).** Config-swap-recoverability implies every leaf decision is a genuine `Aut(adj)` symmetry — vertex-model completeness, no rank-alignment needed. | — |

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
| `RankAligned` | 482-490 | The algebraic firing condition: a rank-aligned automorphism exists (`∃ g ∈ Aut(adj), g · π_σ = π_flip`). The oracle fires exactly when this holds. | Definition |
| `isAut_candidateTwist_iff_rankAligned` | 492-500 | **Interface.** The forced candidate is an automorphism iff `RankAligned` — the completeness question restated against the named predicate. | — |
| `AbelianSufficiency` | 502-512 | **The per-decision relativized completeness target.** `RealizableFlip → IsAut candidate`: if the flip is a real symmetry then the forced candidate verifies. False in the non-abelian regime (the wall); the claim to discharge on the abelian/cascade class. | Definition |
| `oracleFires_of_abelianSufficiency` | 514-529 | **Capstone (what suffices).** `AbelianSufficiency` plus a real symmetry implies the oracle fires — the linear-oracle analog of cascade's `cascadeComplete_of_localization`. | — |
| `abelianSufficiency_of_rankPerm_eq` | 531-542 | **Non-vacuous closed instance.** The absorbed decision is abelian-sufficient (candidate `= 1 ∈ Aut` outright) — validates the scaffold against a real instance. | — |
| `AbelianSufficiencyHolds` | 544-552 | The graph-level discharge target: every leaf decision is abelian-sufficient. Open obligation `abelianSufficiencyHolds_of_cfi` is downstream (via `theorem_1_HOR_cfi_oddDeg`, the same nut as Tier-3a B1's `hwit`). | Definition |
| `oracleFires_of_abelianSufficiencyHolds` | 554-568 | **Graph-level capstone.** `AbelianSufficiencyHolds` implies the oracle fires at every leaf decision that is a real symmetry — relativized completeness on the abelian class. | — |

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

| `stabilizer_eq_bot_of_isPretransitive_comm` | 324-342 | **(seal core L1, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** A transitive, faithful, **abelian** action is **free**: every point-stabilizer is trivial ("transitive abelian ⟹ regular"). The textbook root of "no non-consumed abelian species". | — |
| `existsUnique_smul_of_isPretransitive_comm` | 344-355 | **(seal core L2)** Unique candidate: in a transitive faithful abelian action exactly one group element moves `a` to `b` (existence from transitivity, uniqueness from L1's trivial stabilizer). | — |
| `smul_eq_on_orbit_of_comm` | 357-366 | **(seal core L3 — load-bearing, axiom-free)** Quotient-free, faithfulness-free form: if `g, h` both move `a` to `b` then they agree on the **whole orbit** of `a` (`g•c = k•b = h•c` for `c = k•a`). The "unique-candidate-on-the-cell" the linear-oracle harvest reads — holds for an abelian residual even with non-trivial global stabilizers (CFI). | — |
| `aut_agree_on_orbit_of_comm` | 368-382 | **(seal instantiation)** L3 for `AutGroup adj`: an **abelian residual** ⟹ two automorphisms both sending `a ↦ b` agree on every `c` in `a`'s orbit, so the decision is determined on its cell (always consumable). | — |
| `not_comm_of_orbit_disagree` | 384-393 | **(seal headline — no non-consumed abelian species)** Contrapositive: a decision `a ↦ b` whose two candidate automorphisms **disagree** on the cell forces a **non-abelian** residual. With the §12 capstone (large primitive non-abelian ⟹ Cameron), the only non-consumed symmetry is a Cameron section — the bottom-up, citation-free half of the seal. | — |
| `card_eq_of_isPretransitive_comm` | 404-418 | **(seal Step 4 — order side, [exhaustive-obstruction §0.7](../docs/chain-descent-exhaustive-obstruction.md))** A transitive, faithful, **abelian** action has `Nat.card G = Nat.card α`: the orbit map `g ↦ g•a` is a bijection (free from L1, surjective from transitivity), so order = degree ("abelian primitive ⟹ regular, hence small"). | — |
| `not_comm_of_isPretransitive_of_stabilizer_ne_bot` | 420-426 | **(seal Step 4, qualitative)** A transitive faithful action with a **non-trivial** point stabilizer (not regular) is **non-abelian** — direct contrapositive of L1. | — |
| `not_comm_of_isPreprimitive_card_lt` | 428-437 | **(seal Step 4 — the headline: large primitive ⟹ non-abelian)** A **preprimitive** faithful action with `Nat.card α < Nat.card G` (group strictly larger than its degree) is **non-abelian**, since a transitive abelian action has order = degree. The order-side proof that a primitive abelian group is `Z_p` (never large); closes the bottom-up route's Step 4 with no citation. | — |
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
| `discrete_of_cellsAreOrbits_base` | 72-79 | **(C1) Finish.** At a base `T` where cells already coincide with `Aut_T`-orbits, warm refinement at `T` is `Discrete` — the cascade reaching full canonization. | — |
| `cellsAreOrbits_compose` | 81-94 | **(C2) Composition induction.** From layer 1's unconditional `CellsAreOrbits` at `T 0` and a `LayerStep` at each subsequent layer, `CellsAreOrbits` holds at the final cumulative set `T k`. | — |
| `cumulative_card_le` | 96-102 | **Depths add (cardinality).** The cumulative individualization set `⋃_{i≤k} S i` has size at most `Σ_{i≤k} f i` when each layer is bounded by its depth `f i`. | — |
| `cascadeComposition` | 104-116 | **Theorem 3a (cascade composition) — headline, conditional form.** Cumulative sets with layer-1 recoverability, per-layer transfer steps, and the final set a base ⟹ warm refinement at `T k` reaches the discrete partition; with `cumulative_card_le` the cascade depth is `≤ Σ fᵢ`. Conditional on the `hstep` obligations (= §4.2.5, Phase D). | — |
| `cascadeComposition_single` | 124-127 | **Single-layer sanity check (k = 0).** One cascade-class layer that is a base reaches discreteness — recovers the Tier-1/Tier-2 orbit-recovery theorems as the composition's base case. | — |

### Phase D — discharging `LayerStep` (the §4.2.5 transfer), intrinsic route

Approach B (build-plan §3): stay on `Fin n`, reduce `LayerStep` to a witness-upgrade via
**set-monotonicity** of warm refinement (reusing `refineStep_iff`); the materialized-quotient
route was rejected (`refineStep` axiomatic, no cross-size API).

| Name | Description | Notes |
|------|-------------|-------|
| `Refines χ₁ χ₂` | `χ₁` refines `χ₂`: the partition of `χ₁` is finer (`χ₁ a = χ₁ b → χ₂ a = χ₂ b`). The partition order used for warm-refinement monotonicity. | Definition |
| `signature_refines` | 145-166 | **Crux of warm-refinement monotonicity.** If `χ₁` refines `χ₂`, equal `χ₁`-signatures give equal `χ₂`-signatures, since `signature χ₂` is the coarsening of `signature χ₁`. | — |
| `iterate_refineStep_refines` / `warmRefine_refines_initial` | warm refinement monotone in the initial colouring's partition order. | axiom-light |
| `individualizedColouring_refines` | 192-204 | Individualizing a superset gives a finer initial colouring: `T ⊆ T'` ⟹ `individualizedColouring n T'` refines `individualizedColouring n T`. | — |
| `warmRefine_indiv_mono` | 206-214 | **Set-monotonicity (the payoff).** Same `(T ∪ S)`-cell ⟹ same `T`-cell: 1-WL is monotone in the individualization set. The load-bearing lemma the docs had mis-cited as `warmRefine_refines`. | — |
| `WitnessUpgrade adj P T S` | **The genuine §4.2.5 content.** For `v, w` in the same `Aut_T`-orbit and the same `(T ∪ S)`-cell, the orbit relation upgrades to `Aut_{T∪S}`. The Phase-D interface predicate. | Definition |
| `layerStep_of_witnessUpgrade` | 228-235 | **The reduction — where Phase C meets the per-layer content.** A `WitnessUpgrade` discharges a `LayerStep`, via set-monotonicity then `CellsAreOrbits T` then the upgrade. | — |
| `layerStep_empty` / `layerStep_subset` / `layerStep_of_cellsAreOrbits` / `layerStep_of_discrete` | Trivial real instances: no-op layer (`S = ∅`), `S ⊆ T`, independently-recoverable target, and the discretizing recursion-bottom. | axiom-light |
| `witnessUpgrade_of_pathFixing` | 260-275 | **Bridge to harvested generators.** If every same-orbit, same-cell pair admits a `P`-preserving automorphism whose support avoids `T ∪ S` (fixes the committed path) and sends `v ↦ w`, the witness-upgrade holds — exactly what the cascade/linear oracles produce. | — |

### Step 5 — the synthesis (Theorem 3a reduced to harvested generators)

| Name | Description | Notes |
|------|-------------|-------|
| `cascadeComposition_pathFixing` | 294-315 | **Theorem 3a, reduced to harvested path-fixing generators.** Cumulative sets by increments, layer-1 recoverable, every layer's residual symmetry realized by path-fixing automorphisms (`hwit`), and the final set a base ⟹ discrete warm refinement at `T k`. Reduces all of Theorem 3a to the single hypothesis of per-layer path-fixing witness existence. | — |
| `cascadeComposition_twoLayer` | 317-332 | **Smallest genuine composition.** An outer cascade-class layer at `T₀`, an inner path-fixing layer with increment `S`, and the union a base ⟹ discreteness — the `CFI(scheme)` / `Scheme(CFI)` shape. | — |

**Phase 6b — CFI gadget flips discharge the Tier-3a `hwit`.** The Stage-3 gadget flip (`CFI.lean §15`)
discharges `cascadeComposition_pathFixing`'s `hwit` for a CFI layering, conditional only on the per-layer
existence of committed-set-avoiding gadget flips (the cascade-1b content).

| Name | Description | Notes |
|------|-------------|-------|
| `CFILayerGadgetFlippable` | Per-layer CFI gadget-flip existence: for each layer and same-orbit/same-cell pair `(v,w)`, an even-symmetric cycle `F` whose flip maps `v ↦ w` with `T i ∪ S i` in `F`-free gadgets. The `hwit` analog of the linear oracle's `CFIGadgetFlippableLocal`. | Definition |
| `cfiLayer_pathFixing_hwit` | **The `hwit` drop-in.** `CFILayerGadgetFlippable` (+ `P` Aut-invariant) ⟹ the Tier-3a `hwit` hypothesis, directly via `cfiFlipAut_pathFixing_witness`. | — |
| `cascadeComposition_cfi` | **Theorem 3a for CFI layers.** A CFI layering whose residual orbit maps are realised by committed-set-avoiding gadget flips reaches the discrete partition — `cascadeComposition_pathFixing` with `hwit` discharged by the Stage-3 flips (conditional only on the cascade-1b cycle existence). | — |
| `recoverableByDepth_of_pathFixing_layers` | 402-420 | **The harvest-window connector.** Lands `cascadeComposition_pathFixing`'s `Discrete` output onto the harvest `RecoverableByDepth` conclusion: a layer chain with per-layer path-fixing `hwit` and a base endpoint gives `RecoverableByDepth adj P b` at the chain-length bound. | — |
| `recoverableByDepth_of_cascadeComposition_cfi` | 422-435 | **CFI corollary of the connector.** `RecoverableByDepth` for a CFI layering via `cascadeComposition_cfi` — the connector with `hwit` discharged by the Stage-3 gadget flips. | — |
| `ResidualAut` | 450-456 | **Residual automorphism.** A `P`-preserving automorphism of `adj` fixing `S` pointwise — an element of the residual group `Aut_S^P`; the building block of the screen predicates. `OrbitPartition adj P S v w ↔ ∃ π, ResidualAut π ∧ π v = w`. | Definition |
| `ResidualAbelian` | 458-463 | **D2 — abelian residual.** The residual group `Aut_S^P` is abelian (any two residual automorphisms commute) — the screen's hidden-abelian / linear leg (calculator §6); the `¬IsBase`-guarded form is the D2 disjunct. | Definition |
| `orbitPartition_iff_residualAut` | 465-471 | `OrbitPartition adj P S v w` unfolds to a `ResidualAut` carrying `v ↦ w`. | — |
| `ResidualAut.mul` | 489-499 | The residual group is closed under composition: composing two `P`-preserving automorphisms fixing `S` pointwise yields another. | — |
| `ResidualInvolutive` | 501-507 | **D2, the exponent-2 form.** Every residual automorphism is an involution — `Aut_S^P` has exponent ≤ 2 (an elementary-abelian `Z₂^d`, CFI's gauge group). The precise form of D2 the swap content needs; strictly stronger than `ResidualAbelian`. | Definition |
| `residualAbelian_of_involutive` | 509-518 | **Exponent-2 ⟹ abelian.** A residual group of involutions commutes — wiring the abstract `ResidualAbelian` predicate to the precise `ResidualInvolutive`. | — |
| `orbitPartition_swap_of_involutive` | 520-533 | **An involutive orbit witness is a swap.** With an exponent-2 residual, an `Aut_S`-orbit pair `a, b` has a residual automorphism with `g a = b` *and* `g b = a` — closing the map-vs-swap gap class-agnostically (the content the CFI route obtains from gadget involutions). | — |
| `swap_of_cellsAreOrbits_involutive` | 535-545 | **The class-agnostic swap certificate at a recoverable node.** Where orbit recovery holds (`CellsAreOrbits`) and the residual is exponent-2, every same-cell decision pair carries a swapping orbit automorphism — the linear oracle's 'a swap exists' input from recovery + D2, replacing the per-class `CFIGadgetFlippable` derivation. | — |
| `residualAut_eq_one_of_isBase` | 547-554 | Under a base (`IsBase`), every residual automorphism is the identity — it can move no point. | — |
| `residualAbelian_of_isBase` | 556-561 | **Trichotomy base case.** A trivial residual (under `IsBase`) is vacuously abelian, so `ResidualAbelian` holds at any base. | — |
| `residualAbelian_mono` | 563-570 | **D2 inherited down the descent.** `ResidualAbelian` passes from `S` to any `S' ⊇ S` (the residual shrinks to a subgroup of an abelian group). | — |
| `StabilizerAt` | 582-605 | **Part A (A1) — the residual group `Aut_S^P` as a `Subgroup`.** Carrier the `P`-preserving automorphisms fixing `S` pointwise (`ResidualAut`); closure via `ResidualAut.mul`. The group object underlying the stabilizer chain. | Definition |
| `mem_stabilizerAt` | 607-608 | Membership: `π ∈ StabilizerAt adj P S ↔ ResidualAut adj P S π` (`Iff.rfl`). | `@[simp]` |
| `stabilizerAt_smul` | 610-612 | The subgroup action is permutation application: `g • v = ↑g v`. | `@[simp]` |
| `mem_stabilizerAt_empty` | 614-620 | **Root = ambient `P`-preserving group.** `StabilizerAt adj P ∅` is exactly the `P`-preserving automorphisms (`FixesPointwise ∅` vacuous). | — |
| `stabilizerAt_mono` | 622-628 | **Stabilizer containment.** `S ⊆ S' → StabilizerAt adj P S' ≤ StabilizerAt adj P S` (fixing more gives a smaller group; subgroup form of `OrbitPartition.mono`). | — |
| `stabilizerAt_eq_bot_iff_isBase` | 630-644 | **`StabilizerAt = ⊥ ⟺ base.** The residual is trivial exactly when `S` is a base (`IsBase`). | — |
| `mem_orbit_stabilizerAt_iff` | 646-657 | **Per-node orbit bridge.** `MulAction.orbit (StabilizerAt adj P S) v` is exactly the `OrbitPartition` relation at `S` (generalizes Group.lean's root bridge off `S = ∅`). | — |
| `residualAut_mem_stabilizerAt` | 679-682 | **(A2) Fold-in entry.** A verified `P`-preserving path-fixing automorphism is a member of `StabilizerAt adj P S`. | — |
| `closure_le_stabilizerAt` | 684-691 | **(A2) The harvested chain stays inside the true residual.** If every harvested generator is a verified path-fixing automorphism, `Subgroup.closure gens ≤ StabilizerAt adj P S` — the over-split-sound contract, group side. | — |
| `orbit_pathFixing_sound` | 693-702 | **(A2) Consumption soundness.** For `H ≤ StabilizerAt adj P S`, `v ∈ orbit H w ⟹ OrbitPartition adj P S w v` — pruning via the chain's orbits is sound. | — |
| `covered_sound` | 704-712 | **(A2) Covered ⟹ sound prune (capstone).** A candidate in the orbit (under verified path-fixing harvested gens) of an explored rep is genuinely `Aut_S^P`-equivalent to it — `CoveredByPathFixingAut` soundness. | — |
| `card_stabilizerAt_pos` | 731-733 | **(A3)** The residual group is finite, so `0 < Nat.card (StabilizerAt adj P S)`. | — |
| `card_stabilizerAt_eq_one_iff_isBase` | 735-740 | **(A3) The rigid verdict.** `Nat.card (StabilizerAt adj P S) = 1 ↔ IsBase adj P S` — residual trivial ⟺ rigid; its negation is the non-rigid/Tier-2-like side (the C# `Tier2Like`/`IrBlindSpot` flag diagnostic). | — |
| `subgroupOf_insert_eq_stabilizer` | 742-755 | **(A3) Chain carrier match.** Inside `Aut_S^P`, the point-stabilizer of `b` is exactly `Aut_{insert b S}^P`. | — |
| `card_stabilizer_eq` | 757-764 | **(A3)** The point-stabilizer inside `Aut_S^P` has the same order as `Aut_{insert b S}^P` (via `subgroupOfEquivOfLe`). | — |
| `card_stabilizerAt_eq_orbit_mul` | 766-775 | **(A3) The order recursion.** `|Aut_S^P| = |orbit of b| · |Aut_{insert b S}^P|` — the inductive step of `order = ∏ basic-orbit sizes`, via `Subgroup.card_mul_index` + `index_stabilizer`. | — |
| `orbitSizeProd` | 786-792 | **(A3.5)** The basic-orbit-size product along an ordered base sequence `bs` from `S`: each `b` contributes `|orbit b under Aut_S^P|`, then the residual descends to `Aut_{insert b S}^P`. The right-hand side of `order = ∏ basic-orbit sizes`. | Definition, `noncomputable` |
| `card_stabilizerAt_eq_prod` | 794-806 | **(A3.5) The telescoping order identity.** For any sequence `bs`, `|Aut_S^P| = orbitSizeProd bs S · |Aut_(accumulated)^P|` — induction on `bs` over `card_stabilizerAt_eq_orbit_mul`; no computable BSGS. | — |
| `card_stabilizerAt_eq_prod_of_base` | 808-815 | **(A3.5) `order = ∏ basic-orbit sizes` at a base.** When `bs.foldl … S` is a base the trailing residual is trivial, so `|Aut_S^P|` is exactly the orbit-size product — the abstract `Order = ∏ OrbitSize` of `PermutationGroup.cs`, no computable BSGS. | — |
| `card_autP_eq_prod_of_base` | 817-824 | **(A3.5) `Aut(G)^P` order as a byproduct.** The `S = ∅` headline: `StabilizerAt adj P ∅` is the whole `P`-preserving Aut group, so a base sequence from `∅` reads off `|Aut(G)^P|` as the orbit-size product (strategy §6, the chain). | — |
| `gensAt` | 846-851 | **(A2-complete) Path-fixing generators at `S`.** The subset `{g ∈ gens | g ∈ StabilizerAt adj P S}` — generators fixing the committed path. Strong-generation realizes each level's orbit from *these*, not the full `closure gens` (the distinction that makes the witness non-circular). | Definition |
| `gensAt_anti` | 853-857 | **(A2-complete)** Path-fixing generators shrink as the path grows: `S ⊆ S' → gensAt … S' ⊆ gensAt … S` (via `stabilizerAt_mono`). | — |
| `closure_gensAt_le_stabilizerAt` | 859-862 | **(A2-complete)** Soundness, intrinsic to `gensAt`: `Subgroup.closure (gensAt adj P gens S) ≤ StabilizerAt adj P S`. | — |
| `closure_gensAt_anti` | 864-868 | **(A2-complete)** Monotonicity of the path-fixing closure: `S ⊆ S' → closure (gensAt … S') ≤ closure (gensAt … S)` — the step that makes the completeness induction descend the base. | — |
| `gensAt_empty_eq` | 870-874 | **(A2-complete)** At the empty path the path-fixing condition is vacuous: `gensAt adj P gens ∅ = gens` once every generator is a `P`-preserving automorphism. | — |
| `stabilizerAt_le_closure_gensAt_step` | 876-906 | **(A2-complete) The one-level completeness core (strong-generation step).** If the path-fixing closure at the next level contains `StabilizerAt (insert b S)` and the path-fixing closure at `S` realizes the full `Aut_S^P`-orbit of `b`, then it contains `StabilizerAt adj P S`. The dual of `closure_le_stabilizerAt`; the `closure_gensAt_anti` descent is where the path-fixing form is essential. | — |
| `CoversOrbits` | 908-920 | **(A2-complete) The harvest's strong-generating-set witness.** Recursive over a base sequence: at each head the *path-fixing* closure `closure (gensAt … S)` realizes the current residual orbit of the base point, recursing to a base at the tail. Genuinely stronger than "`gens` generate the top group" (non-circular); the honest analog of the within-cell depth witness, supplied by the per-level path-fixing harvest. | Definition |
| `coversOrbits_realize_of_mem` | 922-931 | **(A2-complete) Coverage step from path-fixing realizers (the harvest interface).** If the path-fixing *generators* `gensAt … S` themselves realize `b`'s orbit, the coverage clause holds (via `Subgroup.subset_closure`). The hook concrete gauge-generator work (CFI/schemes) plugs into. | — |
| `coversOrbits_isBase_foldl` | 933-939 | **(A2-complete)** The terminal accumulated set `bs.foldl insert S` of a coverage witness is a base (matches A3.5's `foldl`). | — |
| `stabilizerAt_le_closure_gensAt_of_coversOrbits` | 941-949 | **(A2-complete) Harvest completeness (`≤`).** A coverage witness gives `StabilizerAt adj P S ≤ Subgroup.closure (gensAt adj P gens S)` — iterates `stabilizerAt_le_closure_gensAt_step` down the base. The dual of `closure_le_stabilizerAt`. | — |
| `stabilizerAt_eq_closure_gensAt_of_coversOrbits` | 951-957 | **(A2-complete) Harvest completeness (equality).** Soundness (`closure_gensAt_le_stabilizerAt`) + coverage give `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` — the path-fixing closure is *exactly* the residual. No separate soundness hypothesis. | — |
| `closure_eq_stabilizerAt_empty_of_coversOrbits` | 959-968 | **(A2-complete) Completeness at the root — the harvested chain *is* `Aut(G)^P`.** At `S = ∅`, coverage + soundness give `Subgroup.closure gens = StabilizerAt adj P ∅`. Closes the cross-branch harvest the way A2 closed soundness. | — |
| `card_closure_gensAt_eq_prod_of_coversOrbits` | 970-978 | **(A2-complete) Capstone — the chain reproduces the residual order.** With A3.5, coverage gives `Nat.card (Subgroup.closure (gensAt adj P gens S)) = orbitSizeProd adj P bs S` (= `∏ basic-orbit sizes`): the folded path-fixing generators recover both the residual group and its order. | — |
| `residualInvolutive_mono` | 1002-1008 | **(A2-complete, de-classed) `ResidualInvolutive` inherited down the descent.** `ResidualInvolutive S → S ⊆ S' → ResidualInvolutive S'` — a subgroup of an exponent-2 group has exponent ≤ 2; the involutive analogue of `residualAbelian_mono`, letting the de-classed coverage carry its hypothesis down the base sequence. | — |
| `coversOrbits_of_realizers` | 1010-1035 | **(A2-complete, de-classed — general/non-abelian) `CoversOrbits` from per-level path-fixing realizers.** If at every level `T ⊇ S` the harvested `gens` contains a residual-at-`T` realizer for each orbit-mate of each base point (`g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w`), and `bs` ends at a base, then `CoversOrbits adj P gens bs S`. **No group-structure hypothesis** — abelian *or* non-abelian (schemes, Cameron) — the honest "covers everything, no class ladder" coverage core; `coversOrbits_of_residualInvolutive` is its exponent-2 corollary. | — |
| `coversOrbits_of_visibleRealizers` | 1037-1054 | **(A2-complete, de-classed — harvest-facing) `CoversOrbits` from realizers keyed on the refinement-visible cell relation.** Same as `coversOrbits_of_realizers` but the realizer hypothesis ranges over same-`warmRefine`-cell pairs (polynomially computable) rather than `OrbitPartition` pairs (orbits refine cells, so it covers a fortiori). The shape the structural (scheme/recovery) harvest supplies: at a recoverable node cells *are* orbits, so visible cell-mates = orbit-mates. | — |
| `closure_eq_stabilizerAt_of_realizers` | 1056-1068 | **(A2-complete, de-classed — general) Harvest completeness from realizers.** `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` from per-level path-fixing realizers (`coversOrbits_of_realizers` + `stabilizerAt_eq_closure_gensAt_of_coversOrbits`). The general (non-exponent-2) analogue of `closure_eq_stabilizerAt_of_residualInvolutive`: the cross-branch harvest reproduces the residual group (and order, via A3.5) for the whole recoverable class, no group-structure hypothesis. | — |
| `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` | 1070-1088 | **(A2-complete, localisation core) Recovery makes the harvest refinement-decidable.** At a node `T` with `CellsAreOrbits`, the refinement-visible realizer hypothesis (same-`warmRefine`-cell pairs, computable) is *equivalent* to the orbit realizer hypothesis (`OrbitPartition` pairs). `→` free (`subset_warmRefine`), `←` uses recovery. Pins localisation as the **polynomiality layer**: coverage correctness holds from orbit realizers unconditionally (`coversOrbits_of_realizers`); recovery makes the equivalent target refinement-computable. Per-level recovery down the base sequence is the substrate-conditional remainder. | — |
| `coversOrbits_of_residualInvolutive` | 1090-1108 | **(A2-complete) De-classed coverage — `CoversOrbits` from an exponent-2 residual.** If the residual is involutive (`ResidualInvolutive`) and `gens` contains every involutive residual automorphism (what the leaf-collision harvest supplies), `CoversOrbits adj P gens bs S` holds. **Now a corollary of `coversOrbits_of_realizers`** (the general non-abelian form): `orbitPartition_swap_of_involutive` supplies the involution realizer for each orbit-mate. Discharges the coverage witness for the whole elementary-abelian-residual class in one theorem — no per-class `Aut(CFI)≅Z₂^β⋊Aut(H)` structure theorem. | — |
| `closure_eq_stabilizerAt_of_residualInvolutive` | 1110-1124 | **(A2-complete) De-classed harvest completeness — the involutive residual *is* the closure of harvested involutions.** At an exponent-2 node, `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S` (via `coversOrbits_of_residualInvolutive` + `stabilizerAt_eq_closure_gensAt_of_coversOrbits`). The cross-branch completeness for every elementary-abelian-residual class with no per-class structure theorem — the cross-branch analogue of `theorem_2_HOR_of_pPolynomial`; CFI's gauge regime is a witness supplying only `ResidualInvolutive` at a gauge-regime `S`. | — |
| `cfiFlipAut_residualAut` | 1140-1151 | **(A2-complete / CFI-cov.1) Gauge flip is a path-fixing residual aut.** A symmetric, even gauge flip `cfiFlipAut F` that is `F`-free on `S`'s gadgets is a `ResidualAut adj P S` (assembles `isAut_cfiFlipAut` + `cfiFlipAut_preserves_P` + locality). The bridge from the `CFI.lean` gauge-flip layer to the A2-complete residual vocabulary. | — |
| `cfiFlipAut_mem_stabilizerAt` | 1153-1159 | **(CFI-cov.1)** A path-fixing gauge flip is an element of the residual group `StabilizerAt adj P S`. | — |
| `cfiFlipAut_orbitPartition` | 1161-1169 | **(CFI-cov.1) Forward coverage.** A path-fixing gauge flip moves `v` within its `Aut_S^P`-orbit: `OrbitPartition adj P S v (cfiFlipAut F v)`. (Reverse — realizing the *full* orbit — is the staged cycle-space content.) | — |
| `cfiGaugeGens` | 1171-1177 | **(CFI-cov.1) The CFI gauge generating set.** All symmetric, even gauge flips `cfiFlipAut F` — the cycle-space `Z₂^β` generators the harvest folds in; `Subgroup.closure (cfiGaugeGens h)` is the gauge group. | Definition |
| `cfiGaugeGens_residualAut_empty` | 1179-1186 | **(CFI-cov.1) Root soundness.** Every gauge flip is a `P`-preserving automorphism (`ResidualAut adj P ∅`) — the Stage-A2 soundness hypothesis `closure_eq_stabilizerAt_empty_of_coversOrbits` consumes. | — |
| `cfiFlipAut_mem_gensAt` | 1188-1196 | **(CFI-cov.1)** A path-fixing gauge flip lies in the path-fixing generators `gensAt adj P (cfiGaugeGens h) S` — gauge generator + member of `StabilizerAt adj P S`. The hook the coverage discharge (CFI-cov.3) uses to realize orbits. | — |
| `isBase_of_discrete_warmRefine` | 1205-1211 | **(CFI-cov.2) Discreteness ⟹ base.** If `warmRefine adj P (individualizedColouring n S)` is discrete then `S` is a base — the orbit partition collapses to equality (`orbit_iff_eq_of_discrete_warmRefine`). The general bridge from cascade `Discrete` output to the `IsBase` terminal of `CoversOrbits`. | — |
| `foldl_insert_eq_union` | 1213-1219 | **(CFI-cov.2)** Folding `insert` over a list from `s` accumulates its elements: `l.foldl (insert) s = s ∪ l.toFinset`. | — |
| `foldl_insert_empty_eq_toFinset` | 1221-1224 | **(CFI-cov.2)** Folding `insert` over a list from `∅` rebuilds its underlying finset (`= l.toFinset`) — matches `CoversOrbits`/A3.5's `foldl`. | — |
| `cfi_exists_base_seq` | 1226-1235 | **(CFI-cov.2) CFI base sequence (odd-degree).** From the axiom-free cascade discreteness (`theorem_1_HOR_cfi_oddDeg`), an odd-degree CFI graph has an ordered base sequence `bs` with `bs.foldl insert ∅` a base — the `IsBase` terminal a `CoversOrbits` witness for CFI requires. | — |
| `gaugeSubgroup` | 1253-1277 | **(CFI-cov.3, de-classed) The CFI gauge group `Z₂^β` as a `Subgroup`.** `cfiGaugeGens h` is closed under the group ops (`cfiFlipAut_xorF` for `*`, `cfiFlipAut_one` for `1`, `cfiFlipAut_involutive` for inverses), so it forms a subgroup, not merely a generating set. | Definition |
| `mem_gaugeSubgroup` | 1279-1280 | **(CFI-cov.3)** Membership in `gaugeSubgroup h` is exactly membership in `cfiGaugeGens h` (`Iff.rfl`). | `@[simp]` |
| `closure_cfiGaugeGens_eq` | 1282-1286 | **(CFI-cov.3)** The closure of the gauge generators *is* the gauge subgroup — they already form a subgroup: `Subgroup.closure (cfiGaugeGens h) = gaugeSubgroup h`. | — |
| `cfiGauge_mul_self` | 1288-1295 | **(CFI-cov.3) The gauge group is exponent-2 (elementary-abelian).** Every gauge generator is a flip `cfiFlipAut F` and flips are involutions (`cfiFlipAut_involutive`), so `g * g = 1` — the exponent-2 input `coversOrbits_of_residualInvolutive` needs, supplied for the gauge group. | — |
| `cfi_coversOrbits` | 1297-1316 | **(CFI-cov.3) The CFI coverage witness, via de-classing (no structure theorem).** From **gauge-generation** `StabilizerAt adj P ∅ ≤ closure (cfiGaugeGens h)` (`hgen`) and odd degree, the gauge flips cover every level's residual orbit: `∃ bs, CoversOrbits adj P (cfiGaugeGens h) bs ∅`. Obtained from `coversOrbits_of_residualInvolutive` (gauge-generation ⟹ exponent-2 residual + `hgens`), with **no** `Φ(σ)` lift or semidirect decomposition. The long-sought `cfi_coversOrbits`, reduced to the single `hgen`. | — |
| `cfi_closure_eq_stabilizerAt` | 1318-1329 | **(CFI-cov.3) CFI cross-branch harvest completeness.** With gauge-generation, the harvested gauge chain *is* the residual: `Subgroup.closure (cfiGaugeGens h) = StabilizerAt adj P ∅` (`≤` free via `cfiGaugeGens_residualAut_empty`, `≥` is `hgen`). | — |
| `cfi_card_stabilizerAt_eq_prod` | 1331-1346 | **(CFI-cov.3) `|Aut(CFI(H))^P| = ∏ basic-orbit sizes`, via the gauge chain.** With gauge-generation, `∃ bs, Nat.card (StabilizerAt adj P ∅) = orbitSizeProd adj P bs ∅` — the `Order = ∏ OrbitSize` of `PermutationGroup.cs` for CFI, computed from the folded gauge generators. The genuine de-classed payoff (needs the full `cfi_coversOrbits` chain, not just the two containments). | — |
| `gadgetOf` | 1365-1366 | **(CFI-cov.4)** The gadget (base vertex) of a CFI vertex `x : Fin n`, through the CFI labelling: `h.H.gadget (h.e x) : Fin h.m`. | Definition |
| `PSeparatesGadgets` | 1368-1373 | **(CFI-cov.4) The honest "base layer resolved" hypothesis.** `P` separates gadgets at `S`: vertices with the same `P`-relations to every committed `s ∈ S` share a gadget. The premise that makes a residual automorphism (which preserves those relations) fix gadgets — encoding the decomposability regime where the `Aut(H)` factor is killed. | Definition |
| `gadgetPreserving_of_pSeparates` | 1375-1388 | **(CFI-cov.4, Lemma A) Gadget-preservation from `P`-separation.** A residual automorphism `g` fixes `S` pointwise and preserves `P`, so `P (g x) s = P (g x)(g s) = P x s` for `s ∈ S`; under `PSeparatesGadgets` this forces `gadgetOf (g x) = gadgetOf x`. Replaces the subtle structural "CFI automorphisms preserve gadgets" with an honest `P`-hypothesis — the key reduction of the gauge-nut discharge. | — |
| `gadgetOf_subsetVertex` | 1396-1399 | **(CFI-cov.4 Lemma B)** `gadgetOf h (subsetVertex hS@v) = v`. | `@[simp]` |
| `gadgetOf_endpointVertex` | 1401-1404 | **(CFI-cov.4 Lemma B)** `gadgetOf h (endpointVertex hw b@v) = v`. | `@[simp]` |
| `exists_vertex_form` | 1406-1415 | **(CFI-cov.4 Lemma B) Vertex destructor.** Every `x : Fin n` is a subset vertex `subsetVertex hS` or an endpoint vertex `endpointVertex hw b` of the CFI graph (via `h.e x` and the bijection round-trips). | — |
| `endpointVertex_bool_inj` | 1417-1424 | **(CFI-cov.4 Lemma B)** Endpoints at the same gadget/direction are equal only for equal parity: `endpointVertex hw b₁ = endpointVertex hw b₂ → b₁ = b₂`. | — |
| `endpointVertex_inj` | 1426-1434 | **(CFI-cov.4 Lemma B)** Endpoints at gadget `v` are equal only for equal direction and parity: `endpointVertex hw₁ b₁ = endpointVertex hw₂ b₂ → w₁ = w₂ ∧ b₁ = b₂`. | — |
| `subset_mem_iff_adj` | 1436-1448 | **(CFI-cov.4 Lemma B) A subset vertex's membership is its adjacency to the `b=false` endpoints:** `e^0_{v→w} ~ a_S^v ↔ w ∈ S`. Lets `g²` (fixing endpoints) pin a subset vertex. | — |
| `isEndpt` | 1450-1453 | **(CFI-cov.4 Lemma B)** Has a cross-gadget neighbour — the structural distinguisher of endpoint vs subset vertices (`∃ y, adj x y = 1 ∧ gadgetOf y ≠ gadgetOf x`). | Definition |
| `isEndpt_endpointVertex` | 1455-1462 | **(CFI-cov.4 Lemma B)** An endpoint vertex has a cross-gadget neighbour (its bridge partner, in gadget `w ≠ v`). | — |
| `not_isEndpt_subsetVertex` | 1464-1471 | **(CFI-cov.4 Lemma B)** A subset vertex has no cross-gadget neighbour (all neighbours are endpoints at its gadget). | — |
| `isEndpt_equivariant` | 1473-1484 | **(CFI-cov.4 Lemma B)** `isEndpt` is automorphism-invariant for a gadget-fixing automorphism: `isEndpt h (g x) ↔ isEndpt h x` (substitute `y = g z`). | — |
| `gadgetFixingAut_endpoint` | 1486-1501 | **(CFI-cov.4 Lemma B, B1) Type preservation (endpoints).** A gadget-fixing automorphism maps an endpoint vertex to an endpoint vertex at the same gadget. | — |
| `gadgetFixingAut_subset` | 1503-1518 | **(CFI-cov.4 Lemma B, B1) Type preservation (subsets).** A gadget-fixing automorphism maps a subset vertex to a subset vertex at the same gadget. | — |
| `gadgetFixingAut_dir` | 1520-1536 | **(CFI-cov.4 Lemma B, B2) Direction preservation.** A gadget-fixing automorphism maps `e^b_{v→w}` to `e^{b'}_{v→w}` (bridge target `w` preserved); only the parity may change. | — |
| `mulSelf_endpoint` | 1538-1556 | **(CFI-cov.4 Lemma B, B2) `g²` fixes endpoints.** A gadget-fixing automorphism maps the parity pair `{e^0_{v→w}, e^1_{v→w}}` into itself; injective on a 2-set ⟹ squares to identity there. | — |
| `mulSelf_subset` | 1558-1587 | **(CFI-cov.4 Lemma B, B3) `g²` fixes subsets.** `g²` preserves adjacency and fixes endpoints, so a subset vertex and its `g²`-image have identical endpoint-adjacencies; a subset is determined by them, so `g²` fixes it. | — |
| `cfiAut_gadgetFixing_mul_self` | 1589-1600 | **(CFI-cov.4 Lemma B) A gadget-fixing CFI automorphism is an involution.** `IsAut g adj` + gadget-preservation ⟹ `g * g = 1` (every vertex is subset (B3) or endpoint (B2), both fixed by `g²`). The medium-risk core of the gauge-nut discharge. | — |
| `cfi_residualInvolutive` | 1602-1611 | **(CFI-cov.4 capstone, Lemma A + Lemma B) `ResidualInvolutive` for CFI in the base-resolved regime.** Where `P` separates gadgets (`PSeparatesGadgets`), every residual automorphism fixes gadgets (Lemma A) and is an involution (Lemma B), so the residual is exponent-2 — the CFI witness `coversOrbits_of_residualInvolutive` consumes, with no structure theorem / `Φ(σ)` lift. | — |
| `isBase_mono` | 1621-1627 | **(CFI-cov.4 harvest)** `IsBase` is upward-closed: `IsBase adj P S → S ⊆ T → IsBase adj P T` (individualizing more shrinks the residual; via `stabilizerAt_mono`). | — |
| `cfi_exists_base_seq_from` | 1629-1641 | **(CFI-cov.4 harvest) A base sequence from any `S`.** For an odd-degree CFI graph, `(allSeeds \ S).toList` is a base sequence from `S`: the cascade gives `IsBase allSeeds` (`theorem_1_HOR_cfi_oddDeg`) and `isBase_mono` lifts it to the superset. Generalizes `cfi_exists_base_seq` (`S = ∅`). | — |
| `cfi_closure_eq_stabilizerAt_of_pSeparates` | 1643-1658 | **(CFI-cov.4 harvest) Cross-branch harvest completeness, base-resolved regime.** Where `P` separates gadgets at `S`, `Subgroup.closure {g | ResidualAut adj P S g ∧ g²=1} = StabilizerAt adj P S` — the harvested involutive residual automorphisms generate the residual. Via `cfi_residualInvolutive` + `closure_eq_stabilizerAt_of_residualInvolutive` over `cfi_exists_base_seq_from`; no structure theorem / `Φ(σ)` lift. | — |
| `cfi_card_stabilizerAt_of_pSeparates` | 1660-1672 | **(CFI-cov.4 harvest) `|Aut_S^P| = ∏ basic-orbit sizes`, base-resolved regime.** Where `P` separates gadgets at `S`, `∃ bs, Nat.card (StabilizerAt adj P S) = orbitSizeProd adj P bs S` — the gauge-layer `Order = ∏ OrbitSize` from the folded involutive generators. The de-classed payoff (needs the full coverage chain). | — |
| `VisiblyRecoverable` | 1695-1711 | **D1 (explicit-chain form).** A single-vertex, per-step symmetry-only chain from `S₀` reaching `CellsAreOrbits` within a depth bound — the unconditional/cascade leg's structural witness, retained alongside the inductive `Findable`. | Definition |
| `recoverableByDepth_of_visiblyRecoverable` | 1713-1718 | **D1 leg (free).** `VisiblyRecoverable ⟹ RecoverableByDepth` — the chain ends on a `CellsAreOrbits` set within the bound. | — |
| `visiblyRecoverable_bound_mono` | 1720-1724 | `VisiblyRecoverable` is monotone in the depth bound (a looser bound is easier). | — |
| `cellsAreOrbits_empty_of_schurian` | 1726-1739 | **Schurian scheme graphs are vertex-transitive: `CellsAreOrbits adj P ∅`.** The `Aut`-orbit relation at `∅` is total (witness from `schurian_transitive` at the diagonal `R₀`), unblocking the symmetry-only first step. | — |
| `visiblyRecoverable_of_cellsAreOrbits_singleton` | 1741-1754 | **`CellsAreOrbits` at a singleton + vertex-transitivity ⟹ D1 at depth 1.** The one-step chain `∅ → {v}` is symmetry-only with `CellsAreOrbits {v}` as endpoint recovery. | — |
| `visiblyRecoverable_scheme` | 1756-1766 | **D1 instance — rank-2, `|J|=1` schurian scheme is visibly recoverable.** Validates `VisiblyRecoverable` against the proved depth-1 scheme orbit recovery (`orbitRecoverable_scheme`). | — |
| `SymmetryOnlyStep` | 1770-1783 | **D1 per-decision primitive (§6.10).** Individualizing `v` commits no real decision: `v`'s 1-WL cell is non-singleton and a single `Aut_S`-orbit. The non-singleton conjunct is load-bearing (forces `v ∉ S`); lifted out of `VisiblyRecoverable`. | Definition |
| `symmetryOnlyStep_of_cellsAreOrbits` | 1785-1795 | `CellsAreOrbits` upgrades any non-singleton cell to a `SymmetryOnlyStep` — the bridge from the recovery predicate to the screen primitive, and why `Discrete` (not bare `CellsAreOrbits`) is a non-false-walling stop (§6.11 F1). | — |
| `symmetryOnlyStep_empty_scheme` | 1797-1818 | **Scheme validation of the primitive.** A vertex-transitive schurian scheme is one orbit at `∅`, so individualizing any `v` (with `n ≥ 2`) is a `SymmetryOnlyStep`. | — |
| `Findable` | 1837-1849 | **The harvest-window screen (sequential D1/D2, §6.10+§6.11).** Least-fixed-point inductive: `recovered` (`Discrete` — the F1-correct stop), `abelian` (`ResidualAbelian ∧ ¬IsBase` — guarded D2), `step` (`SymmetryOnlyStep` + recurse). Bound-free classification; `¬Findable` is the seal's wall (IR-blind-spot / Cameron by residual order). | Inductive |
| `FindableWithin` | 1860-1878 | **`Findable` with its recovery depth (Phase 0).** Bound-indexed companion: `recovered`→`b=S.card`, `step` propagates `b`, `abelian` carries `RecoverableByDepth adj P b` as a field (the D2-bridge interface). De-vacuates the `∃ b` conclusion (`recoverableByDepth_univ`). | Inductive |
| `recoverableByDepth_of_findableWithin` | 1880-1890 | **Screen soundness — non-vacuous.** `FindableWithin adj P S b ⟹ RecoverableByDepth adj P b` at the carried bound: `recovered`/`step` free, `abelian` returns its carried recoverability field. | — |
| `findable_of_findableWithin` | 1892-1901 | Forgetting the bound (and the abelian recoverability witness) collapses `FindableWithin` to the bound-free `Findable` classification; the reverse needs the D2 bridge, so `FindableWithin` is strictly stronger. | — |
| `findableWithin_cfi_gauge` | 1929-1939 | **D2-bridge anchor (CFI gauge).** For an odd-degree CFI graph, a hidden non-trivial abelian residual (`ResidualAbelian ∧ ¬ IsBase`, the screen's D2 predicate) discharges `FindableWithin` at `cfi_depth_bound h` via the axiom-free `recoverableByDepth_cfi` — the D2 analogue of `visiblyRecoverable_scheme`. | — |
| `recoverableByDepth_of_cfi_gauge` | 1941-1949 | **The CFI gauge is `RecoverableByDepth`.** Bound-carrying soundness applied to `findableWithin_cfi_gauge`: a hidden non-trivial abelian CFI residual recovers by depth `cfi_depth_bound h`, routed through the screen so the D2 leg is certified non-vacuous end-to-end. | — |
| `findable_cfi_gauge` | 1951-1959 | **The CFI gauge is `Findable`** (bound-free classification): a hidden non-trivial abelian CFI residual lands in the screen's D2 leg — the abelian disjunct populated by the central recoverable, non-Cameron example. | — |
| `soStep` | 1979-1983 | Leg A — one round of the symmetry-only closure: individualize a symmetry-only vertex if one exists, else stay put. Extensive; strictly grows until no symmetry-only step remains. | Definition, `noncomputable` |
| `soStep_extensive` | 1985-1989 | The symmetry-only closure round is extensive — it only ever adds the chosen vertex. | — |
| `symmetryOnlyStep_not_mem` | 1991-2000 | A symmetry-only step's vertex is not yet committed (`v ∉ S`): a committed vertex is a warm-refinement-preserved singleton, so its cell could not be non-singleton. This is what makes `soStep` strictly grow until stuck. | — |
| `soStep_pos` | 2002-2005 | When a symmetry-only step exists, the closure round takes it (inserts the chosen vertex). | — |
| `exists_symmetryOnly_saturated` | 2007-2024 | **Leg A — bounded termination of the symmetry-only process.** Iterating the symmetry-only closure from any `S₀` reaches a saturated node `S* ⊇ S₀` with no symmetry-only step available, within `≤ n − |S₀|` rounds — the engine-powered, class-agnostic half of the harvest-window trichotomy's termination. | — |
| `MovedAt` | 2035-2040 | Leg A — a vertex moved by some residual automorphism at `S`; weaker than a symmetry-only step (its cell may be coarser than its orbit), so the right object for the general support induction. | Definition |
| `movedAt_not_mem` | 2042-2044 | A moved vertex is not committed (`v ∉ S`), since a residual automorphism fixes `S` pointwise. | — |
| `isBase_of_no_moved` | 2046-2056 | A node with no moved vertex is a base (trivial residual). | — |
| `movedStep` | 2057-2061 | Leg A — one round of the moved-vertex closure: individualize a moved vertex if one exists, else stay. Extensive; strictly grows until the residual is trivial (a base). | Definition, `noncomputable` |
| `movedStep_extensive` | 2063-2066 | The moved-vertex closure round is extensive. | — |
| `movedStep_pos` | 2068-2070 | When a moved vertex exists, the closure round takes it. | — |
| `exists_isBase_saturated` | 2072-2089 | **Leg A — the general support induction (every graph reaches a base).** Individualizing moved vertices from any `S₀` reaches a base `S* ⊇ S₀` (trivial residual) within `≤ n − |S₀|` rounds, via the `Saturation` engine — holding for every graph (CFI, schemes, rigid alike). | — |
| `MovedAt.anti` | 2102-2111 | **Moved-set anti-monotonicity.** A residual automorphism fixing `S` also fixes any `S₀ ⊆ S`, so a vertex moved at `S` is already moved at `S₀` — the moved-set shrinks as the individualized set grows, which makes it a saturation bound. | — |
| `movedSet` | 2112-2117 | **The residual support at `S₀`:** the vertices moved by some residual automorphism fixing `S₀` (the support of `Aut_{S₀}^P`). Disjoint from `S₀`; its cardinality is the harvest-window depth `|support(g)|`. | Definition, `noncomputable` |
| `mem_movedSet` | 2119-2121 | Membership in `movedSet`: `v ∈ movedSet adj P S₀ ↔ MovedAt adj P S₀ v`. | — |
| `movedStep_subset_bound` | 2123-2136 | Interval invariance of the support bound: on every `f`-reachable set `S₀ ⊆ s ⊆ S₀ ∪ movedSet`, `movedStep` stays inside `S₀ ∪ movedSet` — the hypothesis feeding the interval-invariant saturation engine. | — |
| `exists_isBase_saturated_support` | 2138-2161 | **Leg A — the tight support bound (`base(g) ≤ |support|`).** Sharpens `exists_isBase_saturated`: the moved-vertex closure reaches a base within `≤ |movedSet adj P S₀|` rounds — the residual support, not the full `n`. | — |
| `forcedNode` | 2181-2186 | **The canonical forced node:** `S₀ ∪ movedSet adj P S₀`, individualizing the whole residual support at once. Choice-free — the deterministic, iso-invariant counterpart of the `Classical.choice`-driven `movedStep` saturation. | Definition, `noncomputable` |
| `forcedNode_isBase` | 2188-2198 | **The forced node is a base — choice-free.** Individualizing the full residual support trivializes the residual group, so `forcedNode adj P S₀` is a base with no `Classical.choice`. | — |
| `movedAt_image` | 2200-2225 | **Automorphism-equivariance of `MovedAt`** (one direction). A `P`-preserving automorphism `g` carries a vertex moved at `S₀` to one moved at `S₀.image g`, via the conjugate `g π g⁻¹`. | — |
| `movedAt_image_iff` | 2227-2239 | **Automorphism-equivariance of `MovedAt`** (iff form): `MovedAt adj P (S₀.image g) (g v) ↔ MovedAt adj P S₀ v` for a `P`-preserving automorphism `g`. | — |
| `movedSet_image` | 2241-2257 | The residual support commutes with automorphisms: `movedSet adj P (S₀.image g) = (movedSet adj P S₀).image g`. | — |
| `forcedNode_image` | 2259-2266 | **The forced node is automorphism-equivariant (iso-invariance).** `forcedNode` commutes with every `P`-preserving automorphism — a canonical function of iso-invariant data, not an arbitrary `Classical.choice`. | — |
| `forcedNode_residual_invariant` | 2268-2281 | **The forced node is fixed by the residual group it resolves.** Every residual automorphism at `S₀` maps `forcedNode adj P S₀` to itself setwise. | — |
| `recoverableAt_base_iff_discrete` | 2295-2306 | **Recovery at a base ⟺ discreteness.** At a base `S`, `OrbitRecoverableAt adj P S` holds iff `warmRefine` is `Discrete` — separating the (consumed) symmetry axis from the sole remaining IR-stickiness axis. | — |
| `forcedNode_recoverable_iff_discrete` | 2308-2317 | **Tying the two axes at the canonical node.** At `forcedNode` (a base), orbit recovery is exactly discreteness of `warmRefine`: symmetry consumed plus no IR-stickiness ⟺ recovery. | — |
| `mem_movedSet_iff_nonsingleton_cell_of_recoverable` | 2326-2343 | **The support is the non-singleton cells, at a recoverable node.** Where `OrbitRecoverableAt adj P S`, a vertex is moved iff it shares its 1-WL cell with another — so refinement computes `movedSet`/`forcedNode`. | — |
| `movedSet_eq_nonsingletonCells_of_recoverable` | 2344-2355 | `movedSet` is refinement-computed at a recoverable node (Finset form): it equals the union of the non-singleton 1-WL cells. | — |
| `relabelAdj` | 2366-2368 | **Relabel a graph by `σ`:** the adjacency where `σ v` plays the role `v` did. `σ` is the canonical graph isomorphism `adj → relabelAdj σ adj`. | Definition |
| `relabelAdj_adj` | 2370-2371 | Unfolding lemma: `(relabelAdj σ A).adj i j = A.adj (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `relabelP` | 2373-2375 | **Relabel a `P`-matrix by `σ`:** `Q (σ⁻¹ ·) (σ⁻¹ ·)`. | Definition |
| `relabelP_apply` | 2377-2378 | Unfolding lemma: `relabelP σ Q i j = Q (σ.symm i) (σ.symm j)`. | `@[simp]` |
| `residualAut_relabel` | 2380-2397 | **Residual automorphisms transport along a relabelling** (forward), via the conjugate `σ π σ⁻¹`: a residual aut at `S` becomes one at `S.image σ` in the relabelled graph. | — |
| `residualAut_relabel_symm` | 2399-2416 | **Residual automorphisms transport back from a relabelling** (reverse), via `σ⁻¹ π σ`. | — |
| `movedAt_relabel_iff` | 2418-2433 | **`MovedAt` is equivariant under relabelling:** `MovedAt (relabelAdj σ adj) (relabelP σ P) (S₀.image σ) (σ v) ↔ MovedAt adj P S₀ v`. | — |
| `movedSet_relabel` | 2435-2450 | The residual support is equivariant under relabelling: `movedSet (relabel… σ) (S₀.image σ) = (movedSet adj P S₀).image σ`. | — |
| `forcedNode_relabel` | 2452-2460 | **Forced node equivariant under arbitrary relabelling — full iso-invariance.** Relabelling the input by any `σ` (not just an automorphism) maps the canonical forced node correspondingly. | — |
| `visiblyRecoverable_pPolynomial` | 2470-2482 | **D1 for every P-polynomial (metric / DRG) scheme graph.** Generalizes `visiblyRecoverable_scheme` (rank-2 / `|J|=1`) to the whole distance-regular family via the depth-1 metric recovery `theorem_2_HOR_of_pPolynomial`. | — |
| `forcedExpand` | 2492-2498 | **M-D instance — the canonical exploration rule.** For rep `r` at a node, explore `r` together with its residual support: `insert r (movedSet adj chain.P (insert r chain.D))`. Iso-invariant and automorphism-equivariant (the per-rep forced node). | Definition, `noncomputable` |
| `lockstepExpand_forcedExpand` | 2500-2518 | **M-D — the lockstep is a theorem.** `forcedExpand` satisfies `LockstepExpand` — the residual-support half is exactly `movedSet_image`, the committed prefix is fixed setwise by `g`. So `matchOracleSet (forcedExpand …)` needs no lockstep hypothesis, only the depth witness. | — |
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
