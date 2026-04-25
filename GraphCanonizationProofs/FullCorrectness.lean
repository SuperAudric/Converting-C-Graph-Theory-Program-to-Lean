import FullCorrectness.Basic
import FullCorrectness.Permutation
import FullCorrectness.Automorphism
import FullCorrectness.Isomorphic
import FullCorrectness.Equivariance.Actions
import FullCorrectness.Equivariance.StageA
import FullCorrectness.Equivariance.RankStateInvariants
import FullCorrectness.Equivariance.ComparisonSort
import FullCorrectness.Equivariance.ComparePathSegments
import FullCorrectness.Equivariance.PathEquivariance
import FullCorrectness.Equivariance.ConvergeLoop
import FullCorrectness.Tiebreak
import FullCorrectness.Invariants
import FullCorrectness.Main

/-!
# Full correctness of the graph canonizer — umbrella + proof plan

Re-exports all submodules under `FullCorrectness/`. External consumers can
`import FullCorrectness` to pull in the whole proof; internal modules import
the specific step(s) they depend on.

The flat-flawed proof in `LeanGraphCanonizerV4Correctness.lean` is retired — its header
explains why its central equivariance claim is literally false. This tree replaces it.

## Target theorem (to be proved in §8)

```
run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

"`run` with all-zero starting vertex types is a complete graph-isomorphism invariant."

## Status at a glance

| Step | Subject                                           | File                                     | Status          |
| ---- | ------------------------------------------------- | ---------------------------------------- | --------------- |
| §1   | Automorphism group, orbits, `permute` action      | `Basic`, `Permutation`, `Automorphism`   | ✅ proved       |
| §1.7 | `Fintype G.Aut` (decidability + finiteness)       | `Automorphism`                           | ✅ proved       |
| §2   | `Isomorphic ↔ ∃σ, H = G.permute σ` bridge         | `Isomorphic`                             | ✅ proved       |
| §3   | `permNat` + `PathSegment/PathsBetween/...permute` | `Equivariance.Actions`                   | ✅ defined      |
| §3A  | `initializePaths_Aut_equivariant` (Stage A)       | `Equivariance.StageA`                    | ✅ proved       |
| §3B  | `calculatePathRankings` size + `σInvariant`       | `Equivariance.RankStateInvariants`       | ✅ proved       |
| §3B  | Generic sort/`orderInsensitiveListCmp` lemmas     | `Equivariance.ComparisonSort`            | ✅ proved       |
| §3B  | `comparePathSegments_total_preorder` (Stage B)    | `Equivariance.ComparePathSegments`       | ✅ proved; `comparePathsBetween_total_preorder` ✅ proved |
| §3B  | σ-equivariance of compare/sort; Stage B assembly  | `Equivariance.PathEquivariance`          | 🧱 2 sorry (`calculatePathRankings_fromRanks_inv`, `calculatePathRankings_betweenRanks_inv`) |
| §4   | `convergeOnce`/`convergeLoop` Aut-invariance; C/D | `Equivariance.ConvergeLoop`              | ✅ proved       |
| §5   | `TypedAut G vts` (subgroup + Fintype)             | `Tiebreak`                               | ✅ defined      |
| §5.0 | `breakTie` output position-by-position            | `Tiebreak`                               | ✅ proved (4 characterization lemmas) |
| §5.1 | `breakTie` is the v*-stabilizer of `TypedAut`     | `Tiebreak`                               | ✅ proved (with `hAutInv`/`hsize`) |
| §5.2 | `breakTie` strictly shrinks `TypedAut`            | `Tiebreak`                               | ✅ proved (with `hmove`) |
| §6.0 | `breakTieAt` output + τ-equivariance              | `Tiebreak`                               | ✅ proved (3 characterization + 1 equivariance) |
| §6   | Tiebreak choice-independence (conceptual crux)    | `Tiebreak`                               | ✅ closed modulo `runFrom_VtsInvariant_eq` (the chained §3 Stages B–D for `runFrom`) |
| §7   | `IsPrefixTyping` definition + zeros instance      | `Invariants`                             | ✅ defined + boundary proved |
| §7   | `breakTie_targetPos_is_min_tied`                  | `Invariants`                             | ✅ proved (uses §5 disjunctive characterization) |
| §7   | Other prefix invariants                           | `Invariants`                             | ✅ all proved (`getFrom_image_isPrefix_for_initializePaths`, `convergeLoop_preserves_prefix`, `n_distinct_ranks`, `orderVertices_prefix_invariant`, Phase 2 breakTie step, Phase 3 convergeLoop_preserves_lower_uniqueness) |
| §8   | Assemble `run_canonical_correctness`              | `Main`                                   | 🧱 assembled, (⟹) `sorry`; (⟸) proved |

## Open obligations (4 total)

| Sorry | Location | What's needed |
| ----- | -------- | ------------- |
| `calculatePathRankings_fromRanks_inv` | `Equivariance.PathEquivariance`    | Foldl induction on the depth loop + σ-equivariance of sortBy + assignRanks at each step. |
| `calculatePathRankings_betweenRanks_inv` | `Equivariance.PathEquivariance` | Companion to the above; same induction. |
| `runFrom_VtsInvariant_eq`             | `Tiebreak`                         | §3 Stages B–D chained for the bounded `runFrom` loop. Mechanical once Stage B–D are discharged. |
| `run_isomorphic_eq` (⟹)               | `Main`                             | Assemble §3 + §4 + §6 against the σ from §2. |

**`Invariants.lean` is fully closed.** `orderVertices_prefix_invariant` and
`orderVertices_n_distinct_ranks` both proved unconditionally.

--------------------------------------------------------------------------------

## §1  Automorphism group, vertex orbits, and permutation action

**Status: proved.** Definitions and theorems live in `Basic`, `Permutation`, `Automorphism`.

### §1.1  Permutation action on `AdjMatrix` (`Permutation.lean`)

`AdjMatrix.permute σ G` relabels the vertices of `G` by `σ`, using `σ.symm` so that
composition is a left action: `G.permute (σ * τ) = (G.permute τ).permute σ`.

Proved:
- `permute_one`                  — `G.permute 1 = G`
- `permute_mul`                  — left-action composition law
- `permute_permute_symm`         — `(G.permute σ).permute σ⁻¹ = G` (round-trip)
- `permute_symm_permute`         — `(G.permute σ⁻¹).permute σ = G`

### §1.2  Bridge to `swapVertexLabels` (`Permutation.lean`)

`swapVertexLabels_eq_permute : swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2)`

Connects the inductive `Isomorphic` generator to the abstract permutation action.
`Equiv.swap v1 v2` is self-inverse (`toFun = invFun` definitionally), which is why
`.symm` reduces by `rfl` here.

### §1.3  Automorphism subgroup (`Automorphism.lean`)

`AdjMatrix.Aut G : Subgroup (Equiv.Perm (Fin n))` — permutations σ with `G.permute σ = G`.

Proved using `permute_one` / `permute_mul` / `permute_permute_symm` for the three
subgroup axioms. Also `mem_Aut_iff_adj` for the pointwise characterization.

### §1.4–§1.6  Orbits and partition (`Automorphism.lean`)

`AdjMatrix.orbit G v := { w | ∃ σ ∈ Aut G, σ v = w }`

`AdjMatrix.orbitSetoid G : Setoid (Fin n)` packages same-orbit as an equivalence relation
(reflexive via `1 ∈ Aut G`, symmetric via inverses, transitive via composition), so the
orbits partition `Fin n` by Lean's quotient infrastructure.

`orbit_stable_under_Aut` — the forward-facing form: `σ ∈ Aut G → σ v ∈ G.orbit v`.

--------------------------------------------------------------------------------

## §2  Bridge lemma: `Isomorphic ↔ ∃ σ, H = G.permute σ`

**Status: proved** in `Isomorphic.lean`.

```
permute_of_Isomorphic        : G ≃ H → ∃ σ, H = G.permute σ
Isomorphic_of_permute        : H = G.permute σ → G ≃ H
Isomorphic_iff_exists_permute: G ≃ H ↔ ∃ σ, H = G.permute σ
```

(⟹) is induction on the `Isomorphic` constructors using `permute_one`,
`swapVertexLabels_eq_permute`, and `permute_mul` (composition order σ₂ * σ₁ in the
`trans` case is forced by the left-action law). (⟸) is `Equiv.Perm.swap_induction_on`
followed by `permute_mul` + `swapVertexLabels_eq_permute` to fold each transposition
back into an `Isomorphic.swap`.

--------------------------------------------------------------------------------

## §3  Pipeline equivariance under Aut(G)

**Goal.** For any σ ∈ `Aut G` and any vertex-type array `vts`, the canonizer pipeline
applied to the σ-permuted graph with σ-permuted types produces the σ-permuted output.

Crucially this is quantified over `σ ∈ Aut G`, **not** all of `Sym(Fin n)`. The old flat
proof quantified over all of `Sym(Fin n)`, which is false because `breakTie` is not
equivariant under arbitrary label permutations (only under automorphisms).

**Stage A — `initializePaths`.**
```
σ ∈ Aut G  →  paths in `swapVL-via-σ G` at (d, s, e)
              correspond to paths in G at (d, σ⁻¹ s, σ⁻¹ e)
```
with edge types, vertex indices, and nested `PathSegment` structures all relabeled by σ.
Proof by induction on depth; the action on `PathSegment`/`PathsBetween`/`PathsFrom` lifts
componentwise from the Fin-level action.

**Stage B — `calculatePathRankings`.** If the input `PathState` and `vertexTypes` are
σ-related, then the output ranks satisfy
```
ranks'.betweenRanks[d][s][e] = ranks.betweenRanks[d][σ⁻¹ s][σ⁻¹ e],
ranks'.fromRanks[d][s]       = ranks.fromRanks[d][σ⁻¹ s].
```
Proof by induction on depth, using that `comparePathSegments` / `comparePathsBetween` /
`comparePathsFrom` only depend on σ-invariant features (edge types and endpoint vertex
types are preserved because σ ∈ Aut G; the recursive rank references are equivariant by IH).

**Stage C — `orderVertices`.** `convergeOnce` reads `fromRanks` (equivariant by Stage B),
so it preserves the relation. `breakTie` is the interesting case — it is equivariant under
`Aut(G)` (not under `Sym(Fin n)`) *at each outer-loop iteration*, because the vertices it
chooses between are all in the same Aut(G)-orbit. See §6 for why the *choice* of which
tied vertex to promote doesn't affect the final answer.

**Stage D — `labelEdgesAccordingToRankings`.** With distinct ranks (§7), the vertex at
position p in the σ-permuted sort is σ applied to the vertex at position p in the original.
The edge at (p, q) is then `(σ·G).adj(σwₚ)(σwₙ) = G.adj wₚ wₙ` by the Aut(G) property.

**Deliverable.** Four equivariance theorems in `FullCorrectness/Equivariance.lean`:
```
initializePaths_Aut_equivariant      : σ ∈ Aut G → ...  (Stage A)
calculatePathRankings_Aut_equivariant: σ ∈ Aut G → ...  (Stage B)
orderVertices_Aut_equivariant        : σ ∈ Aut G → ...  (Stage C, modulo §6)
labelEdges_Aut_equivariant           : σ ∈ Aut G → ...  (Stage D, given §7)
```

## §4  `convergeLoop` output is Aut(G)-invariant

**Goal.**
```
σ ∈ Aut G  ∧  (∀ v, vts[σ v] = vts[v])  →  ∀ v, (convergeLoop state vts fuel)[σ v]
                                                  = (convergeLoop state vts fuel)[v]
```
i.e. if the input vertex types are Aut(G)-invariant, so is the output.

**Why.** `convergeOnce` writes `rankState.getFrom (n-1) v` into slot `v`. That value
depends only on paths-from-v; any σ ∈ Aut G bijects paths-from-v with paths-from-(σv)
preserving edge types and endpoint types (the endpoint types are Aut-invariant by the IH
on vertex-types). So the multisets fed into `comparePathsFrom` are identical, the ranks
are identical, and Aut-invariance is preserved. Induct on the fuel parameter.

**Corollary.** Starting from the all-zeros array (which is trivially Aut-invariant), after
`convergeLoop`, vertices in the same Aut(G)-orbit carry the same type.

**Deliverable.** One theorem in `FullCorrectness/Equivariance.lean`:
```
convergeLoop_Aut_invariant : σ ∈ Aut G → vts σ-invariant → convergeLoop output σ-invariant
```

## §5  `breakTie` shrinks the typed-automorphism group

Let `Aut(G, T)` := `{ σ ∈ Aut G | σ permutes T as a bijection on equal values }` be the
automorphisms preserving a given typing T. This is a subgroup of `Aut G`.

**Goal.** Let T be Aut(G)-invariant, let t₀ be the smallest value held by at least two
vertices, let V_{t₀} be its type-class, let v* := min V_{t₀} (by Fin order), and let
T' := `breakTie T t₀` (which promotes every vertex in V_{t₀} except v*). Then
```
Aut(G, T')  =  { σ ∈ Aut(G, T) | σ v* = v* }                         (stabilizer of v*)
```

**Why.** σ ∈ Aut(G, T') iff σ preserves T' iff σ sends the unique type-t₀ vertex (v*) to
itself and sends V_{t₀} \ {v*} to itself. The first condition forces σ v* = v*; the second
is then automatic given σ ∈ Aut(G, T).

**Strict shrinking.** If some τ ∈ Aut(G, T) moves v* (the `hmove` hypothesis below), then
that τ is in `TypedAut G T` but not in the v*-stabilizer, so the stabilizer is a proper
subgroup. After each tiebreak, the typed-automorphism group strictly shrinks; after at
most n tiebreaks it is trivial (all types distinct).

**Deliverable.** Both theorems are proved in `FullCorrectness/Tiebreak.lean`:
```
breakTie_Aut_stabilizer  : [with hsize + hAutInv]
    σ ∈ TypedAut G (breakTie vts t₀).1  ↔  (σ ∈ TypedAut G vts ∧ σ v* = v*)
breakTie_TypedAut_le     : TypedAut G (breakTie vts t₀).1 ≤ TypedAut G vts
breakTie_strict_shrink   : [with hmove] TypedAut G (breakTie vts t₀).1 < TypedAut G vts
```

Four position-by-position characterization lemmas underpin the proofs:
```
breakTie_size             : (breakTie vts t₀).1.size = vts.size
breakTie_getD_below       : vts[j] < t₀ → (breakTie vts t₀).1[j] = vts[j]
breakTie_getD_above       : vts[j] > t₀ → (breakTie vts t₀).1[j] = vts[j] + 1   -- when fired
breakTie_getD_at_min      : v_star is min of typeClass → (breakTie vts t₀).1[v_star] = t₀
breakTie_getD_at_other    : w ≠ v_star in typeClass → (breakTie vts t₀).1[w] = t₀ + 1
```
The split into `_below` / `_above` (rather than a single `_of_ne`) reflects the
shift-then-promote design forced by dense ranks (see the `breakTie` docstring in
[LeanGraphCanonizerV4.lean](LeanGraphCanonizerV4.lean)).

Two reusable corollaries support §7's `breakTie_targetPos_is_min_tied`:
```
breakTie_getD_target     : vts[w] = t₀ → output[w] = t₀ ∨ output[w] = t₀ + 1
breakTie_getD_target_ge  : vts[w] = t₀ → t₀ ≤ output[w]
```
Both pick `v_star` as the smallest target-valued index (`Nat.find`) and apply
`breakTie_getD_at_min` / `breakTie_getD_at_other`.

### Hypotheses beyond the original sketch

  1. **§5.1 carries `hsize : vts.size = n` and `hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts`.**
     The Aut-invariance is genuinely necessary: without it, a label swap between a
     non-`v*` member of `typeClass t₀` and some position carrying value `t₀ + 1` can
     preserve `vts'` (both get value `t₀+1`) without preserving `vts`. Aut-invariance
     rules out this counterexample, and is satisfied at every `breakTie` call by §4's
     corollary.

  2. **§5.2 carries `hmove : ∃ σ ∈ G.TypedAut vts, σ v_star ≠ v_star`.**
     The plan's sketch derived strict shrinking from "same-type vertices lie in a single
     Aut-orbit" (§4's corollary), but §4 only gives the forward direction (same-orbit →
     same-type). The reverse is essentially the algorithm's completeness and is captured
     here as the minimal needed input.

## §6  Tiebreak choice-independence (the conceptual crux)

This is the step the old flat proof did not need — because it assumed `breakTie` never
fires — and the reason the flat proof fails once tiebreaks are real.

**Goal.** Let T be Aut(G)-invariant. Let t₀ be the smallest repeated value, and let v₁, v₂
be any two vertices in V_{t₀} (so by §4 they are in the same Aut(G, T)-orbit). Let T₁ / T₂
be the result of promoting v₁ / v₂ respectively. Then
```
 Run the remainder of the canonizer pipeline (including all subsequent tiebreaks and the
 final relabel) starting from (G, T₁) vs. (G, T₂). The **final canonical matrices are equal.**
```

**Why.** Let τ ∈ Aut(G, T) with τ v₁ = v₂ (exists by same-orbit). Then the pair (G, T₂)
equals τ · (G, T₁) in the sense that G is τ-invariant (τ ∈ Aut G) and T₂ = τ · T₁ (the
promoted-type array, permuted by τ, matches the other choice). By Aut(G)-equivariance of
the remaining pipeline (§3), running on τ · (G, T₁) produces τ · (final output). But the
final output has all types distinct, so the relabel step in §8 sorts τ away, producing the
same canonical matrix.

### Reduction to a single pipeline-equivariance lemma

`tiebreak_choice_independent` carries two extra hypotheses beyond the plan sketch:
  - `hsize : vts.size = n` — trivially satisfied by the algorithm.
  - `hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂` — orbit connectivity. Same "same-type ⟹
    same-orbit" requirement that §5.2 needed, surfaced explicitly because §4 only gives
    the forward direction.

With those hypotheses, §6 reduces to the *pipeline equivariance* statement:

```
runFrom_VtsInvariant_eq :
  τ ∈ G.Aut → (∀ w, arr₂[w] = arr₁[τ⁻¹ w]) → runFrom s arr₁ G = runFrom s arr₂ G
```

which is §3 (Stages B–D) chained. **`tiebreak_choice_independent` type-checks** by
discharging via `runFrom_VtsInvariant_eq` applied to the τ-related pair `breakTieAt vts t₀
v₁`, `breakTieAt vts t₀ v₂` (related by the τ from `hconn`). The single open obligation in
this whole chain is `runFrom_VtsInvariant_eq` itself.

Supporting deliverables in `Tiebreak.lean`:
```
breakTieAt_size             : (breakTieAt vts t₀ keep).size = vts.size
breakTieAt_getD_of_ne       : vts[j] ≠ t₀ → (breakTieAt vts t₀ keep)[j] = vts[j]
breakTieAt_getD_keep        : (breakTieAt vts t₀ keep)[keep] = vts[keep]
breakTieAt_getD_promoted    : w ≠ keep ∧ vts[w] = t₀ → (breakTieAt vts t₀ keep)[w] = t₀ + 1
breakTieAt_VtsInvariant_eq  : [τ-equivariance under VtsInvariant τ vts]
```

## §7  "Converged types are a prefix of ℕ" invariant

`orderVertices` calls `breakTie convergedTypes targetPosition` where `targetPosition`
is the outer-loop counter `0, 1, …, n-1`, NOT the smallest tied value. For §5/§6 to
apply, we need: at iteration p, the smallest tied value is exactly p.

**Goal.**
```
∀ p ≤ n, after p outer iterations, the typing takes values exactly in {0, 1, …, p-1, k}
         where k is either the next tied value (= p, if one exists) or n (if all distinct).
```

**Why.** Initial types from `convergeLoop` form a prefix-of-ℕ ranking (this follows from
`assignRanks`, which assigns the index of the first element in each equivalence class;
the dense-rank pipeline keeps values exactly 0..m-1). Each `breakTie` with target p leaves
values 0..p-1 unchanged and promotes some value-p vertices to p+1, which the next
`convergeLoop` re-densifies.

**Deliverables in `FullCorrectness/Invariants.lean`:**
```
convergeLoop_preserves_prefix              : ✅ proved (specialized to `state := initializePaths G`;
                                              the general form is literally false — see file header)
getFrom_image_isPrefix_for_initializePaths : ✅ proved (deep core: `n = 0` boundary + `n ≥ 1` via
                                              outer/inner fold helpers + dense-rank density)
breakTie_targetPos_is_min_tied             : ✅ proved
orderVertices_prefix_invariant             : 🟡 closed conditional on Phase 3 sub-lemma
                                              `convergeLoop_preserves_lower_uniqueness`. Outer
                                              induction skeleton (`_strong` form) and Phase 2
                                              (breakTie step) ✅ proved.
orderVertices_n_distinct_ranks             : ✅ proved (corollary of `_prefix_invariant` at `p = n`
                                              via pigeonhole + `Finite.injective_iff_bijective`,
                                              now requires a `vts.size = n` hypothesis to thread
                                              through the strengthened invariant)
```

The `orderVertices_prefix_invariant` proof factors into three phases:

- **Phase 1 — inductive skeleton** (✅): Strengthened invariant (`_strong` form) tracks
  both the prefix-typing property and the uniqueness `0..q-1`. Induction on `q` from `0`
  to `p`. The base case is vacuous. The step uses Phase 3 (convergeLoop preservation)
  followed by Phase 2 (breakTie step).

- **Phase 2 — breakTie step** (✅ as `breakTie_step_preserves_uniqueness`): For `T`
  prefix with `0..q-1` uniquely held and `q < n`, `(breakTie T q).1` is prefix and has
  `0..q` uniquely held. Cases on `breakTieCount T q < 2` (noop) or `≥ 2` (fires).
  Uses `breakTie_getD_below`, `breakTie_getD_at_min`, `breakTie_getD_at_other`,
  `breakTie_getD_above_or`, plus a converse to `breakTieCount_ge_two_of_distinct`
  (`exists_two_distinct_q_in_T`, derived from `List.Duplicate` + `List.Sublist`).

- **Phase 3 — convergeLoop preservation** (🧱 single sorry, with sub-sub-lemmas being
  built): For `T` prefix with `0..q-1` uniquely held by `v_0..v_{q-1}` (with `T[v_k] = k`),
  `convergeLoop _ T fuel` has the same property. The proof uses three weaker facts about
  `T' = convergeOnce T`: (a) `T'[v_k] < q` for unique-typed `v_k`, (b) `T'[w] ≥ q` for
  non-unique-typed `w`, (c) `k ↦ T'[v_k]` is injective. Then `{T'[v_k] | k < q} = {0..q-1}`
  and the public `∃!` follows.

  Sub-sub-lemmas:
  - **P3.1** ✅ `comparePathsFrom_eq_compare_of_start_types_ne` (different start types ⟹
    `comparePathsFrom` returns the comparison directly).
  - **P3.B** ✅ `assignRanks_rank_le_pos` (rank at position `k` is `≤ k`). Foundational.
    Uses aux lemmas `assignRanksFoldl_lastEntry_rank_le` (lastEntry rank tracks step count)
    and `assignRanks_snoc_decompose` (snoc-decomposition with rank bound).
  - **P3.C** ✅ `assignRanks_rank_eq_pos_when_distinct` (rank `=` position when
    consecutive cmps differ). Built on `assignRanks_strong_invariant` which simultaneously
    tracks (i) rank-at-every-position and (ii) lastEntry-rank, via `reverseRecOn`
    induction. Uses `assignRanks_snoc_decompose_strict` (sharper snoc-decomposition with
    exact rank formula) and `assignRanks_foldl_lastEntry_fst` (lastEntry's first
    component).
  - **P3.D** ✅ `sortBy_first_q_positions_have_start_types`: closed this session.
    For `T` uniquely-typed at `0..q-1`, the first `q` positions of
    `sortBy comparePathsFrom T pathsAtTop` have start types `0, 1, …, q-1` in order.
    Strategy: strong induction on position `k`, with two sub-arguments:
    (A) `V_k ≥ k` — uses uniqueness + nodup of starts in sortedList: any value `j < k`
    that V_k could take would force its start to coincide with the unique witness at
    position `j` (where `V_j = j` by IH), contradicting nodup.
    (B) `V_k ≤ k` — find the unique witness `w_k` for value `k`; locate its position
    `pos` in sortedList; trichotomy on `pos` vs `k` gives a contradiction in each case
    (`pos < k` contradicts IH, `pos = k` gives `V_k = k`, `pos > k` violates Pairwise
    via P3.1 since `V_k > k = V_pos` would force `cmp = .gt`).
    Foundation work this session:
    - **`comparePathsFrom_total_preorder`** ✅ proved (by lifting from
      `comparePathsBetween_total_preorder` + the now-public `orderInsensitiveListCmp_*`
      helpers).
    - Made public: `orderInsensitiveListCmp_refl`, `orderInsensitiveListCmp_swap_lt`,
      `orderInsensitiveListCmp_swap_gt`, `orderInsensitiveListCmp_trans` in
      `ComparePathSegments.lean`; `sortBy_pairwise` in `ComparisonSort.lean`.
  - **P3.E** ✅ `convergeOnce_preserves_lower_uniqueness` fully closed.
    Prefix + size conjuncts via `convergeOnce_writeback` +
    `getFrom_image_isPrefix_for_initializePaths`. Uniqueness conjunct via the (a)/(b)/(c)
    pattern: per-vertex chain identification + P3.D + P3.C-prefix + monotonicity +
    boundary-distinctness extension. Helpers added:
    - `assignRanks_rank_eq_of_prefix` (rank at k in `assignRanks (A ++ B)` equals rank
      at k in `assignRanks A` for k < A.length).
    - `assignRanks_rank_eq_pos_when_distinct_prefix` (P3.C-prefix: rank = position for
      positions < q when only the prefix has distinct cmps).
    - `assignRanks_pairwise_rank_le` + `assignRanks_rank_monotone` (rank values
      non-decreasing along assignList; via the foldl invariant
      `revList head = lastEntry, head ≥ tail`).
    - `chain_value_at_vertex_for_assignRanks_sortBy` (per-vertex chain-rank lookup
      via `array_set_chain_at_target_nodup`).
    - **Aux** `fromRanks_at_n_minus_1_eq_chain_for_initializePaths` ✅ proved.
      Mirrors `getFrom_image_isPrefix_for_initializePaths`'s outer/inner-fold unwinding;
      witness `br` is the iteration's let-bound `updatedBetweenFn`, and after unwinding
      both sides become the same chain syntactically (closed by `rfl`).
  - **P3.5** ✅ `convergeLoop_preserves_lower_uniqueness`: closed via fuel induction
    using P3.E.

Closing `getFrom_image_isPrefix_for_initializePaths` (n ≥ 1) used these helpers, all in
`Invariants.lean`:
- `inner_fold_slice_at_depth` — strips the outer `fromAcc.set! depth` wrapper of the inner
  fold, reducing to a chain of `set!`s on the depth slice.
- `outer_fold_fromAcc_other_target_unchanged` — characterizes the outer depth loop: the
  `fromRanks` slot at any `target` is preserved as long as `target` is not in the list of
  remaining depths to process.
- `array_set_chain_outside_unchanged` / `array_set_chain_at_target_nodup` — read out a
  `set!` chain at any target index when the chain's indices are `Nodup`.
- `initializePaths_pathsAtDepth_startVertices_eq_range` — for `state := initializePaths G`,
  the depth-`d` slice's `pathsFrom.startVertexIndex.val` list equals exactly `List.range n`.
- `chain_image_dense_of_perm_and_density` — generic image-density lemma: if the chain's
  indices are a permutation of `0..n-1` and the rank set is downward-closed, the image
  over `Fin n` is exactly `{0, …, m-1}` for some `m`.
- `chain_image_dense_for_assignRanks_sortBy` — wrapper specializing to the `assignRanks ⊕
  sortBy` form, deriving the perm/density conditions from `assignRanks_map_fst`,
  `sortBy_perm`, `assignRanks_image_dense`, and the start-vertex-list equality above.

`breakTie_targetPos_is_min_tied` proof sketch: assume by contradiction two distinct
vertices `w₁ ≠ w₂` share an output value `val ≤ p`. By `breakTie_getD_target`, target-valued
positions land on `{p, p+1}`; since `p+1 > p`, an output `≤ p` rules out promotion, so
`output[w_i] = vts[w_i]` (preserved). Two sub-cases on `val`:
- `val < p`: by the prefix-uniqueness hypothesis at `k := val`, `w₁ = w₂`. ⊥.
- `val = p`: only the smallest target-valued index keeps value `p` (others are promoted by
  `breakTie_getD_at_other`), so both `w_i` equal that index. ⊥.

## §8  Assembling `run_canonical`

With §1–§7 in hand:

**(→)** Given G ≃ H. By §2, there is σ : Equiv.Perm (Fin n) with H = G.permute σ. We want
`run 0 H = run 0 G`. Decompose the pipeline:

  1. `initializePaths` + `convergeLoop` + all iterations of `breakTie`/`convergeLoop` →
     some final typing T_G (for G) / T_H (for H).
  2. `labelEdgesAccordingToRankings T_G G` / `labelEdgesAccordingToRankings T_H H`.

The pipeline applied to H = G.permute σ with the all-zeros input is related by σ to the
pipeline applied to G. For the part of σ inside Aut G, this is §3 + §4 equivariance (T_H
is σ·T_G up to tiebreak choices, and §6 says those don't matter). For the part of σ outside
Aut G… there is no "outside" — σ takes G to G.permute σ = H, and H ≃ G, so this is just
restating that G, H are isomorphic. The canonical output depends on the abstract graph,
not the labeling.

**(←)** Given `run 0 G = run 0 H`. By `run_isomorphic_to_input` (proved in §4 of the flat
file, reused here), G ≃ run 0 G and H ≃ run 0 H. Chain:
```
G ≃ run 0 G = run 0 H ≃⁻¹ H   ⟹   G ≃ H.
```
This direction re-uses the genuinely-proved §4 lemma from the old flat file.

**Deliverable.** The capstone theorem in `FullCorrectness/Main.lean`:
```
theorem run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

--------------------------------------------------------------------------------

## Risks and open invariants

**R1.** §6 strong induction requires `|Aut(G, T)|` to be a well-founded measure. Trivial
with `Fintype`, but we need to actually put a `Fintype` instance on `Aut(G, T)` (it is a
subgroup of `Sym(Fin n)` which is finite). **Resolved:** `Fintype` instances on `Aut` and
`TypedAut` are in `Automorphism.lean` and `Tiebreak.lean`.

**R2.** §7's prefix-of-ℕ invariant assumes dense ranking throughout. **Resolved by the
sparse → dense ranking migration** (now landed in `LeanGraphCanonizerV4.lean`):
`assignRanks` produces dense ranks, `getArrayRank` densifies at the entry point, and
`breakTie` uses shift-then-promote (`shiftAbove` + `breakTiePromote`) to preserve density
across iterations. Re-verify `countUniqueCanonicals 4 == 11` and the literal-string
`#guard`s in `LeanGraphCanonizerV4Tests.lean` if the algorithm is touched again.

**R3.** `convergeLoop` is given fuel equal to `state.vertexCount`. Correctness does not
require it to actually reach a fixed point — §4 says the output is always Aut-invariant,
fixed point or not — but we should double-check that "output is Aut-invariant at every
iteration" is what induction gives us, not the weaker "fixed point is Aut-invariant."

**R4.** `Fin`/`Nat` bounds on `set!`, `getD`, and the array-index arithmetic throughout
will produce side conditions. Collect into a single `def` + lemmas file if they multiply.

## Suggested development order

Serial dependencies run §1 → §2 → §3 → §4 → (§5 ∥ §7) → §6 → §8. The independent
work (Mathlib-facing infrastructure: §1 done; §2 done) can proceed in parallel with
algorithm-facing work (§3–§5 are about the specific data structures of this canonizer).

§6 is the single hardest step and should be the budgeting focus once §3–§5 are in place.
-/
