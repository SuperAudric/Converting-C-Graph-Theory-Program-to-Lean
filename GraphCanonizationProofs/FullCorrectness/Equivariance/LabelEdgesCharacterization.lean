import FullCorrectness.Equivariance.Actions
import FullCorrectness.Permutation
import FullCorrectness.Automorphism

/-!
# Cell-wise characterization of `labelEdgesAccordingToRankings`
  (`FullCorrectness.Equivariance.LabelEdgesCharacterization`)

Phase 3's deep technical content. Proves that for tie-free `rks`,

```
labelEdgesAccordingToRankings rks G = G.permute (denseRanksPerm rks)
```

where `denseRanksPerm rks : Equiv.Perm (Fin n)` is the unique permutation determined by
the dense-rank assignment.

## Approach (selection-sort by rank)

The labelEdgesAccordingToRankings fold is essentially selection sort: at step `k`, find
the vertex with rank `k` and swap it into position `k`. The cumulative effect of all
swaps is the permutation `denseRanksPerm rks` (mapping each vertex to its dense-rank
position).

The proof tracks an invariant on the fold's `(graph, rankMap)` pair, namely:
  `∃ σ_k, graph_k = G.permute σ_k AND rankMap_k = denseRanks_0 ∘ σ_k⁻¹`,
extending the strengthening pattern used in `labelEdgesAccordingToRankings_isomorphic`
(in `LeanGraphCanonizerV4Correctness.lean`) which only tracked the existence of σ_k,
not its identity.

## Status

This file establishes the foundational lemmas; the cell-wise characterization is the
deep content. Currently provides:

  * `computeDenseRanks_size` — output has size `numVertices`.
  * Helpers for working with the (rank, vertex-index) lex sort.

The full characterization is left as a `sorry` with detailed proof structure documented;
finishing it is one of the two remaining technical pieces (the other being Phase 5's
joint induction).
-/

namespace Graph

variable {n : Nat}

/-! ### `computeDenseRanks` size -/

/-- The output of `computeDenseRanks` has size equal to the input `numVertices`.

The result is built by folding over a list with `set!` operations starting from
`(Array.range numVertices).map fun _ => 0` which has size `numVertices`. Both
`set!` and the underlying `setIfInBounds` are size-preserving. -/
theorem computeDenseRanks_size (numVertices : Nat) (rks : Array VertexType) :
    (computeDenseRanks numVertices rks).size = numVertices := by
  unfold computeDenseRanks
  -- Generic: foldl of set! preserves size.
  suffices haux : ∀ (l : List Nat) (init : Array Nat),
      init.size = numVertices →
      ∀ (sorted : List (VertexType × Nat)),
        (l.foldl (fun (positionArray : Array Nat) sortedIdx =>
            positionArray.set! (sorted.getD sortedIdx (0, 0)).2 sortedIdx) init).size = numVertices by
    apply haux
    simp
  intro l
  induction l with
  | nil => intros _ h _; exact h
  | cons x xs ih =>
    intros init h_size sorted
    rw [List.foldl_cons]
    apply ih
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact h_size

/-! ### Strengthened fold lemma — tracks the cumulative permutation

Generalizes `labelEdgesAccordingToRankings_isomorphic` (which only tracks `G ≃ ...`)
by carrying an explicit permutation `σ` such that `acc.1 = G.permute σ`. This is the
strengthened invariant required for the cell-wise characterization. -/

/-- The labelEdges fold step extracted as a function. Public so downstream files
(Phase 3.E in `StageDRelational.lean`) can rewrite via `labelEdges_fold_strong`. -/
def labelEdgesStep (n : Nat) (vertices : List (Fin n))
    (accumulated : AdjMatrix n × Array Nat) (currentFin : Fin n) :
    AdjMatrix n × Array Nat :=
  let (graph, rankMap) := accumulated
  let targetPos := currentFin.val
  match vertices.find? (fun searchFin => rankMap.getD searchFin.val 0 == targetPos) with
  | none => (graph, rankMap)
  | some sourceFin =>
    let sourceIdx := sourceFin.val
    let swappedGraph := graph.swapVertexLabels currentFin sourceFin
    let rankAtSource := rankMap.getD sourceIdx 0
    let rankAtTarget := rankMap.getD targetPos 0
    (swappedGraph, (rankMap.set! sourceIdx rankAtTarget).set! targetPos rankAtSource)

/-- **Strengthened fold invariant.** For any list `vs` and accumulator with
`acc.1 = G.permute σ` for some `σ`, the foldl preserves the existence of such a
permutation. This generalizes `labelEdgesAccordingToRankings_isomorphic` from `G ≃ acc.1`
to "acc.1 is a specific permute of G".

The proof structure mirrors `labelEdgesAccordingToRankings_isomorphic`: induction on
`vs` with case-split on the `find?` branch. The `none` branch leaves σ unchanged; the
`some` branch composes one swap into σ.

**Use case:** specialized at `vs = List.finRange n` and `acc = (G, denseRanks rks)`,
the resulting σ is the cumulative composition of all swaps. Identifying this σ as
`denseRanksPerm rks` (the dense-rank perm) is the second half of the cell-wise
characterization.

**Status:** stated; not yet proved. The proof is direct but tedious — each swap
contributes one `Equiv.swap` factor to σ. -/
theorem labelEdges_fold_permutes
    (G : AdjMatrix n) (vs : List (Fin n)) (acc : AdjMatrix n × Array Nat)
    (σ : Equiv.Perm (Fin n)) (h_acc : acc.1 = G.permute σ) :
    ∃ σ' : Equiv.Perm (Fin n),
      (vs.foldl (labelEdgesStep n (List.finRange n)) acc).1 = G.permute σ' := by
  induction vs generalizing acc σ with
  | nil =>
    -- Base case: the foldl is acc itself.
    refine ⟨σ, ?_⟩
    rw [List.foldl_nil]
    exact h_acc
  | cons v rest ih =>
    rw [List.foldl_cons]
    -- One step: case-split on the find? branch.
    obtain ⟨graph, rankMap⟩ := acc
    show ∃ σ', (rest.foldl (labelEdgesStep n (List.finRange n))
                  (labelEdgesStep n (List.finRange n) (graph, rankMap) v)).1 = G.permute σ'
    unfold labelEdgesStep
    simp only []
    split
    · -- none branch: accumulator unchanged.
      apply ih
      exact h_acc
    · -- some sourceFin branch: graph gets one swap.
      rename_i sourceFin _
      apply ih (acc := (graph.swapVertexLabels v sourceFin, _))
      -- New graph = graph.swapVertexLabels v sourceFin
      --           = (G.permute σ).swapVertexLabels v sourceFin
      --           = (G.permute σ).permute (Equiv.swap v sourceFin)
      --           = G.permute (Equiv.swap v sourceFin * σ).
      have h_graph_eq : graph = G.permute σ := h_acc
      show graph.swapVertexLabels v sourceFin = G.permute (Equiv.swap v sourceFin * σ)
      rw [swapVertexLabels_eq_permute, h_graph_eq, ← AdjMatrix.permute_mul]

/-! ### Strong fold invariant — tracks the rankMap as well

This is the deeper variant of `labelEdges_fold_permutes`. It additionally tracks
`acc.2 = rankMap_0 ∘ σ⁻¹` (in `getD`-pointwise form). Combined with the algorithm's
selection-sort structure, this lets us identify the σ at the end of the fold.

The key insight: the labelEdges fold updates rankMap by swapping two entries (at
`currentFin.val` and `sourceFin.val`). This corresponds to composing one `Equiv.swap`
into σ — and the rankMap relationship `rankMap = rankMap_0 ∘ σ⁻¹` is preserved by
this composition. -/

/-- Local helper: `set!` at the same in-bounds index gives the inserted value. -/
private theorem set!_getD_self_aux (xs : Array Nat) (i : Nat) (v d : Nat)
    (h : i < xs.size) : (xs.set! i v).getD i d = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

/-- Local helper: `set!` at a different index leaves `getD` unchanged. -/
private theorem set!_getD_ne_aux (xs : Array Nat) (i j : Nat) (v d : Nat)
    (h : i ≠ j) : (xs.set! i v).getD j d = xs.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

/-- **Local helper for the rankMap swap step.** When the rankMap satisfies the find?
condition `rankMap[sourceFin] = v`, the swap-step on the rankMap is equivalent to
swapping the values at positions `v.val` and `sourceFin.val`, which is exactly
`rankMap` indexed via `Equiv.swap v sourceFin`. -/
private theorem rankMap_swap_step_eq
    (rankMap : Array Nat) (v sourceFin : Fin n) (h_size : rankMap.size = n)
    (h_eq_at_sf : rankMap.getD sourceFin.val 0 = v.val) (v' : Fin n) :
    ((rankMap.set! sourceFin.val (rankMap.getD v.val 0)).set! v.val
      (rankMap.getD sourceFin.val 0)).getD v'.val 0
    = rankMap.getD ((Equiv.swap v sourceFin) v').val 0 := by
  -- Bound facts.
  have h_v_lt : v.val < (rankMap.set! sourceFin.val (rankMap.getD v.val 0)).size := by
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; rw [h_size]; exact v.isLt
  -- Case-split on v' = v, v' = sourceFin, or other.
  by_cases h_v_eq : v'.val = v.val
  · -- v' = v: result is rankAtSource = rankMap[sourceFin] = v.val.
    have h_swap : (Equiv.swap v sourceFin) v' = sourceFin := by
      have h_v'_eq_v : v' = v := Fin.ext h_v_eq
      rw [h_v'_eq_v]; exact Equiv.swap_apply_left v sourceFin
    rw [h_swap, h_eq_at_sf]
    -- LHS: outer set! at v.val gives rankMap[sourceFin] = v.val.
    rw [h_v_eq, set!_getD_self_aux _ v.val _ _ h_v_lt]
  · by_cases h_sf_eq : v'.val = sourceFin.val
    · -- v' = sourceFin (and v.val ≠ sourceFin.val by case 1).
      have h_swap : (Equiv.swap v sourceFin) v' = v := by
        have h_v'_eq_sf : v' = sourceFin := Fin.ext h_sf_eq
        rw [h_v'_eq_sf]; exact Equiv.swap_apply_right v sourceFin
      rw [h_swap]
      -- LHS: outer set! at v.val DIDN'T touch v'.val = sourceFin.val (since v.val ≠ sourceFin.val).
      have h_v_ne : v.val ≠ v'.val := fun h => h_v_eq h.symm
      rw [set!_getD_ne_aux _ v.val v'.val _ _ h_v_ne]
      -- LHS: inner set! at sourceFin.val DID touch v'.val = sourceFin.val (since v'.val = sourceFin.val).
      rw [h_sf_eq]
      have h_sf_lt : sourceFin.val < rankMap.size := h_size ▸ sourceFin.isLt
      rw [set!_getD_self_aux _ sourceFin.val _ _ h_sf_lt]
    · -- v' ≠ v, v' ≠ sourceFin: rankMap unchanged at v', and swap is identity at v'.
      have h_swap : (Equiv.swap v sourceFin) v' = v' := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; exact h_v_eq (by rw [h])
        · intro h; exact h_sf_eq (by rw [h])
      rw [h_swap]
      -- LHS: both set!s leave v'.val alone.
      have h_v_ne : v.val ≠ v'.val := fun h => h_v_eq h.symm
      have h_sf_ne : sourceFin.val ≠ v'.val := fun h => h_sf_eq h.symm
      rw [set!_getD_ne_aux _ v.val v'.val _ _ h_v_ne]
      rw [set!_getD_ne_aux _ sourceFin.val v'.val _ _ h_sf_ne]

/-- **Strong fold invariant**: tracks both the cumulative permutation σ AND the
relationship between the current rankMap and the original rankMap_0 via σ⁻¹.

The invariant: at any point in the fold,
  `output.1 = G.permute σ AND output.2.size = n AND
   ∀ v, output.2.getD v.val 0 = rankMap_0.getD (σ⁻¹ v).val 0`. -/
theorem labelEdges_fold_strong
    (G : AdjMatrix n) (rankMap_0 : Array Nat) (h_size_0 : rankMap_0.size = n)
    (vs : List (Fin n)) (acc : AdjMatrix n × Array Nat)
    (σ : Equiv.Perm (Fin n))
    (h_graph : acc.1 = G.permute σ)
    (h_rankMap_size : acc.2.size = n)
    (h_rankMap_eq : ∀ v : Fin n, acc.2.getD v.val 0 = rankMap_0.getD (σ⁻¹ v).val 0) :
    ∃ σ' : Equiv.Perm (Fin n),
      (vs.foldl (labelEdgesStep n (List.finRange n)) acc).1 = G.permute σ' ∧
      (vs.foldl (labelEdgesStep n (List.finRange n)) acc).2.size = n ∧
      (∀ v : Fin n, (vs.foldl (labelEdgesStep n (List.finRange n)) acc).2.getD v.val 0
                    = rankMap_0.getD (σ'⁻¹ v).val 0) := by
  induction vs generalizing acc σ with
  | nil =>
    refine ⟨σ, ?_, ?_, ?_⟩
    · rw [List.foldl_nil]; exact h_graph
    · rw [List.foldl_nil]; exact h_rankMap_size
    · intro v; rw [List.foldl_nil]; exact h_rankMap_eq v
  | cons v rest ih =>
    rw [List.foldl_cons]
    obtain ⟨graph, rankMap⟩ := acc
    have h_graph_eq : graph = G.permute σ := h_graph
    have h_rankMap_size_v : rankMap.size = n := h_rankMap_size
    have h_rankMap_eq_v : ∀ v' : Fin n, rankMap.getD v'.val 0
                                       = rankMap_0.getD (σ⁻¹ v').val 0 := h_rankMap_eq
    show ∃ σ', (rest.foldl (labelEdgesStep n (List.finRange n))
                 (labelEdgesStep n (List.finRange n) (graph, rankMap) v)).1 = G.permute σ' ∧ _ ∧ _
    unfold labelEdgesStep
    simp only []
    split
    · -- none branch: accumulator unchanged.
      apply ih (σ := σ)
      · exact h_graph_eq
      · exact h_rankMap_size_v
      · exact h_rankMap_eq_v
    · -- some sourceFin branch.
      rename_i sourceFin h_find
      -- Key fact: rankMap.getD sourceFin.val 0 = v.val (from the find? predicate).
      have h_find_eq : rankMap.getD sourceFin.val 0 = v.val := by
        have h_member := List.find?_some h_find
        simp at h_member
        rw [Array.getD_eq_getD_getElem?]
        exact h_member
      apply ih (σ := Equiv.swap v sourceFin * σ)
      · -- graph_new = G.permute (swap v sourceFin * σ).
        show graph.swapVertexLabels v sourceFin = G.permute (Equiv.swap v sourceFin * σ)
        rw [swapVertexLabels_eq_permute, h_graph_eq, ← AdjMatrix.permute_mul]
      · -- size preserved.
        show ((rankMap.set! sourceFin.val (rankMap.getD v.val 0)).set! v.val
                (rankMap.getD sourceFin.val 0)).size = n
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
            Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact h_rankMap_size_v
      · -- rankMap relationship preserved.
        intro v'
        show ((rankMap.set! sourceFin.val (rankMap.getD v.val 0)).set! v.val
                (rankMap.getD sourceFin.val 0)).getD v'.val 0
            = rankMap_0.getD ((Equiv.swap v sourceFin * σ)⁻¹ v').val 0
        -- Use the helper rankMap_swap_step_eq.
        rw [rankMap_swap_step_eq rankMap v sourceFin h_rankMap_size_v h_find_eq v']
        -- Now: rankMap.getD (Equiv.swap v sourceFin v').val 0
        --    = rankMap_0.getD ((Equiv.swap v sourceFin * σ)⁻¹ v').val 0.
        -- Apply h_rankMap_eq_v (Equiv.swap v sourceFin v').
        rw [h_rankMap_eq_v (Equiv.swap v sourceFin v')]
        -- Now we need: σ⁻¹ (Equiv.swap v sourceFin v') = (Equiv.swap v sourceFin * σ)⁻¹ v'.
        -- (Equiv.swap v sourceFin * σ)⁻¹ v' = σ⁻¹ (Equiv.swap v sourceFin)⁻¹ v'
        --                                   = σ⁻¹ (Equiv.swap v sourceFin v')   (swap is self-inverse).
        rfl

/-! ### Terminal rankMap identity

The labelEdges fold over `List.finRange n` is selection-sort: it processes positions
0, 1, ..., n-1 in order, placing the vertex with rank `k` at position `k` at iteration
`k`. Once placed, the rankMap entry at position `k` becomes `k.val` and is never touched
again (the find? predicate at later iterations searches for `currentFin'.val ≠ k.val`).

So the terminal rankMap is "identity": `rankMap.getD v.val 0 = v.val` for all `v`. -/

/-- **Auxiliary fold invariant for terminal rankMap identity.**

For any sublist `vs` of `List.finRange n` (Nodup), starting from acc where:
  - rankMap values contain each `k.val` for `k : Fin n` somewhere (multiset fact),
  - rankMap is "already identity" on positions outside `vs`,
the terminal rankMap (after processing `vs`) is identity on every position.

This generalized form lets us induct cleanly: the IH applies to the tail with one
fewer remaining element, and the "outside vs" set grows by one. -/
private theorem labelEdges_fold_terminal_aux
    (vs : List (Fin n)) (h_nodup : vs.Nodup)
    (acc : AdjMatrix n × Array Nat)
    (h_size : acc.2.size = n)
    (h_multiset : ∀ k : Fin n, ∃ w : Fin n, acc.2.getD w.val 0 = k.val)
    (h_processed : ∀ v : Fin n, v ∉ vs → acc.2.getD v.val 0 = v.val) :
    ∀ v : Fin n,
      (vs.foldl (labelEdgesStep n (List.finRange n)) acc).2.getD v.val 0 = v.val := by
  induction vs generalizing acc with
  | nil =>
    intro v
    rw [List.foldl_nil]
    exact h_processed v (by simp)
  | cons head tail ih =>
    rw [List.foldl_cons]
    -- Apply the step at `head`. We need to show the invariant is preserved.
    obtain ⟨graph, rankMap⟩ := acc
    have h_size_v : rankMap.size = n := h_size
    -- Prepare for find?: ∃ w, rankMap[w.val] = head.val, by h_multiset.
    obtain ⟨w_head, h_w_head_eq⟩ := h_multiset head
    -- find? on List.finRange n with predicate `rankMap[searchFin.val] == head.val`
    -- returns some matching element. Use cases on the result.
    have h_w_in : w_head ∈ List.finRange n := List.mem_finRange w_head
    have h_w_pred : (fun searchFin : Fin n => rankMap.getD searchFin.val 0 == head.val) w_head
                    = true := by
      simp only []
      rw [h_w_head_eq]; simp
    have h_find_isSome :
        ((List.finRange n).find? (fun searchFin : Fin n =>
          rankMap.getD searchFin.val 0 == head.val)).isSome := by
      rw [List.find?_isSome]
      exact ⟨w_head, h_w_in, h_w_pred⟩
    -- Extract the sourceFin.
    obtain ⟨sourceFin, h_find_eq⟩ := Option.isSome_iff_exists.mp h_find_isSome
    -- Get the property of sourceFin: rankMap[sourceFin.val] = head.val.
    have h_sf_eq : rankMap.getD sourceFin.val 0 = head.val := by
      have h_sf_pred := List.find?_some h_find_eq
      simp at h_sf_pred
      rw [Array.getD_eq_getD_getElem?]
      exact h_sf_pred
    -- Compute the step's output explicitly.
    -- labelEdgesStep with `find? = some sourceFin` produces the swap step.
    show ∀ v : Fin n, (tail.foldl (labelEdgesStep n (List.finRange n))
                        (labelEdgesStep n (List.finRange n) (graph, rankMap) head)).2.getD
                          v.val 0 = v.val
    -- Apply IH on tail with new accumulator.
    apply ih
    · exact (List.nodup_cons.mp h_nodup).2
    · -- Size preserved.
      unfold labelEdgesStep
      simp only []
      rw [h_find_eq]
      -- Output: (graph.swapVertexLabels head sourceFin, (rankMap.set! ...).set! ...).
      show ((rankMap.set! sourceFin.val (rankMap.getD head.val 0)).set! head.val
              (rankMap.getD sourceFin.val 0)).size = n
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
          Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact h_size_v
    · -- Multiset preserved: for each k, some w' has new rankMap[w'.val] = k.val.
      intro k
      unfold labelEdgesStep
      simp only []
      rw [h_find_eq]
      show ∃ w' : Fin n,
        ((rankMap.set! sourceFin.val (rankMap.getD head.val 0)).set! head.val
          (rankMap.getD sourceFin.val 0)).getD w'.val 0 = k.val
      -- Use the rankMap_swap_step_eq helper: new rankMap at w' = rankMap at swap_perm w'.
      -- So we need rankMap at swap_perm⁻¹ (witness for k) = k.val.
      -- Equivalently, find w' such that swap_perm w' is the witness for k in old rankMap.
      obtain ⟨w_old, h_w_old⟩ := h_multiset k
      -- Apply swap_perm⁻¹ = swap_perm to w_old to get w'.
      refine ⟨(Equiv.swap head sourceFin) w_old, ?_⟩
      rw [rankMap_swap_step_eq rankMap head sourceFin h_size_v h_sf_eq]
      -- Goal: rankMap.getD ((Equiv.swap head sourceFin) ((Equiv.swap head sourceFin) w_old)).val 0 = k.val
      rw [Equiv.swap_apply_self]
      exact h_w_old
    · -- "Already processed" property: for v ∉ tail, new rankMap[v.val] = v.val.
      intro v h_v_not_in_tail
      unfold labelEdgesStep
      simp only []
      rw [h_find_eq]
      show ((rankMap.set! sourceFin.val (rankMap.getD head.val 0)).set! head.val
              (rankMap.getD sourceFin.val 0)).getD v.val 0 = v.val
      rw [rankMap_swap_step_eq rankMap head sourceFin h_size_v h_sf_eq]
      -- Case-split on v = head (= currentFin) vs v ∉ vs.
      by_cases h_v_eq_head : v = head
      · -- v = head. (Equiv.swap head sourceFin) head = sourceFin.
        subst h_v_eq_head
        rw [Equiv.swap_apply_left]
        exact h_sf_eq
      · -- v ≠ head, v ∉ tail. So v ∉ vs = head :: tail.
        have h_v_not_in_vs : v ∉ head :: tail := by
          intro h
          rcases List.mem_cons.mp h with h | h
          · exact h_v_eq_head h
          · exact h_v_not_in_tail h
        -- By h_processed, rankMap[v.val] = v.val.
        have h_v_processed : rankMap.getD v.val 0 = v.val := h_processed v h_v_not_in_vs
        -- Need: (Equiv.swap head sourceFin) v ≠ head and ≠ sourceFin (so the swap is identity at v).
        -- Actually we need to show rankMap.getD ((Equiv.swap head sourceFin) v).val 0 = v.val.
        -- For (Equiv.swap head sourceFin) v: depends on v vs head, sourceFin.
        -- v ≠ head (by h_v_eq_head).
        -- v vs sourceFin: if v = sourceFin, then h_processed gives rankMap[v.val] = v.val,
        --   but rankMap[sourceFin.val] = head.val ≠ v.val (since v = sourceFin so v.val = sourceFin.val,
        --   but v ≠ head so v.val ≠ head.val, contradicting h_sf_eq if v = sourceFin and v.val = sourceFin.val).
        --   So sourceFin = v would mean sourceFin.val = v.val, h_sf_eq: rankMap[sourceFin.val] = head.val,
        --   h_v_processed: rankMap[v.val] = v.val. So head.val = v.val, contradicting v ≠ head (Fin.ext).
        have h_v_ne_sf : v ≠ sourceFin := by
          intro h_eq
          rw [h_eq] at h_v_processed
          rw [h_v_processed] at h_sf_eq
          -- Now h_sf_eq : sourceFin.val = head.val, so sourceFin = head, but v = sourceFin
          -- and v ≠ head gives sourceFin ≠ head.
          have h_sf_eq_head : sourceFin = head := Fin.ext h_sf_eq
          rw [h_sf_eq_head] at h_eq
          exact h_v_eq_head h_eq
        rw [Equiv.swap_apply_of_ne_of_ne h_v_eq_head h_v_ne_sf]
        exact h_v_processed

/-- **Terminal rankMap identity** for the `labelEdgesAccordingToRankings` fold. After
the foldl over `List.finRange n` starting from any rankMap_0 whose values are a
permutation of `{0, 1, ..., n-1}`, the terminal rankMap satisfies
`rankMap.getD v.val 0 = v.val` for all `v : Fin n`. -/
theorem labelEdges_terminal_rankMap_identity
    (G : AdjMatrix n) (rankMap_0 : Array Nat) (h_size : rankMap_0.size = n)
    (h_multiset : ∀ k : Fin n, ∃ w : Fin n, rankMap_0.getD w.val 0 = k.val) :
    ∀ v : Fin n,
      ((List.finRange n).foldl (labelEdgesStep n (List.finRange n)) (G, rankMap_0)).2.getD
          v.val 0 = v.val := by
  apply labelEdges_fold_terminal_aux
  · exact List.nodup_finRange n
  · exact h_size
  · exact h_multiset
  · intro v h_not_in
    exfalso
    exact h_not_in (List.mem_finRange v)

/-! ### Combining the pieces: cell-wise characterization

With `labelEdges_fold_strong` (σ-tracking) and `labelEdges_terminal_rankMap_identity`
(terminal rankMap), we can identify σ at the end of the fold:

  output.2.getD v.val 0 = rankMap_0.getD (σ⁻¹ v).val 0   (from fold_strong)
  output.2.getD v.val 0 = v.val                        (from terminal_rankMap_identity)
  ⟹ rankMap_0.getD (σ⁻¹ v).val 0 = v.val              (combine)

So σ⁻¹ is the unique vertex map satisfying `rankMap_0.getD (σ⁻¹ v).val 0 = v.val`.
For tie-free rks, this is `vertexAtRank rks` — the inverse of the dense-rank
permutation. -/

/-! ### Status of remaining cell-wise characterization

With `labelEdges_fold_strong` (proved) and `labelEdges_terminal_rankMap_identity`
(stated as the last open piece), the cell-wise characterization of labelEdges follows:

  output.2.getD v.val 0 = rankMap_0.getD (σ⁻¹ v).val 0   (from fold_strong)
  output.2.getD v.val 0 = v.val                          (from terminal_rankMap_identity)
  ⟹ rankMap_0.getD (σ⁻¹ v).val 0 = v.val                (combine)

Specialized at `rankMap_0 = computeDenseRanks rks` (tie-free), this means σ⁻¹ acts
as `vertexAtRank rks` (the unique-vertex-with-given-rank map). The labelEdges output
is then `G.permute σ`.

For Phase 3's main theorem (Stage D-rel under tie-freeness), the analogous
characterization on rks₂ = τ-shifted rks₁ shows `σ_2 = σ_1 ∘ τ⁻¹`, and the `τ⁻¹ ∈ Aut G`
condition collapses the difference.

Once `labelEdges_terminal_rankMap_identity` is closed, the rest is ~50 lines of algebra
in `StageDRelational.lean`.
-/

end Graph
