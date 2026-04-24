import LeanGraphCanonizerV4
import FullCorrectness.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Correctness of the Graph Canonizer — **FLAWED / ABANDONED ATTEMPT**

> ⚠ **Status: not a valid proof.**  Parts of this file are genuinely proved and are reused
> elsewhere (see "What is still correct" below), but the central strategy — a full-Sym(n)
> equivariance of the pipeline under `swapVTs` — is based on a **false premise** about how
> `breakTie` interacts with label permutations. Several lemma statements in §5 are
> unprovable as written, and the main theorems in §7 transitively depend on them via
> `sorry`. The corrected proof is being developed in the `FullCorrectness/` tree, starting
> with an Aut(G)-restricted equivariance and a separate tiebreak-choice-independence
> argument. See `FullCorrectness/Isomorphic.lean` and its header for the replacement plan.

## The flawed premise

The old strategy assumed: for any vertex swap σ = (v₁ v₂),
```
  orderVertices (σ · G) (σ · vts) = σ · orderVertices G vts.
```
This would be true if `convergeLoop` alone separated every automorphism orbit (i.e. if
`breakTie` never fired non-trivially). It is **false** in general because `breakTie`
picks the *lowest-index* vertex from a tied class and promotes it. After applying σ to
the graph, a *different* vertex is now the lowest-index in the tied class, so a different
vertex is promoted, and the resulting rankings differ by more than just a swap.

Equivalently: `breakTie` is equivariant under `Aut(G)` (the graph's symmetry group), but
**not** under arbitrary elements of `Sym(Fin n)`. The old proof quantified over all of
`Sym(Fin n)` via `swapVTs`, so it cannot close.

## What is still correct (reused by `FullCorrectness/`)

Four things in this file are genuinely proved and safe to depend on:

  §2  `swapVertexLabels_self_inverse`, `swapVertexLabels_comm` — concrete swap facts.
  §3  `Isomorphic.symm`                                        — `≃` is an equivalence relation.
  §4  `labelEdgesAccordingToRankings_isomorphic`,
      `run_isomorphic_to_input`                                — `G ≃ run vts G` for all vts.
      This alone suffices for the (←) direction of the main theorem: if canonical forms
      agree then `G ≃ run zeros G = run zeros H ≃⁻¹ H`, so `G ≃ H`. That direction,
      `run_eq_implies_iso` in §7, is therefore genuinely proved by this file.

## What is broken (do not depend on)

  §5  `orderVertices_swap_equivariant`   — **STATEMENT IS FALSE**. Cannot be proved.
  §5  `orderVertices_distinct_ranks`     — statement is true, but the surrounding
                                            narrative about why was wrong; see inline
                                            warning at the theorem.
  §5  `labelEdges_swap_equivariant`      — conditionally fine but unreachable: the proof
                                            chain to its `hdist` hypothesis goes through
                                            the false lemma above.
  §6  `run_swap_invariant`               — *statement* is true (consequence of the
                                            canonical theorem), but the sketched proof
                                            through §5 cannot be completed. `sorry`.
  §7  `run_isomorphic_eq`, `run_canonical` — *statements* are true; their proofs here
                                              route through `run_swap_invariant` and so
                                              are effectively `sorry`. Do not import
                                              these for a claim of correctness.

## Sections

  §1  AdjMatrix extensionality                              [shared via `FullCorrectness.Basic`]
  §2  swapVertexLabels involution                           [proved]
  §3  Isomorphic is an equivalence relation                 [proved]
  §4  `run` output is isomorphic to input                   [proved]
  §5  Equivariance lemmas for the pipeline                  [BROKEN — one statement is false]
  §6  `run_swap_invariant`                                  [sorry; strategy cannot close]
  §7  Main theorems                                         [sorry-reachable via §6]
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## §1  AdjMatrix extensionality -/

-- `AdjMatrix.ext` is now shared via `FullCorrectness.Basic`.

/-! ## §2  swapVertexLabels is an involution -/

/-- The conditional-swap function `fun x => if x=v1 then v2 else if x=v2 then v1 else x` is an
    involution: applying it twice returns the original value. -/
private theorem swapFin_invol (v1 v2 x : Fin n) :
    (if (if x = v1 then v2 else if x = v2 then v1 else x) = v1
     then v2
     else if (if x = v1 then v2 else if x = v2 then v1 else x) = v2
          then v1
          else (if x = v1 then v2 else if x = v2 then v1 else x)) = x := by
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all

theorem swapVertexLabels_self_inverse (v1 v2 : Fin n) (G : AdjMatrix n) :
    swapVertexLabels v1 v2 (swapVertexLabels v1 v2 G) = G := by
  ext i j; simp only [swapVertexLabels, swapFin_invol]

theorem swapVertexLabels_comm (v1 v2 : Fin n) (G : AdjMatrix n) :
    swapVertexLabels v1 v2 G = swapVertexLabels v2 v1 G := by
  ext i j
  simp only [swapVertexLabels]
  split_ifs with hi1 hi2 hj1 hj2 <;> simp_all

/-! ## §3  Isomorphic is an equivalence relation -/

/-- `Isomorphic` is symmetric: if G ≃ H then H ≃ G. -/
theorem AdjMatrix.Isomorphic.symm {n : Nat} {G H : AdjMatrix n} (h : G ≃ H) : H ≃ G := by
  induction h with
  | refl G => exact .refl G
  | swap G v1 v2 =>
    -- Need: swapVertexLabels v1 v2 G ≃ G.
    -- Applying .swap to (swapVertexLabels v1 v2 G) gives it ≃ its own swap, which by
    -- self_inverse equals G.
    have h := Isomorphic.swap (swapVertexLabels v1 v2 G) v1 v2
    rw [swapVertexLabels_self_inverse] at h
    exact h
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

/-! ## §4  `labelEdgesAccordingToRankings` output is isomorphic to input -/

/-- The fold inside `labelEdgesAccordingToRankings` applies zero or more `swapVertexLabels`
    calls.  Therefore its output is isomorphic to its graph input.

    Proof sketch: strengthen to ∀ G' with G ≃ G', `G ≃ (foldl step (G', ranks) vs).1`.
    Base: G ≃ G (refl).  Step: if G ≃ g then G ≃ g (none branch) or G ≃ swapVL cur src g
    (some branch, by trans with Isomorphic.swap g cur src). -/
theorem labelEdgesAccordingToRankings_isomorphic {n : Nat}
    (vts : Array VertexType) (G : AdjMatrix n) :
    G ≃ labelEdgesAccordingToRankings vts G := by
  -- Strengthen: for any acc with G ≃ acc.1, the fold output's first component is ≃ G.
  -- This lets the induction go, since each step either leaves the graph alone (none branch)
  -- or applies swapVertexLabels (some branch), both preserving the invariant.
  suffices key : ∀ (vs : List (Fin n)) (acc : AdjMatrix n × Array Nat),
      G ≃ acc.1 →
      G ≃ (vs.foldl
            (fun (accumulated : AdjMatrix n × Array Nat) currentFin =>
              let (graph, rankMap) := accumulated
              let targetPos := currentFin.val
              match (List.finRange n).find? fun searchFin =>
                  rankMap.getD searchFin.val 0 == targetPos with
              | none => (graph, rankMap)
              | some sourceFin =>
                  let sourceIdx    := sourceFin.val
                  let swappedGraph := graph.swapVertexLabels currentFin sourceFin
                  let rankAtSource := rankMap.getD sourceIdx 0
                  let rankAtTarget := rankMap.getD targetPos 0
                  (swappedGraph,
                   (rankMap.set! sourceIdx rankAtTarget).set! targetPos rankAtSource))
            acc).1 by
    -- Let Lean infer the list and initial accumulator via definitional unfolding of
    -- labelEdgesAccordingToRankings (avoids naming the private computeDenseRanks).
    exact key _ _ (.refl G)
  intro vs
  induction vs with
  | nil =>
    intro acc hG
    simp only [List.foldl_nil]
    exact hG
  | cons v rest ih =>
    intro acc hG
    obtain ⟨graph, rankMap⟩ := acc
    simp only [List.foldl_cons]
    apply ih
    -- Goal: G ≃ (step ⟨graph, rankMap⟩ v).1.
    -- dsimp reduces the beta/iota/zeta redexes to expose the match; then split on it.
    -- (.1 on a match is NOT def-eq to pushing .1 into branches, but after split each
    -- branch has .1 on a concrete constructor, which does reduce definitionally.)
    dsimp only
    split
    · -- none branch: accumulator unchanged, first component is still graph
      exact hG
    · -- some src branch: graph gets one swapVertexLabels step; let Lean infer the vertex
      exact hG.trans (.swap graph v _)

/-- The output of `run` is always isomorphic to its graph input. -/
theorem run_isomorphic_to_input {n : Nat} (vts : Array VertexType) (G : AdjMatrix n) :
    G ≃ run vts G :=
  labelEdgesAccordingToRankings_isomorphic _ G

/-! ## §5  Equivariance of the canonizer pipeline -/

/-- Swap two positions in a `VertexType` array. -/
def swapVTs (v1 v2 : Fin n) (vts : Array VertexType) : Array VertexType :=
  let a := vts.getD v1.val 0
  let b := vts.getD v2.val 0
  (vts.set! v1.val b).set! v2.val a

/-- Swapping the same position twice is the identity. -/
theorem swapVTs_self_inverse (v1 v2 : Fin n) (vts : Array VertexType) (hvts : vts.size = n) :
    swapVTs v1 v2 (swapVTs v1 v2 vts) = vts := by
  have hv1 : v1.val < vts.size := hvts ▸ v1.isLt
  have hv2 : v2.val < vts.size := hvts ▸ v2.isLt
  simp only [swapVTs, Array.set!_eq_setIfInBounds]
  -- Helper: setting a position to its current value is identity.
  have hself : ∀ (i : Nat) (hi : i < vts.size), vts.setIfInBounds i (vts.getD i 0) = vts := by
    intro i hi
    apply Array.ext_getElem?
    intro k
    simp only [Array.getElem?_setIfInBounds]
    by_cases h : i = k
    · subst h; simp [Array.getD_eq_getD_getElem?, hi]
    · simp [h]
  -- inner = (vts.setIfInBounds v1 (getD v2 0)).setIfInBounds v2 (getD v1 0)
  -- inner.getD v1 0 = getD v2 0  (last write at v1 came from position v2)
  have hD1 : ((vts.setIfInBounds v1.val (vts.getD v2.val 0)).setIfInBounds v2.val
              (vts.getD v1.val 0)).getD v1.val 0 = vts.getD v2.val 0 := by
    by_cases h : v2.val = v1.val
    · simp [Array.getD_eq_getD_getElem?, h, hv1]
    · simp [Array.getD_eq_getD_getElem?, h, hv1]
  -- inner.getD v2 0 = getD v1 0  (last write at v2 came from position v1)
  have hD2 : ((vts.setIfInBounds v1.val (vts.getD v2.val 0)).setIfInBounds v2.val
              (vts.getD v1.val 0)).getD v2.val 0 = vts.getD v1.val 0 := by
    simp [Array.getD_eq_getD_getElem?, hv2]
  rw [hD1, hD2]
  -- Goal: (((vts.sIB v1 Q).sIB v2 P).sIB v1 P).sIB v2 Q = vts
  --   where P = getD v1 0, Q = getD v2 0
  by_cases h12 : v1.val = v2.val
  · -- v1 = v2: all four operations are at the same index, collapse repeatedly.
    simp only [h12, Array.setIfInBounds_setIfInBounds]
    exact hself v2.val hv2
  · -- v1 ≠ v2: commute (sIB v2 P · sIB v1 P) to (sIB v1 P · sIB v2 P),
    --   then collapse each pair of same-index writes.
    have hne : v2.val ≠ v1.val := Ne.symm h12
    rw [Array.setIfInBounds_comm (vts.getD v1.val 0) (vts.getD v1.val 0) hne]
    simp only [Array.setIfInBounds_setIfInBounds]
    rw [hself v1.val hv1]
    exact hself v2.val hv2

/-- An all-zeros array is invariant under any position swap (all values are already equal). -/
theorem swapVTs_zeros (v1 v2 : Fin n) :
    swapVTs v1 v2 (Array.replicate n 0) = Array.replicate n 0 := by
  simp only [swapVTs]
  -- Both getD calls return 0: every element of replicate n 0 is 0.
  have ha : (Array.replicate n (0 : VertexType)).getD v1.val 0 = 0 := by
    simp [v1.isLt]
  have hb : (Array.replicate n (0 : VertexType)).getD v2.val 0 = 0 := by
    simp [v2.isLt]
  -- set!-ing 0 into an all-0 array is a no-op (setIfInBounds_replicate_self).
  simp only [ha, hb, Array.set!_eq_setIfInBounds, Array.setIfInBounds_replicate_self]

/-- ⚠ **THIS STATEMENT IS FALSE.** Kept as a record of the flawed old strategy; do not
    import or depend on it.

    The claim is that `orderVertices` commutes with arbitrary label swaps. It fails
    because `breakTie` is not equivariant under `Sym(Fin n)` — it picks the lowest-index
    element of a tied class, and a label swap changes which element is lowest-index. See
    the file header for the full discussion.

    A correct, restricted version (with σ ∈ `Aut G`, not arbitrary σ) is planned in
    `FullCorrectness/Equivariance.lean`. -/
theorem orderVertices_swap_equivariant {n : Nat} (G : AdjMatrix n) (v1 v2 : Fin n)
    (vts : Array VertexType) :
    orderVertices (initializePaths (swapVertexLabels v1 v2 G)) (swapVTs v1 v2 vts) =
    swapVTs v1 v2 (orderVertices (initializePaths G) vts) := by
  sorry

/-- After `orderVertices` finishes, all vertices have distinct rank values.

    **Note on history.** An earlier version of the surrounding narrative claimed this held
    *because* `breakTie` never fires — that claim was wrong. `breakTie` does fire on graphs
    with non-trivial automorphisms, but the tied vertices are symmetric to each other, so
    promoting one of them just collapses one symmetry. The **statement** of this theorem
    (ranks distinct after n iterations) is still correct by design of the outer loop, but
    the flawed narrative originally justified it differently.

    Proof sketch (still valid): after n iterations of the outer loop, each value in 0..n-1
    is held by at most one vertex — iteration p ensures uniqueness of value p. -/
    --possible duplicate of tiebreak->orderVertices_n_distinct_ranks
theorem orderVertices_distinct_ranks {n : Nat} (state : PathState) (vts : Array VertexType) :
    let ranks := orderVertices state vts
    ∀ i j : Fin n, i ≠ j → ranks.getD i.val 0 ≠ ranks.getD j.val 0 := by
  sorry

/-- ⚠ **Unreachable in the flawed strategy.** The statement is plausibly true under its
    `hdist` hypothesis, but every attempted proof of `run_swap_invariant` that feeds the
    needed ranks into it goes through `orderVertices_swap_equivariant`, which is false.
    Do not depend on this lemma; the real proof will approach Stage D differently. -/
theorem labelEdges_swap_equivariant {n : Nat}
    (G : AdjMatrix n) (v1 v2 : Fin n) (ranks : Array VertexType)
    (hdist : ∀ i j : Fin n, i ≠ j → ranks.getD i.val 0 ≠ ranks.getD j.val 0) :
    labelEdgesAccordingToRankings (swapVTs v1 v2 ranks) (swapVertexLabels v1 v2 G) =
    labelEdgesAccordingToRankings ranks G := by
  sorry

/-! ## §6  run_swap_invariant -/

/-- Swapping two vertex labels before calling `run` (with all-zero starting types) does not
    change the output.

    ⚠ **Statement is true, but this proof cannot be completed.** It is a consequence of the
    full canonical theorem (any label swap is an isomorphism, so canonical forms agree).
    The sketched derivation below, via `orderVertices_swap_equivariant`, routes through a
    **false** lemma and will therefore stay at `sorry`. The real proof in `FullCorrectness/`
    obtains this as a corollary of Aut-equivariance + tiebreak choice-independence. -/
theorem run_swap_invariant {n : Nat} (G : AdjMatrix n) (v1 v2 : Fin n) :
    run (Array.replicate n 0) (swapVertexLabels v1 v2 G) =
    run (Array.replicate n 0) G := by
  simp only [run]
  -- getArrayRank (replicate n 0): all values equal, every element has rank 0.
  -- Let zeros := Array.replicate n 0.  Note getArrayRank zeros = zeros (proved below as
  -- getArrayRank_zeros, used implicitly here via sorry).
  -- By orderVertices_swap_equivariant with vts = zeros:
  --   orderedRanks' := orderVertices (initializePaths (swapVL G)) zeros
  --                 = orderVertices (initializePaths (swapVL G)) (swapVTs v1 v2 zeros)
  --                      [because swapVTs v1 v2 zeros = zeros by swapVTs_zeros]
  --                 = swapVTs v1 v2 (orderVertices (initializePaths G) zeros)
  --                      [by orderVertices_swap_equivariant]
  --                 =: swapVTs v1 v2 orderedRanks
  -- By labelEdges_swap_equivariant (with distinctness from orderVertices_distinct_ranks):
  --   labelEdgesAccordingToRankings orderedRanks' (swapVL G)
  --   = labelEdgesAccordingToRankings (swapVTs v1 v2 orderedRanks) (swapVL G)
  --   = labelEdgesAccordingToRankings orderedRanks G
  sorry

/-! ## §7  Main theorems -/

/-- Isomorphic graphs produce the same canonical form.

    ⚠ **Statement is the (→) direction of the main theorem and is true**, but this proof
    depends on `run_swap_invariant`, which in turn depends on the false §5 lemma. Effectively
    `sorry`. The corrected proof lives in `FullCorrectness/Main.lean` (planned). -/
theorem run_isomorphic_eq {n : Nat} {G H : AdjMatrix n}
    (h : G ≃ H) :
    run (Array.replicate n 0) G = run (Array.replicate n 0) H := by
  induction h with
  | refl G => rfl
  | swap G v1 v2 => exact (run_swap_invariant G v1 v2).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Graphs with the same canonical form are isomorphic. -/
theorem run_eq_implies_iso {n : Nat} {G H : AdjMatrix n}
    (h : run (Array.replicate n 0) G = run (Array.replicate n 0) H) :
    G ≃ H := by
  -- G ≃ run zeros G  (output is always isomorphic to input)
  have hG : G ≃ run (Array.replicate n 0) G := run_isomorphic_to_input _ G
  -- H ≃ run zeros H
  have hH : H ≃ run (Array.replicate n 0) H := run_isomorphic_to_input _ H
  -- Chain: G ≃ run zeros G = run zeros H ≃⁻¹ H
  rw [h] at hG
  exact hG.trans hH.symm

/-- **Main theorem**: `run` with all-zero vertex inputs is a complete graph-isomorphism invariant.
    Two graphs are isomorphic if and only if `run` maps them to identical adjacency matrices.

    ⚠ **Sorry-reachable.** The (←) direction is genuinely proved (via
    `run_eq_implies_iso`, which only uses the valid §4 result). The (→) direction relies on
    `run_isomorphic_eq` → `run_swap_invariant` → the false §5 lemma. Do not cite this
    theorem as evidence of correctness. The corrected version will appear in
    `FullCorrectness/Main.lean`. -/
theorem run_canonical {n : Nat} (G H : AdjMatrix n) :
    G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H :=
  ⟨run_isomorphic_eq, run_eq_implies_iso⟩

end Graph
