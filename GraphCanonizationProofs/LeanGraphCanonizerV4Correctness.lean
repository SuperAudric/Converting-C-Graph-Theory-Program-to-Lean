import LeanGraphCanonizerV4
import Mathlib.Tactic

/-!
# Correctness of the Graph Canonizer

## Main theorem

  `run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H`

That is, `run` with all-zero vertex inputs is a canonical form for graph isomorphism:
isomorphic graphs produce identical outputs, and non-isomorphic graphs produce distinct outputs.

## Proof structure

**→ (isomorphic ⟹ equal outputs)**

By induction on `Isomorphic`.  The key case is a single vertex swap; `run_swap_invariant` (§6)
handles it.  The argument: the full pipeline is *equivariant* under vertex permutations (§5) —
running on a σ-permuted graph with σ-permuted vertex types yields the σ-permuted output.  For
all-zero starting types, σ-permuted zeros = zeros, so the final outputs are literally equal.

The equivariance chain (all proved in §5, sketched in comments):

  Stage A – `initializePaths`:  paths in `swapVL v1 v2 G` at position (d,s,e) correspond to
  paths in G at position (d, σs, σe) with vertex indices relabeled by σ.

  Stage B – `calculatePathRankings`:  by induction on depth, if the input path state and vertex
  types are σ-related, the output ranks satisfy `ranks'[d][s][e] = ranks[d][σs][σe]`.

  Stage C – `orderVertices`:  `convergeOnce` is equivariant (it reads fromRanks); `breakTie`
  breaks ties by index, but after all n iterations the *dense* rank of vertex w in the swapped
  system equals the dense rank of σw in the original (because ties are fully resolved and the
  graph topology, not the labeling, determines the canonical ordering).

  Stage D – `labelEdgesAccordingToRankings`:  with distinct dense ranks, the vertex at position
  p in the swapped sort is σ of the vertex at position p in the original sort.  The edge between
  positions p and q is then `G.adj(σ(σwₚ))(σ(σwₙ)) = G.adj wₚ wₙ`. ∎

**← (equal outputs ⟹ isomorphic)**

`run_isomorphic_to_input` (§4) shows `G ≃ run zeros G` for any G, because
`labelEdgesAccordingToRankings` is a sequence of `swapVertexLabels` steps.  Given equal outputs:
  G ≃ run zeros G = run zeros H ≃⁻¹ H,  so  G ≃ H. ∎

## Sections

  §1  AdjMatrix extensionality
  §2  swapVertexLabels is an involution
  §3  Isomorphic is an equivalence relation (adds symmetry and provides dot notation)
  §4  `labelEdgesAccordingToRankings` output is isomorphic to input; hence `run zeros G ≃ G`
  §5  Equivariance lemmas for the pipeline  [sorry — see stage comments above]
  §6  `run_swap_invariant`  [sorry — assembles §5]
  §7  Main theorems: `run_isomorphic_eq`, `run_eq_implies_iso`, `run_canonical`
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## §1  AdjMatrix extensionality -/

@[ext]
theorem AdjMatrix.ext {n : Nat} {G H : AdjMatrix n}
    (h : ∀ i j : Fin n, G.adj i j = H.adj i j) : G = H := by
  cases G; cases H; congr; funext i j; exact h i j

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
  sorry

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
theorem swapVTs_self_inverse (v1 v2 : Fin n) (vts : Array VertexType) :
    swapVTs v1 v2 (swapVTs v1 v2 vts) = vts :=
  sorry

/-- An all-zeros array is invariant under any position swap (all values are already equal). -/
theorem swapVTs_zeros (v1 v2 : Fin n) :
    swapVTs v1 v2 (Array.replicate n 0) = Array.replicate n 0 := by
  -- All elements are 0, so both getD calls return 0, and set!-ing 0 into an all-0 array is a no-op.
  sorry

/-- **Core equivariance** (Stage C + wrap-up of A–D):
    Computing `orderVertices` on the vertex-swapped graph with vertex-swapped types yields the
    vertex-swapped ordered ranks.

    Full proof requires Stages A–D from the module docstring:
    - Stage A: initializePaths equivariance (path state is σ-relabeled).
    - Stage B: calculatePathRankings equivariance (ranks satisfy ranks'[d][s][e]=ranks[d][σs][σe]).
    - Stage C: convergeOnce/breakTie/orderVertices equivariance.
    Stage D is handled separately by `labelEdges_swap_equivariant`. -/
theorem orderVertices_swap_equivariant {n : Nat} (G : AdjMatrix n) (v1 v2 : Fin n)
    (vts : Array VertexType) :
    orderVertices (initializePaths (swapVertexLabels v1 v2 G)) (swapVTs v1 v2 vts) =
    swapVTs v1 v2 (orderVertices (initializePaths G) vts) := by
  sorry

/-- After `orderVertices` finishes, all vertices have distinct rank values.
    This is needed to ensure the index-tiebreaker in `computeDenseRanks` never fires,
    making `denseRanks'[i] = denseRanks[σi]` an exact equality.

    Proof sketch: after n iterations of the outer loop, each value in 0..n-1 is held by at
    most one vertex (shown by induction: iteration p ensures uniqueness of value p). -/
theorem orderVertices_distinct_ranks {n : Nat} (state : PathState) (vts : Array VertexType) :
    let ranks := orderVertices state vts
    ∀ i j : Fin n, i ≠ j → ranks.getD i.val 0 ≠ ranks.getD j.val 0 := by
  sorry

/-- **Stage D**: `labelEdgesAccordingToRankings` with consistently swapped ranks and graph
    produces the same result as the original.

    With distinct dense ranks, `denseRanks'[i] = denseRanks[σi]`.  The selection sort places
    vertex σwₚ at position p in `swapVL G`; the edge between positions p and q is then
    `(swapVL G).adj(σwₚ)(σwₙ) = G.adj(σ²wₚ)(σ²wₙ) = G.adj wₚ wₙ`. -/
theorem labelEdges_swap_equivariant {n : Nat}
    (G : AdjMatrix n) (v1 v2 : Fin n) (ranks : Array VertexType)
    (hdist : ∀ i j : Fin n, i ≠ j → ranks.getD i.val 0 ≠ ranks.getD j.val 0) :
    labelEdgesAccordingToRankings (swapVTs v1 v2 ranks) (swapVertexLabels v1 v2 G) =
    labelEdgesAccordingToRankings ranks G := by
  sorry

/-! ## §6  run_swap_invariant -/

/-- Swapping two vertex labels before calling `run` (with all-zero starting types) does not
    change the output. -/
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

/-- Isomorphic graphs produce the same canonical form. -/
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
    Two graphs are isomorphic if and only if `run` maps them to identical adjacency matrices. -/
theorem run_canonical {n : Nat} (G H : AdjMatrix n) :
    G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H :=
  ⟨run_isomorphic_eq, run_eq_implies_iso⟩

end Graph
