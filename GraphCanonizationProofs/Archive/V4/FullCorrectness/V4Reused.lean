import LeanGraphCanonizerV4
import FullCorrectness.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Distilled remnants of the abandoned `LeanGraphCanonizerV4Correctness.lean`

The original `LeanGraphCanonizerV4Correctness.lean` was a flat correctness proof
built on a false premise (`orderVertices_swap_equivariant`). The proof was
retired; the corrected proof lives in `FullCorrectness/`. A small number of
lemmas in the flat file were genuinely proved and still load-bearing for
`FullCorrectness/Main.lean`'s (⇐) direction. They are reproduced here:

- `swapVertexLabels_self_inverse`  — concrete swap fact (§2)
- `swapVertexLabels_comm`          — concrete swap fact (§2)
- `AdjMatrix.Isomorphic.symm`      — `≃` is an equivalence relation (§3)
- `labelEdgesAccordingToRankings_isomorphic` — `G ≃ labelEdges vts G` (§4)
- `run_isomorphic_to_input`        — `G ≃ run vts G` (§4)
- `run_eq_implies_iso`             — (⇐) direction of canonical theorem (§7,
                                      genuinely proved via §4 + transitivity)

Everything in the original §5/§6/§7 that *wasn't* genuinely proved (the false
`orderVertices_swap_equivariant`, `run_swap_invariant` with unreachable proof,
etc.) is dropped — see git history for the original text. The accompanying
`swapVTs`/`swapVTs_self_inverse`/`swapVTs_zeros` were stepping-stones for the
false lemma and not used elsewhere, so they are also dropped.
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## §2 — swapVertexLabels is an involution -/

/-- The conditional-swap function `fun x => if x=v1 then v2 else if x=v2 then v1 else x` is
    an involution: applying it twice returns the original value. -/
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

/-! ## §3 — Isomorphic is an equivalence relation -/

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

/-! ## §4 — `labelEdgesAccordingToRankings` output is isomorphic to input -/

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

/-! ## §7 — (⇐) direction of the canonical theorem -/

/-- Graphs with the same canonical form are isomorphic. The (⇐) direction of
    `FullCorrectness.run_canonical_correctness` reuses this verbatim. -/
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

end Graph
