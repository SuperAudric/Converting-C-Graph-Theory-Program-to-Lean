import LeanGraphCanonizerV4
import Mathlib.Tactic

/-!
# Shared basics for the full-correctness proof

Small reusable lemmas that would otherwise be duplicated across the correctness files.

Currently holds just `AdjMatrix.ext`. Each step of the `FullCorrectness/` proof imports
this module (transitively or directly); the old `LeanGraphCanonizerV4Correctness.lean`
file also imports it, so the lemma is defined in exactly one place.
-/

namespace Graph
namespace AdjMatrix

/-- Two adjacency matrices are equal iff their adjacency functions agree pointwise. -/
@[ext]
theorem ext {n : Nat} {G H : AdjMatrix n}
    (h : ∀ i j : Fin n, G.adj i j = H.adj i j) : G = H := by
  cases G; cases H; congr; funext i j; exact h i j

end AdjMatrix
end Graph
