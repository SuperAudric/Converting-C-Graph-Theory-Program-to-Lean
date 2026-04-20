import Mathlib.Tactic
import Aesop
open Nat

namespace Graph
-- I should probably use Mathlib.Combinatorics.SimpleGraph instead of making my own adjacency matrix structure


/-- An adjacency-matrix representation of a graph on `n` vertices. -/
structure AdjMatrix (n : Nat) where
  adj : Fin n → Fin n → Nat
deriving Repr, DecidableEq
namespace AdjMatrix

variable {n : Nat}

/-- Swap two vertices in an adjacency matrix. -/
def swapVertices (i j : Fin n) (G : AdjMatrix n) : AdjMatrix n :=
{ adj := fun u v =>
    let u' := if u = i then j else if u = j then i else u
    let v' := if v = i then j else if v = j then i else v
    G.adj u' v' }

/-! ## Isomorphism -/ --Intentionally based on List.Perm

/--
`Isomorphic G₁ G₂` or `G₁ ≃ G₂` asserts `G₁` and `G₂` are graph-isomorphic.
This is defined inductively by induction using pairwise vertex swaps.
-/

inductive Isomorphic : AdjMatrix n → AdjMatrix n → Prop
  /-- Reflexivity -/
  | refl (G : AdjMatrix n) :
      Isomorphic G G

  /-- A single vertex swap preserves isomorphism -/
  | swap (G : AdjMatrix n) (i j : Fin n) :
      Isomorphic G (swapVertices i j G)

  /-- Transitivity of isomorphism -/
  | trans {G₁ G₂ G₃ : AdjMatrix n} :
      Isomorphic G₁ G₂ →
      Isomorphic G₂ G₃ →
      Isomorphic G₁ G₃

@[inherit_doc] scoped infixl:50 " ≃ " => Isomorphic


/--  Convert the adjacency matrix to a human readable form. -/
def adjToString (G : AdjMatrix n) : String :=
  let rows := List.finRange n
  let rowStrings := rows.map fun i =>
    let row := List.finRange n
    let rowString := row.map fun j =>
      toString (G.adj i j)
    String.join (rowString.intersperse " ")
  String.join (rowStrings.intersperse "\n")


/-- Define the `ToString` instance for `AdjMatrix n` to use `adjToString` automatically. -/
instance : ToString (AdjMatrix n) :=
  ⟨fun G => adjToString G⟩

end AdjMatrix
end Graph
