import FullCorrectness.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# §1.1–§1.2  Permutation action on `AdjMatrix`

Sets up `AdjMatrix.permute σ G` as a **left** action of `Equiv.Perm (Fin n)` on adjacency
matrices, and connects it to the existing `swapVertexLabels` via
`swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2)`.

All subsequent correctness modules reason through `permute`, not `swapVertexLabels`.
-/

namespace Graph
open AdjMatrix

variable {n : Nat}

/-! ## §1.1  The permutation action -/

/--
Relabel the vertices of `G` by the permutation `σ`. The use of `σ.symm` makes composition
a left action: `G.permute (σ * τ) = (G.permute τ).permute σ` (see `permute_mul`).
Intuition: `σ` moves the label — the vertex originally at position `i` now sits at `σ i` —
so the edge at the new position `(i, j)` is the edge that was at `(σ⁻¹ i, σ⁻¹ j)`.
-/
def AdjMatrix.permute (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) : AdjMatrix n :=
  { adj := fun i j => G.adj (σ.symm i) (σ.symm j) }

@[simp]
theorem AdjMatrix.permute_adj (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) (i j : Fin n) :
    (G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j) := rfl

/-- Permuting by the identity does nothing. -/
@[simp]
theorem AdjMatrix.permute_one (G : AdjMatrix n) : G.permute 1 = G := by
  apply AdjMatrix.ext
  intro i j
  simp [AdjMatrix.permute]

/-- Permutation action composes as a left action: `(σ * τ) · G = σ · (τ · G)`. -/
theorem AdjMatrix.permute_mul (σ τ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    G.permute (σ * τ) = (G.permute τ).permute σ := by
  apply AdjMatrix.ext
  intro i j
  -- Both sides reduce to `G.adj (τ.symm (σ.symm i)) (τ.symm (σ.symm j))`.
  simp [AdjMatrix.permute, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply]

/-- Permuting by an inverse undoes the original permutation. -/
@[simp]
theorem AdjMatrix.permute_permute_symm (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    (G.permute σ).permute σ⁻¹ = G := by
  rw [← AdjMatrix.permute_mul, inv_mul_cancel, AdjMatrix.permute_one]

@[simp]
theorem AdjMatrix.permute_symm_permute (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    (G.permute σ⁻¹).permute σ = G := by
  rw [← AdjMatrix.permute_mul, mul_inv_cancel, AdjMatrix.permute_one]

/-! ## §1.2  Bridge to `swapVertexLabels` -/

/--
The existing `swapVertexLabels v1 v2 G` is precisely `G.permute (Equiv.swap v1 v2)`. This
lemma is the bridge between the concrete swap-based `Isomorphic` generator and the abstract
permutation action.
-/
theorem swapVertexLabels_eq_permute (G : AdjMatrix n) (v1 v2 : Fin n) :
    swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2) := by
  apply AdjMatrix.ext
  intro i j
  have hsymm : ∀ x : Fin n, (Equiv.swap v1 v2).symm x = Equiv.swap v1 v2 x := fun _ => rfl
  simp only [AdjMatrix.permute_adj, swapVertexLabels, hsymm, Equiv.swap_apply_def]

end Graph
