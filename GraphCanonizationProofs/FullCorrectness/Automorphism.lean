import FullCorrectness.Permutation
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# §1.3–§1.6  Automorphism group and vertex orbits

Defines `Aut G` as a `Subgroup (Equiv.Perm (Fin n))`, vertex orbits under `Aut G`, and
packages same-orbit as a `Setoid` (so orbits partition `Fin n` automatically).

Downstream modules (Equivariance, Tiebreak) reason about `Aut(G)`-invariance of the
canonizer pipeline; this module supplies the group-theoretic vocabulary.
-/

namespace Graph
open AdjMatrix

variable {n : Nat}

/-! ## §1.3  The automorphism group `Aut G` -/

/--
The automorphism group of `G`: permutations that leave `G` invariant under relabeling.
Equivalently (see `mem_Aut_iff_adj`): permutations `σ` with `G.adj (σ⁻¹ i) (σ⁻¹ j) = G.adj i j`
for all `i, j`. These are the symmetries the canonizer cannot and should not distinguish.
-/
def AdjMatrix.Aut (G : AdjMatrix n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | G.permute σ = G }
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq] at *
    rw [AdjMatrix.permute_mul, hτ, hσ]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact AdjMatrix.permute_one G
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq] at *
    calc G.permute σ⁻¹
        = (G.permute σ).permute σ⁻¹ := by rw [hσ]
      _ = G := AdjMatrix.permute_permute_symm σ G

theorem mem_Aut_iff {σ : Equiv.Perm (Fin n)} {G : AdjMatrix n} :
    σ ∈ G.Aut ↔ G.permute σ = G := Iff.rfl

/-- Characterization of `Aut` via the adjacency function. -/
theorem mem_Aut_iff_adj {σ : Equiv.Perm (Fin n)} {G : AdjMatrix n} :
    σ ∈ G.Aut ↔ ∀ i j, G.adj (σ.symm i) (σ.symm j) = G.adj i j := by
  constructor
  · intro h i j
    have := congrArg (fun (H : AdjMatrix n) => H.adj i j) h
    simpa [AdjMatrix.permute] using this
  · intro h
    apply AdjMatrix.ext
    intro i j
    simp [AdjMatrix.permute, h]

/-! ## §1.4  Vertex orbits -/

/-- The `Aut(G)`-orbit of a vertex `v`: all vertices reachable from `v` by an automorphism. -/
def AdjMatrix.orbit (G : AdjMatrix n) (v : Fin n) : Set (Fin n) :=
  { w | ∃ σ ∈ G.Aut, σ v = w }

theorem mem_orbit_iff {G : AdjMatrix n} {v w : Fin n} :
    w ∈ G.orbit v ↔ ∃ σ ∈ G.Aut, σ v = w := Iff.rfl

/-! ## §1.5  Same-orbit is an equivalence relation -/

theorem AdjMatrix.mem_orbit_self (G : AdjMatrix n) (v : Fin n) : v ∈ G.orbit v :=
  ⟨1, G.Aut.one_mem, by simp⟩

theorem AdjMatrix.mem_orbit_symm {G : AdjMatrix n} {v w : Fin n} (h : w ∈ G.orbit v) :
    v ∈ G.orbit w := by
  obtain ⟨σ, hσ, hσv⟩ := h
  refine ⟨σ⁻¹, G.Aut.inv_mem hσ, ?_⟩
  have : σ⁻¹ (σ v) = v := by simp
  rw [← hσv]; exact this

theorem AdjMatrix.mem_orbit_trans {G : AdjMatrix n} {u v w : Fin n}
    (huv : v ∈ G.orbit u) (hvw : w ∈ G.orbit v) : w ∈ G.orbit u := by
  obtain ⟨σ, hσ, hσu⟩ := huv
  obtain ⟨τ, hτ, hτv⟩ := hvw
  refine ⟨τ * σ, G.Aut.mul_mem hτ hσ, ?_⟩
  rw [Equiv.Perm.mul_apply, hσu, hτv]

/-- Same-orbit is an equivalence relation on vertices; its classes are the `Aut(G)`-orbits,
which therefore partition `Fin n`. -/
def AdjMatrix.orbitSetoid (G : AdjMatrix n) : Setoid (Fin n) where
  r v w := w ∈ G.orbit v
  iseqv :=
    { refl  := G.mem_orbit_self
      symm  := AdjMatrix.mem_orbit_symm
      trans := AdjMatrix.mem_orbit_trans }

/-! ## §1.6  Characterization used downstream -/

/-- If `σ ∈ Aut G`, then `σ` maps each orbit to itself. The form downstream modules
consume: "any automorphism sends `v` to another vertex in its orbit." -/
theorem AdjMatrix.orbit_stable_under_Aut {G : AdjMatrix n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ G.Aut) (v : Fin n) : σ v ∈ G.orbit v :=
  ⟨σ, hσ, rfl⟩

theorem AdjMatrix.exists_Aut_of_mem_orbit {G : AdjMatrix n} {v w : Fin n}
    (h : w ∈ G.orbit v) : ∃ σ ∈ G.Aut, σ v = w := h

end Graph
