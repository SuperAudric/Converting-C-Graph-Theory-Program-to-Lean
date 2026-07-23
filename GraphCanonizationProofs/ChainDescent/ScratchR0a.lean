import ChainDescent.Force
import ChainDescent.SelectNode

/-!
R0a core, with the AUGMENTED key. The plain `lookaheadKey` (adjacency-only leaf matrix)
cannot force `σ u = w` (pin untracked) nor colour-preservation (χ dropped). Recording
`(pin-rank, χ-in-rank-order, leaf-matrix)` fixes both. This scratch proves the crux from
the three component-equalities that an augmented key would deliver.
-/

namespace ChainDescent
namespace ScratchR0a

open ChainDescent.Descend
open ChainDescent.Force
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-- **R0a CORE (augmented key).** Given discretizing pins for `u` and `w`, plus the three
equalities an augmented key delivers — equal pin-rank, equal χ-in-rank-order, equal leaf matrix —
there is a **colour-automorphism** taking `u ↦ w`. -/
theorem r0a_core (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (hu : Discrete (lookData adj χ u).col) (hw : Discrete (lookData adj χ w).col)
    -- (c) leaf matrices equal
    (hlm : leafMatrix adj (lookData adj χ u).col = leafMatrix adj (lookData adj χ w).col)
    -- (a) pin ranks equal (as Fin n)
    (hpin : Colouring.rankPerm _ hu u = Colouring.rankPerm _ hw w)
    -- (b) χ agrees in rank order
    (hcol : ∀ i : Fin n, χ ((Colouring.rankPerm _ hu).symm i) = χ ((Colouring.rankPerm _ hw).symm i)) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  -- leaf matrix equality ⟹ labelledAdj equality
  rw [leafMatrix_eq_labelledAdj adj _ hu, leafMatrix_eq_labelledAdj adj _ hw] at hlm
  set πu := Colouring.rankPerm (lookData adj χ u).col hu with hπu
  set πw := Colouring.rankPerm (lookData adj χ w).col hw with hπw
  -- the candidate automorphism
  refine ⟨πw⁻¹ * πu, ⟨?_, ?_⟩, ?_⟩
  · -- adjacency preserved: adj (σ i) (σ j) = adj i j
    intro i j
    have hEq := congrFun (congrFun hlm (πu i)) (πu j)
    simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
    -- hEq : adj i j = adj (πw.symm (πu i)) (πw.symm (πu j))
    change adj.adj (πw.symm (πu i)) (πw.symm (πu j)) = adj.adj i j
    exact hEq.symm
  · -- colour preserved: χ (σ v) = χ v
    intro v
    change χ (πw.symm (πu v)) = χ v
    have := hcol (πu v)
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  · -- σ u = w
    change πw.symm (πu u) = w
    rw [hpin, Equiv.symm_apply_apply]

end ScratchR0a
end ChainDescent
