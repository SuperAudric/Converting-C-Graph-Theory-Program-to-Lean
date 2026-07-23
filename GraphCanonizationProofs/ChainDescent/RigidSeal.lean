import ChainDescent.Force
import ChainDescent.SelectNode

/-!
# The rigid seal — R0a: force separates non-automorphic pairs on the discretizing regime

The clean, wall-free core of Algorithm R's Lean build. On the **discretizing regime** (individualizing a
branch vertex refines to a discrete colouring), an augmented force key **`leafColKey`** — recording the
canonical `(pin-rank, χ-in-rank-order, leaf-matrix)` — is a *complete* invariant of the coloured-pointed
graph, so two branch vertices attain equal keys **iff** a colour-automorphism carries one to the other. Hence
`leafColKey` separates exactly the non-automorphic pairs (`RigidResolved`), discharging `NodeResolved` on the
discretizing regime.

⚠ The plain `Force.lookaheadKey` (adjacency-only leaf matrix) is **insufficient**: equal keys give only a
*graph* automorphism, with no `σ u = w` (the pin is not at a canonical rank) and no χ-preservation. `leafColKey`
is the strictly-stronger, still-polynomial, still-equivariant upgrade the rigid-seal doc anticipates ("the
solver replaces `lookaheadKey` with a stronger key"). This is R0a's realigned target: it feeds `HandledS` via
`answersS_of_handledS` (`SelectNode.lean`).
-/

namespace ChainDescent
namespace RigidSeal

open ChainDescent.Descend
open ChainDescent.Force
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-! ## 1. The augmented force key -/

/-- **The coloured leaf key.** On the discretizing branch, rank `v` by the complete coloured-pointed invariant
`(pin-rank, χ-in-rank-order, leaf-matrix)`; otherwise fall back to the cell-size histogram (as `lookaheadKey`). -/
def leafColKey : Key n := fun adj χ v =>
  let ψ : Colouring n := (lookData adj χ v).col
  ((if Discrete ψ then
      1 :: (Colouring.vertexRank ψ v).val
        :: ((List.finRange n).map (fun i => χ (rankInv ψ i)) ++ flatten (leafMatrix adj ψ))
    else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)),
   CostModel.WarmRefine.warmRefineCost n + n * n)

@[simp] theorem keyV_leafColKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (leafColKey (n := n)) adj χ v =
      (let ψ : Colouring n := (lookData adj χ v).col
       if Discrete ψ then
         1 :: (Colouring.vertexRank ψ v).val
           :: ((List.finRange n).map (fun i => χ (rankInv ψ i)) ++ flatten (leafMatrix adj ψ))
       else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)) := rfl

/-- The look-ahead colouring's cost — one refinement plus `n²`, charged like `lookaheadKey`. -/
theorem keyCost_leafColKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (leafColKey (n := n)) adj χ v = CostModel.WarmRefine.warmRefineCost n + n * n := rfl

/-! ## 2. `rankInv` transports (the χ-in-rank-order equivariance atom) -/

/-- **`rankInv` transports**: the rank-`i` vertex of the relabelled discrete colouring is `σ` of the rank-`i`
vertex of the original. Direct from `vertexRank`-injectivity and `vertexRank_transport`. -/
theorem rankInv_transport (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) (h : Discrete ψ) (i : Fin n) :
    rankInv (transportColouring σ ψ) i = σ (rankInv ψ i) := by
  have h' : Discrete (transportColouring σ ψ) := (discrete_transport σ ψ).mpr h
  rw [rankInv_eq_symm (transportColouring σ ψ) h' i, rankInv_eq_symm ψ h i]
  apply (Colouring.rankPerm (transportColouring σ ψ) h').injective
  rw [Equiv.apply_symm_apply, Colouring.rankPerm_apply, vertexRank_transport,
      ← Colouring.rankPerm_apply ψ h, Equiv.apply_symm_apply]

/-! ## 3. R0a core — equal augmented keys ⟹ a colour-automorphism `u ↦ w` -/

/-- **R0a CORE.** Given discretizing pins for `u`, `w` plus the three component-equalities the augmented key
delivers — equal leaf matrix, equal pin-rank, equal χ-in-rank-order — there is a **colour-automorphism** of
`(adj, χ)` taking `u ↦ w`. -/
theorem r0a_core (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (hu : Discrete (lookData adj χ u).col) (hw : Discrete (lookData adj χ w).col)
    (hlm : leafMatrix adj (lookData adj χ u).col = leafMatrix adj (lookData adj χ w).col)
    (hpin : Colouring.rankPerm _ hu u = Colouring.rankPerm _ hw w)
    (hcol : ∀ i : Fin n,
      χ ((Colouring.rankPerm _ hu).symm i) = χ ((Colouring.rankPerm _ hw).symm i)) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  rw [leafMatrix_eq_labelledAdj adj _ hu, leafMatrix_eq_labelledAdj adj _ hw] at hlm
  set πu := Colouring.rankPerm (lookData adj χ u).col hu with hπu
  set πw := Colouring.rankPerm (lookData adj χ w).col hw with hπw
  refine ⟨πw⁻¹ * πu, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    have hEq := congrFun (congrFun hlm (πu i)) (πu j)
    simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
    change adj.adj (πw.symm (πu i)) (πw.symm (πu j)) = adj.adj i j
    exact hEq.symm
  · intro v
    change χ (πw.symm (πu v)) = χ v
    have := hcol (πu v)
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  · change πw.symm (πu u) = w
    rw [hpin, Equiv.symm_apply_apply]

/-! ## 4. `leafColKey` is equivariant -/

theorem keyEquivariant_leafColKey : KeyEquivariant (leafColKey (n := n)) := by
  intro σ adj χ v
  rw [keyV_leafColKey, keyV_leafColKey]
  simp only [lookData_col_transport σ adj χ v]
  by_cases hd : Discrete ((lookData adj χ v).col)
  · rw [if_pos ((discrete_transport σ _).mpr hd), if_pos hd]
    have hpin : Colouring.vertexRank (transportColouring σ (lookData adj χ v).col) (σ v)
        = Colouring.vertexRank (lookData adj χ v).col v := vertexRank_transport σ _ v
    have hcolord :
        (List.finRange n).map
            (fun i => transportColouring σ χ (rankInv (transportColouring σ (lookData adj χ v).col) i))
          = (List.finRange n).map (fun i => χ (rankInv (lookData adj χ v).col i)) := by
      apply List.map_congr_left
      intro i _
      rw [rankInv_transport σ _ hd i]
      show transportColouring σ χ (σ (rankInv (lookData adj χ v).col i))
        = χ (rankInv (lookData adj χ v).col i)
      simp [transportColouring]
    rw [hpin, hcolord, leafMatrix_transport σ adj _ hd]
  · rw [if_neg (fun hc => hd ((discrete_transport σ _).mp hc)), if_neg hd]
    exact congrArg (0 :: ·) (List.map_congr_left (fun c _ =>
      cellOf_card_transport σ ((lookData adj χ v).col) c.val))

/-! ## 5. The completeness step — equal `leafColKey` values ⟹ a colour-automorphism -/

/-- **★ EQUAL KEYS ⟹ AUTOMORPHIC (discretizing regime).** If `u` and `w` both discretize on individualization
and attain the same `leafColKey` value, a colour-automorphism of `(adj, χ)` carries `u ↦ w`. The three key
components decompose to exactly `r0a_core`'s hypotheses. -/
theorem colAut_of_leafColKey_eq (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (hu : Discrete (lookData adj χ u).col) (hw : Discrete (lookData adj χ w).col)
    (hkey : keyV (leafColKey (n := n)) adj χ u = keyV (leafColKey (n := n)) adj χ w) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  rw [keyV_leafColKey, keyV_leafColKey] at hkey
  simp only [if_pos hu, if_pos hw] at hkey
  obtain ⟨_, htail⟩ := List.cons.inj hkey
  obtain ⟨hrank, hrest⟩ := List.cons.inj htail
  have hlen : ((List.finRange n).map (fun i => χ (rankInv (lookData adj χ u).col i))).length
      = ((List.finRange n).map (fun i => χ (rankInv (lookData adj χ w).col i))).length := by simp
  obtain ⟨hχo, hflat⟩ := List.append_inj hrest hlen
  have hlm : leafMatrix adj (lookData adj χ u).col = leafMatrix adj (lookData adj χ w).col :=
    flatten_injective hflat
  have hpin : Colouring.rankPerm _ hu u = Colouring.rankPerm _ hw w := by
    rw [Colouring.rankPerm_apply, Colouring.rankPerm_apply]; exact Fin.ext hrank
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map] at hχo
  have hcolfun := List.ofFn_inj.mp hχo
  have hcol : ∀ i, χ ((Colouring.rankPerm _ hu).symm i) = χ ((Colouring.rankPerm _ hw).symm i) := by
    intro i
    rw [← rankInv_eq_symm _ hu, ← rankInv_eq_symm _ hw]
    exact congrFun hcolfun i
  exact r0a_core adj χ u w hu hw hlm hpin hcol

/-! ## 6. `RigidResolved` — force separates every non-automorphic branch pair -/

/-- **The rigid-seam predicate (§4).** *Force distinguishes every non-automorphic branch pair.* -/
def RigidResolved (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
    keyV key adj χ u ≠ keyV key adj χ w

/-- **★★ R0a — `leafColKey` DISCHARGES `RigidResolved` on the discretizing regime** (no wall). Contrapositive of
`colAut_of_leafColKey_eq`: equal keys would furnish the very colour-automorphism a non-automorphic pair rules
out. -/
theorem rigidResolved_leafColKey (adj : AdjMatrix n) (χ : Colouring n)
    (hdisc : ∀ v ∈ branches χ, Discrete (lookData adj χ v).col) :
    RigidResolved (leafColKey (n := n)) adj χ := by
  intro u hu w hw hrig hkey
  obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w (hdisc u hu) (hdisc w hw) hkey
  exact hrig σ hσ hσuw

/-! ## 7. Wiring to `NodeResolved` — a rigid discretizing cell is handled by force -/

/-- **★★★ R0a → `NodeResolved`.** On a **rigid discretizing** branch cell — every branch vertex discretizes on
individualization, and no two distinct branch vertices are colour-automorphic — `leafColKey` separates the whole
cell, so the fused node resolves (`Select.NodeResolved`). This is regime (1) rigid: it feeds `HandledS` via
`Select.answersS_of_handledS`, no wall. -/
theorem nodeResolved_leafColKey_of_rigid_discretizing (S : Consume.Supply n) (adj : AdjMatrix n)
    (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hdisc : ∀ v ∈ branches χ, Discrete (lookData adj χ v).col)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (leafColKey (n := n)) S adj χ := by
  refine Select.nodeResolved_of_cellResolved hnd (Or.inr ?_)
  intro u hu w hw hkey
  by_contra hne
  obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w (hdisc u hu) (hdisc w hw) hkey
  exact hrigid u hu w hw hne σ hσ hσuw

end RigidSeal
end ChainDescent
