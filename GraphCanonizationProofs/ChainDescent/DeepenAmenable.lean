import ChainDescent.DeepenR1

/-!
# `C3b` tranche 2, part VI — Layer 1 foundations for `Amenable ⟹ R1`

R1's crux FACTORS (see `DeepenR1` header): `R1 ⟸ (Amenable ⟹ R1) + Amenable`, where `Amenable` says
every deepening level's `chooseIdK` cell is a single orbit of the pointwise-stabilizer of the
individualized-so-far. **Layer 1** (`Amenable ⟹ R1`) is the mechanical **re-relating induction**:

> the deepen-from-`a` and replay-from-`b` descents (`a ~ b` via `σ ∈ Aut`) stay related by an
> automorphism `σₖ ∈ Aut(adj)` with `ψ_b^(k) = transportColouring σₖ ψ_a^(k)`.

Maintained per level: `chooseIdK` picks the same id, so the selected cells are `σₖ`-images; the cell
being single-orbit under `Stab` (= `Amenable`) yields `τ ∈ Stab(ψ_b)` fixing the lowest-index mismatch
`τ (σₖ u_a) = u_b`, and `σₖ₊₁ := τ σₖ` re-establishes the invariant. At discreteness the leaves are
`σ`-related, so `twistOf`'s colour-match IS `σ` on all of `K`, hence the exec twist verifies and
directly reaches `b`.

This file lands the **transport atoms** the induction runs on. The atom is `step_aut`: an automorphism
of the graph transports one individualize+refine step between `σ`-related colourings — the level-to-level
engine. `transportColouring_comp` composes the per-level `σₖ`. (The full induction and the residual
K-coverage obligation — `SameOrbits` is over all vertices, the induction gives the branch cell — build
on these.)
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-- **Transported colourings compose.** `transportColouring σ χ = χ ∘ σ.symm`, so applying `τ` then
`σ`'s transport is the transport by `τ * σ` — this composes the per-level automorphisms `σₖ` the
re-relating induction threads. -/
theorem transportColouring_comp (σ τ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    transportColouring τ (transportColouring σ χ) = transportColouring (τ * σ) χ := by
  funext u
  simp only [transportColouring, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  rfl

/-- **★ THE TRANSPORT ATOM — an automorphism transports one deepening step.** `step_transport`
specialised at a graph-automorphism `σ` (`relabelAdj σ adj = adj`): individualizing `σ v` in the
`σ`-transported colouring and refining equals the `σ`-image of individualizing `v` in `χ` and refining.
No colouring-preservation is needed — the colouring is transported explicitly — so this fires for the
`σₖ` relating the two descents at every level, whatever the current colouring. -/
theorem step_aut {adj : AdjMatrix n} {σ : Equiv.Perm (Fin n)}
    (hadj : relabelAdj σ adj = adj) (χ : Colouring n) (v : Fin n) :
    (step adj (transportColouring σ χ) (σ v)).col
      = transportColouring σ ((step adj χ v).col) := by
  have h := step_transport σ adj χ v
  rw [hadj] at h
  exact h

/-- An `IsColAut` automorphism is in particular a graph-automorphism, so it transports a step; the
current colouring is transported explicitly (this is `step_aut` with the `IsColAut` witness supplying
`relabelAdj σ adj = adj`). -/
theorem step_isColAut {adj : AdjMatrix n} {χ : Colouring n} {σ : Equiv.Perm (Fin n)}
    (hσ : IsColAut adj χ σ) (ψ : Colouring n) (v : Fin n) :
    (step adj (transportColouring σ ψ) (σ v)).col
      = transportColouring σ ((step adj ψ v).col) :=
  step_aut hσ.relabel ψ v

end Deepen
end ChainDescent
