import ChainDescent.RigidSolverSound
import ChainDescent.RigidFrame

/-!
# `gen` sub-brick (D) — read the labelling: `rankPerm` of the refined colouring

The final layer of the concrete rigid labelling `gen`. Bricks (A)–(C) built and canonicalised the χ-framed F₂
RREF; (D) turns it into the actual permutation P3-Sound's `emitLabel` consumes, and closes the equivariance.

**The construction.** The RREF solve refines χ to a finer colouring `ref adj χ` (χ, plus each vertex's canonical
solved F₂ value). On the linear residue this refinement is **discrete** (the solve breaks every gauge tie), and
then the canonical labelling is simply its rank permutation:

  `genOfRef ref adj χ _ := if Discrete (ref adj χ) then some (rankPerm (ref adj χ)) else none`.

It **ignores the pin `v`** — a whole-graph canonical labelling suffices, because `ptForm`'s pin component
`(π v).val` already separates the pinned vertex (its rank), so `skOf (emitLabel (genOfRef ref))` distinguishes
every branch pair once `ref` is discrete.

**The equivariance (the point of (D)).** `rankPerm` transports as a right-multiplication by `σ⁻¹`
(`rankPerm_transport`, from `vertexRank_transport`) — which is *exactly* `GenEquivariant`'s shape. So
`GenEquivariant (genOfRef ref)` reduces to **`RefEquivariant ref`** (the refinement transports), and nothing
else. Composed with P3-Sound (`keyEquivariant_compKey_emitLabel`), the **entire `①` obligation of the rigid
`compKey` closes on `RefEquivariant ref` alone**. And `RefEquivariant` for the concrete χ-frame refinement is
what (C)'s `RigidFrame.framedRREF_transport` reduces to the (carried) extraction transport. `hemit` reduces to
`ref` discretizing on the residue (`emit_isSome_genOfRef`), carried per-family.

So after (A)–(D): the rigid linear `①`/`②` is `RefEquivariant ref` (⟸ carried extraction transport, via C) +
`ref` discrete on the residue (⟸ the solve discretizes, carried per-family). The pure-F₂ / RREF / frame /
labelling layers owe **nothing** further.
-/

namespace ChainDescent
namespace RigidGen

open ChainDescent.Descend
open ChainDescent.RigidSolver
open ChainDescent.Force
open ChainDescent.RigidSeal
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-- The refinement is equivariant: refining the σ-relabelled graph gives the σ-transport of the refinement. -/
def RefEquivariant (ref : AdjMatrix n → Colouring n → Colouring n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    ref (relabelAdj σ adj) (transportColouring σ χ) = transportColouring σ (ref adj χ)

/-- **`gen` from a refinement.** The canonical labelling = `rankPerm` of χ refined by the solve (`ref adj χ`),
when discrete; else flag. Ignores the pin `v`. Noncomputable (the `①` proof needs no executability). -/
noncomputable def genOfRef (ref : AdjMatrix n → Colouring n → Colouring n) :
    AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n)) :=
  fun adj χ _ => if h : Discrete (ref adj χ) then some (Colouring.rankPerm (ref adj χ) h) else none

/-- `rankPerm` transports as a right-multiplication by `σ⁻¹` — the `GenEquivariant` shape, from
`vertexRank_transport`. -/
theorem rankPerm_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (h : Discrete χ)
    (h' : Discrete (transportColouring σ χ)) :
    Colouring.rankPerm (transportColouring σ χ) h' = Colouring.rankPerm χ h * σ⁻¹ := by
  apply Equiv.ext
  intro u
  rw [Colouring.rankPerm_apply, Equiv.Perm.mul_apply, Colouring.rankPerm_apply]
  have hv := vertexRank_transport σ χ (σ.symm u)
  rw [Equiv.apply_symm_apply] at hv
  exact hv

/-- **★★ (D) — the labelling read is equivariant.** If the refinement transports (`RefEquivariant`), the
`rankPerm`-of-refinement labelling satisfies `GenEquivariant`. All of the rigid `①`'s equivariance is thereby
reduced to the refinement transporting. -/
theorem genEquivariant_genOfRef (ref : AdjMatrix n → Colouring n → Colouring n)
    (href : RefEquivariant ref) : GenEquivariant (genOfRef ref) := by
  intro σ adj χ v
  simp only [genOfRef, href σ adj χ]
  by_cases h : Discrete (ref adj χ)
  · have h' : Discrete (transportColouring σ (ref adj χ)) := (discrete_transport σ (ref adj χ)).mpr h
    rw [dif_pos h', dif_pos h, Option.map_some]
    exact congrArg some (rankPerm_transport σ (ref adj χ) h h')
  · have h' : ¬ Discrete (transportColouring σ (ref adj χ)) :=
      fun hc => h ((discrete_transport σ (ref adj χ)).mp hc)
    rw [dif_neg h', dif_neg h, Option.map_none]

/-- The emit is `some` exactly when the refinement is discrete — so `hemit` (no-flag on the linear residue)
reduces to `ref` discretizing there (carried per-family: the RREF solve refines χ to a discrete colouring on
the F₂-linear residue). -/
theorem emit_isSome_genOfRef (ref : AdjMatrix n → Colouring n → Colouring n)
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) (h : Discrete (ref adj χ)) :
    (emitLabel (genOfRef ref) adj χ v).isSome := by
  simp only [emitLabel, genOfRef, dif_pos h, Option.map_some, Option.isSome_some]

/-- **★★★ (D) capstone.** The whole `compKey` `①` obligation closes on `RefEquivariant ref` alone: compose the
labelling-read equivariance with P3-Sound's `keyEquivariant_compKey_emitLabel`. -/
theorem keyEquivariant_compKey_genOfRef (ref : AdjMatrix n → Colouring n → Colouring n)
    (href : RefEquivariant ref) :
    KeyEquivariant (compKey (skOf (emitLabel (genOfRef ref)))) :=
  keyEquivariant_compKey_emitLabel (genOfRef ref) (genEquivariant_genOfRef ref href)

/-- **★★★ (D) firing capstone.** `NodeResolved` on any rigid cell where the refinement is discrete — soundness
is free (P3-Sound), so the only hypotheses are `ref` discrete (⟹ `hemit`) and the cell being rigid. Closes the
rigid force branch on `RefDiscrete` + rigidity. -/
theorem nodeResolved_compKey_genOfRef (ref : AdjMatrix n → Colouring n → Colouring n)
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hdisc : ∀ u ∈ branches χ, ¬ Discrete (lookData adj χ u).col → Discrete (ref adj χ))
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel (genOfRef ref)))) S adj χ :=
  nodeResolved_compKey_emitLabel (genOfRef ref) S adj χ hnd
    (fun u hu hnu => emit_isSome_genOfRef ref adj χ u (hdisc u hu hnu)) hrigid

end RigidGen
end ChainDescent
