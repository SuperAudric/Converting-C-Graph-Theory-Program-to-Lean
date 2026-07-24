import ChainDescent.GaugeBridge
import ChainDescent.RigidSolveF2
import Mathlib.GroupTheory.Solvable

/-!
# W2 Tier B — the abelian branch (Γ abelian → `ker H`, reusing `RigidSolveF2`)

Planning doc: `docs/chain-descent-w2-solvability-route.md` §5 (Tier B, abelian branch) + §4a.

The abelian threshold is the base of the solvable target. Two parts:

* **Group level** — `isSolvable_of_carrier_comm`: a **commutative** gauge carrier is **solvable**.
  So the abelian case needs no separate wall; it is the trivial base of `forceSolvable`
  (`abelian ⊊ solvable`, doc §3).
* **F₂ level (the `RigidSolveF2` reuse)** — the abelian gauge is concretely the kernel `kerF2 H`
  of the recovered system `H` (an additive `ZMod 2`-subgroup, abelian by construction), and
  `IsRigidF2 H ⟺ kerF2 H = ⊥` (`isRigidF2_iff_kerF2_eq_bot`): *rigidity = no gauge freedom*. The
  rigid case's solve is the built determinacy `unique_solution_of_rigid`, re-exported here in gauge
  language as `rigid_unique_solve`.

⚠ The correspondence `GaugeContract.carrier ≅ kerF2 H` (multiplicative permutation gauge ≅ additive
F₂ gauge) is the carried `Recover` / `ForcingModel` bridge — NOT proved here. This module supplies
both endpoints: the group-level solvability of an abelian carrier, and the concrete F₂ gauge the
built solver operates over.
-/

namespace ChainDescent
namespace GaugeComplex

open RigidSolveF2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part 1 — abelian gauge ⟹ solvable (group level) -/

/-- **Abelian ⟹ solvable.** A commutative gauge carrier is solvable, so the abelian threshold is
contained in the solvable target: the abelian case is the trivial base of `forceSolvable`, needing
no separate handling. -/
theorem isSolvable_of_carrier_comm {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    (G : GaugeContract adj P χ) (h : ∀ a b : G.carrier, a * b = b * a) :
    IsSolvable G.carrier :=
  isSolvable_of_comm h

/-! ## Part 2 — the F₂ gauge `kerF2 H` (reusing `RigidSolveF2`) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Additivity of the F₂ pairing in the assignment argument. -/
theorem dotP_add_right (r a b : ι → ZMod 2) : dotP r (a + b) = dotP r a + dotP r b := by
  simp only [dotP, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The **F₂ gauge** of a recovered system `H`: the kernel `{x : ∀ r ∈ H, dotP r x = 0}` as an
additive subgroup of `ι → ZMod 2`, abelian by construction. In the abelian/CFI case `Γ ≅ kerF2 H`
(the correspondence is the carried `Recover` bridge); this is the concrete gauge the built rigid
solver works over. -/
def kerF2 (H : Finset (ι → ZMod 2)) : AddSubgroup (ι → ZMod 2) where
  carrier := {x | ∀ r ∈ H, dotP r x = 0}
  zero_mem' := by intro r _; exact dotP_zero_right r
  add_mem' := by intro a b ha hb r hr; rw [dotP_add_right, ha r hr, hb r hr, add_zero]
  neg_mem' := by
    intro a ha r hr
    have h := dotP_sub r 0 a
    rwa [zero_sub, dotP_zero_right, ha r hr, sub_zero] at h

@[simp] theorem mem_kerF2 {H : Finset (ι → ZMod 2)} {x : ι → ZMod 2} :
    x ∈ kerF2 H ↔ ∀ r ∈ H, dotP r x = 0 := Iff.rfl

/-- **`IsRigidF2` = the F₂ gauge is trivial.** Rigidity of the recovered system is exactly "no gauge
freedom": the kernel is `⊥`. Ties `RigidSolveF2.IsRigidF2` to this track's gauge language. -/
theorem isRigidF2_iff_kerF2_eq_bot (H : Finset (ι → ZMod 2)) :
    IsRigidF2 H ↔ kerF2 H = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  exact ⟨fun hrig x hx => hrig x hx, fun h x hx => h x hx⟩

/-- The abelian branch's **solve**, in gauge language: a **rigid** system (trivial F₂ gauge) has a
unique solution — the built `RigidSolveF2.unique_solution_of_rigid` re-exported. So on the abelian
branch, `IsRigidF2` (no gauge) ⟹ the labelling is determined; a nontrivial `kerF2 H` is the gauge
freedom to solve/quotient. -/
theorem rigid_unique_solve (H : Finset (ι → ZMod 2)) (b : (ι → ZMod 2) → ZMod 2)
    (hrig : IsRigidF2 H) {x y : ι → ZMod 2}
    (hx : ∀ r ∈ H, dotP r x = b r) (hy : ∀ r ∈ H, dotP r y = b r) : x = y :=
  unique_solution_of_rigid H b hrig hx hy

--#print axioms isSolvable_of_carrier_comm
--#print axioms isRigidF2_iff_kerF2_eq_bot
--#print axioms rigid_unique_solve

end GaugeComplex
end ChainDescent
