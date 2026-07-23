import ChainDescent.ForcingCircuits

/-!
# P3-F₂ core — the F₂ rigid-solve determinacy (the linear-case engine)

The heart of the F₂ rigid solver (`docs/chain-descent-rigid-seal.md` §8.2 P3-F₂; `IR §11.3`): where 1-WL /
unit-propagation **stalls** on a rigid F₂ residue, full **Gaussian** solving resolves it because a rigid system
has a **unique** solution. This module formalises that determinacy over `ZMod 2`, on the same `rowspace` objects
P1/P2 extract:

* `dotP r x` — the F₂ pairing `∑ᵢ rᵢ xᵢ` (a constraint `r` evaluated at an assignment `x`).
* `IsRigidF2 H` — the constraint matrix has **trivial kernel** (`dim ker = 0`): the only assignment orthogonal to
  every row is `0`. This is the doc's *rigid* condition (`Aut = ker H` on the F₂ layer; rigid ⟺ `dim ker = 0`).
* **`unique_solution_of_rigid`** — a rigid F₂ system `Hx = b` has **at most one** solution. This is *why* Gaussian
  beats the myopic descent: the descent pays `2^{#free}` and stalls (`#free = Θ(n)` on expanders), while the
  unique solution is a single linear solve.

The determinacy is what lets the concrete labelling `gen` (the rest of P3-F₂) read a *canonical* assignment off
the rigid residue; the remaining P3-F₂ work is wiring that unique assignment — under an iso-invariant frame — into
an equivariant `gen` (`RigidSolverSound.GenEquivariant`). `dotP_zero_rowspace` ties rigidity to the extracted
`rowspace H`: orthogonality to the rows extends to the whole row space, so `IsRigidF2` is a property of
`rowspace H` alone (basis-independent).
-/

namespace ChainDescent
namespace RigidSolveF2

open scoped BigOperators
open ChainDescent.ForcingCircuits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **F₂ pairing** — a constraint row `r` evaluated at an assignment `x`: `∑ᵢ rᵢ · xᵢ`. -/
def dotP (r x : ι → ZMod 2) : ZMod 2 := ∑ i, r i * x i

@[simp] theorem dotP_zero_right (r : ι → ZMod 2) : dotP r 0 = 0 := by
  simp [dotP]

theorem dotP_sub (r x y : ι → ZMod 2) : dotP r (x - y) = dotP r x - dotP r y := by
  simp only [dotP, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dotP_add_left (a b x : ι → ZMod 2) : dotP (a + b) x = dotP a x + dotP b x := by
  simp only [dotP, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotP_smul_left (s : ZMod 2) (a x : ι → ZMod 2) : dotP (s • a) x = s * dotP a x := by
  simp only [dotP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Rigidity of the F₂ system** — trivial kernel: the only assignment orthogonal to every row is the zero
assignment (`dim ker = 0`). The F₂-layer form of the residue being *rigid* (`IR §11.3`). -/
def IsRigidF2 (H : Finset (ι → ZMod 2)) : Prop :=
  ∀ x : ι → ZMod 2, (∀ r ∈ H, dotP r x = 0) → x = 0

/-- **★★ The solve determinacy.** A **rigid** F₂ system `Hx = b` has **at most one** solution: two solutions
differ by a kernel element, which rigidity forces to zero. This is the unique-solve that Gaussian delivers where
the unit-propagation descent stalls. -/
theorem unique_solution_of_rigid (H : Finset (ι → ZMod 2)) (b : (ι → ZMod 2) → ZMod 2)
    (hrig : IsRigidF2 H) {x y : ι → ZMod 2}
    (hx : ∀ r ∈ H, dotP r x = b r) (hy : ∀ r ∈ H, dotP r y = b r) : x = y := by
  have hker : ∀ r ∈ H, dotP r (x - y) = 0 := by
    intro r hr
    rw [dotP_sub, hx r hr, hy r hr, sub_self]
  exact sub_eq_zero.mp (hrig (x - y) hker)

/-- **Orthogonality extends to the row space.** If `x` is orthogonal to every row, it is orthogonal to every
codeword of `rowspace H`. Hence `IsRigidF2` is a property of `rowspace H` alone — the extracted object P1/P2
recover — not of any particular row presentation. -/
theorem dotP_zero_rowspace (H : Finset (ι → ZMod 2)) (x : ι → ZMod 2)
    (hx : ∀ r ∈ H, dotP r x = 0) {c : ι → ZMod 2} (hc : c ∈ rowspace H) : dotP c x = 0 := by
  induction hc using Submodule.span_induction with
  | mem r hr => exact hx r (Finset.mem_coe.mp hr)
  | zero => simp [dotP]
  | add a b _ _ ha hb => rw [dotP_add_left, ha, hb, add_zero]
  | smul s a _ ha => rw [dotP_smul_left, ha, mul_zero]

/-- Rigidity depends only on the row **space**: orthogonality to every codeword of `rowspace H` forces `0`. The
`rowspace`-level form of `IsRigidF2`, so the unique-solve determinacy transfers to whatever presentation the
extraction produces. -/
theorem isRigidF2_rowspace (H : Finset (ι → ZMod 2)) (hrig : IsRigidF2 H)
    (x : ι → ZMod 2) (hx : ∀ c ∈ rowspace H, dotP c x = 0) : x = 0 :=
  hrig x (fun r hr => hx r (Submodule.subset_span (Finset.mem_coe.mpr hr)))

end RigidSolveF2
end ChainDescent
