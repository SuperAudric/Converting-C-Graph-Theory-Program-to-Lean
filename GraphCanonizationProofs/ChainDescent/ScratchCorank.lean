/-
# Corank-uniform radical bound (increment 3, step 3e-ii — the corank ≥ 2 handling).

`normT_le` bounds `q·‖T‖` by `∑_{y,z} ‖χy‖‖χz‖·√(qᵈ·|radical F_{y,z}|)`, where the per-pair radical
`|radical F_{y,z}|` can in principle be large (corank ≥ 2 members of the pencil `F = y•pairForm_u + z•pairForm_v`).
The clean resolution: **do not stratify by corank.** Every *nonzero* form `F` has a radical that is a PROPER subspace
(`radical = ⊤ ⟺ polar F ≡ 0 ⟺ F = 0` in char ≠ 2), hence `|radical F| · q ≤ |V|` UNIFORMLY — corank 1, 2, or higher
all obey the same proper-subspace bound `|radical| ≤ q^{d-1}`. So a corank-`c` member contributes
`√|radical| ≤ q^{(d-1)/2}` regardless of `c`, and a single Schwartz–Zippel count of degenerate `(y,z)` (≤ `d·q`,
the named shared-with-increment-4 input) bounds the whole degenerate contribution.

This file proves the corank-uniform core:
* `polarRad` — the polar-radical of a quadratic form, as a `Submodule`.
* `polarRad_card_filter` — its `Fintype.card` equals the `Finset.filter` cardinality used in `normT_le`'s RHS.
* `polarRad_ne_top_of_ne_zero` — `F ≠ 0 ⟹ radical proper` (char ≠ 2).
* `radical_card_mul_card_le` — `F ≠ 0 ⟹ |radical F| · q ≤ |V|` (the uniform proper-subspace bound; THE corank ≥ 2 enabler).

NOT in build (scratch; `lake env lean ChainDescent/ScratchCorank.lean`).
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace ChainDescent

open Module

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The polar-radical of a quadratic form `F`, bundled as a submodule:
`{ h | ∀ x, polar F x h = 0 }`. (Right radical of `F.polarBilin`.) -/
def polarRad (F : QuadraticForm K V) : Submodule K V where
  carrier := {h | ∀ x, QuadraticMap.polar F x h = 0}
  zero_mem' := fun x => QuadraticMap.polar_zero_right F x
  add_mem' := by
    intro a b ha hb x
    rw [QuadraticMap.polar_add_right, ha x, hb x, add_zero]
  smul_mem' := by
    intro c a ha x
    rw [QuadraticMap.polar_smul_right, ha x, smul_zero]

@[simp] theorem mem_polarRad {F : QuadraticForm K V} {h : V} :
    h ∈ polarRad F ↔ ∀ x, QuadraticMap.polar F x h = 0 := Iff.rfl

/-- The `Finset.filter` cardinality used in `normT_le`'s RHS equals `Nat.card` of `polarRad F`.
Routed through `Nat.card`/`Set.ncard` (instance-free) to avoid `Fintype`-on-submodule instance mismatches. -/
theorem polarRad_card_filter [Fintype V] [DecidableEq K] (F : QuadraticForm K V) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar F x h = 0)).card
      = Nat.card (polarRad F) := by
  classical
  rw [show Nat.card (polarRad F) = (polarRad F : Set V).ncard from rfl,
    Set.ncard_eq_toFinset_card' (polarRad F : Set V)]
  congr 1
  ext h
  simp only [Set.mem_toFinset, SetLike.mem_coe, mem_polarRad, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- **`F ≠ 0 ⟹ its polar-radical is a PROPER subspace** (char ≠ 2).** If the radical were everything, then
`polar F x x = 0` for all `x`, i.e. `2 • F x = 0`, i.e. `F x = 0` (invertible 2), forcing `F = 0`. -/
theorem polarRad_ne_top_of_ne_zero [Invertible (2 : K)] (F : QuadraticForm K V) (hF : F ≠ 0) :
    polarRad F ≠ ⊤ := by
  intro htop
  apply hF
  have hzero : ∀ x, F x = 0 := by
    intro x
    have hx : QuadraticMap.polar F x x = 0 := by
      have hmem : x ∈ polarRad F := htop ▸ Submodule.mem_top
      exact hmem x
    rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at hx
    exact (mul_eq_zero.1 hx).resolve_left (Invertible.ne_zero (2 : K))
  exact QuadraticMap.ext (fun x => by simp [hzero x])

/-- **The corank-uniform proper-subspace bound (the corank ≥ 2 enabler).** For any NONZERO quadratic form `F`
on a finite space `V` over a finite field `K` (char ≠ 2), `|radical F| · |K| ≤ |V|` — equivalently
`|radical F| ≤ q^{d-1}`, regardless of the corank. -/
theorem radical_card_mul_card_le [Fintype K] [DecidableEq K] [Fintype V] [Invertible (2 : K)]
    (F : QuadraticForm K V) (hF : F ≠ 0) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar F x h = 0)).card * Fintype.card K
      ≤ Fintype.card V := by
  classical
  rw [polarRad_card_filter, ← Nat.card_eq_fintype_card (α := K), ← Nat.card_eq_fintype_card (α := V),
    Module.natCard_eq_pow_finrank (K := K) (V := polarRad F),
    Module.natCard_eq_pow_finrank (K := K) (V := V)]
  have hlt : finrank K (polarRad F) < finrank K V :=
    Submodule.finrank_lt (polarRad_ne_top_of_ne_zero F hF)
  calc Nat.card K ^ finrank K (polarRad F) * Nat.card K
      = Nat.card K ^ (finrank K (polarRad F) + 1) := by rw [pow_succ]
    _ ≤ Nat.card K ^ finrank K V := Nat.pow_le_pow_right Nat.card_pos hlt

end ChainDescent

#print axioms ChainDescent.polarRad_card_filter
#print axioms ChainDescent.polarRad_ne_top_of_ne_zero
#print axioms ChainDescent.radical_card_mul_card_le
