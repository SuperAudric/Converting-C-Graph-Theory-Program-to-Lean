/-
# WL-visibility of group structure — the algebraic cores (early de-risk build)

Scoping the Lean formalization of the WL-visibility dichotomy found empirically by
`NonAbelianCfiProbe` (memory `project_nonabelian_cfi_witness_2026-06-28`):

  * the standard CFI / multipede gadget (relation `g₁·…·g_d = 1`) is **1-WL-BLIND**
    to the group structure (S₃ ≡ Z₆), because the relation is *coordinate-regular*
    (a perfect quasigroup) — fixing one coordinate leaves a count independent of the
    value AND of the group;
  * a **commutator / commuting-pairs gadget is 1-WL-VISIBLE** — the commuting-degree
    `|C(g)|` varies with `g` exactly when the group is non-abelian, so colour
    refinement splits by centralizer size.

This file fixes the two *algebraic hearts* of that dichotomy (pure group theory,
Mathlib-direct), separable from the graph-encoding plumbing. They are the load-bearing
facts the full WL-visibility theorems will consume; building them first de-risks the
doc (per the standing steer: fix early stages before writing the plan up).

NOT in build (`lake env lean` scratch). Axiom target `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Push

namespace WLVis

/-! ## Blindness heart — the product gadget is coordinate-regular -/

/-- **Coordinate-regularity (degree 3).** Fixing the first coordinate to ANY `a`,
the number of completing pairs `(y, z)` with `a·y·z = 1` is `|G|`, independent of
`a` and of whether `G` is abelian. This uniform "fix-one-coordinate ⟹ `|G|^{d-2}`
completions" is the perfect-quasigroup property of the relation `g₁g₂g₃ = 1`, and is
the *source* of 1-WL's blindness: every value-vertex of a segment sees the same
number of gadget-tuples, so colour refinement never splits a segment cell — for any
group. -/
theorem product_coord_regular {G : Type*} [Group G] [Fintype G] [DecidableEq G] (a : G) :
    Fintype.card {p : G × G // a * p.1 * p.2 = 1} = Fintype.card G :=
  Fintype.card_eq.mpr ⟨{
    toFun := fun p => p.1.1
    invFun := fun y => ⟨(y, (a * y)⁻¹), by rw [mul_inv_cancel]⟩
    left_inv := by
      rintro ⟨⟨y, z⟩, h⟩
      have hz : z = (a * y)⁻¹ := eq_inv_of_mul_eq_one_right h
      simp [hz]
    right_inv := fun y => rfl }⟩

/-- The same count, stated as *independence of the fixed value* (what blindness
literally needs: all values of a segment are interchangeable to 1-WL). -/
theorem product_coord_regular_indep {G : Type*} [Group G] [Fintype G] [DecidableEq G] (a a' : G) :
    Fintype.card {p : G × G // a * p.1 * p.2 = 1}
      = Fintype.card {p : G × G // a' * p.1 * p.2 = 1} := by
  rw [product_coord_regular, product_coord_regular]

/-! ## Degree-2 coordinate-regularity — the kernel for ≥2-WL blindness

`product_coord_regular` is *fix-one* coordinate-regularity (the 1-WL count: fixing one
coordinate of `t₀·t₁·t₂ = 1` leaves `|G|` completions). The coherent configuration that
hidden symmetry lives in is `≥2`-WL, which counts completions with *two* coordinates
fixed. For the minimal `d = 3` gadget that count is the kernel below: fixing any two of
the three ordered coordinates leaves a **linear equation `u · z · w = 1` in the third**,
whose solution `z = u⁻¹ · w⁻¹` is **unique** — count `= 1`, independent of the fixed
values `u, w` and of `G`. This is exactly the `Γ`-blindness a 2-WL pair-refinement needs
on the minimal gadget; it is the d=3 instance of "fix all-but-one coordinate of an
ordered product ⟹ the last is determined", the noncommutative quasigroup law one degree
up from `product_coord_regular`.

(The general-`d` *aggregate* `#{t : Fin d → G // ∏ t = 1 ∧ t k = a} = |G|^{d−2}`,
independent of `a`, follows from this kernel by a `List.ofFn`-product splitting + counting
wrapper; it is the R2 / full-multipede extension and is deferred — the minimal gadget needs
only the kernel.) -/

/-- **Degree-2 coordinate-regularity (the kernel).** The solution set of the linear
equation `u · z · w = 1` is a singleton (`z = u⁻¹ · w⁻¹`); hence its cardinality is `1`,
independent of `u`, `w`, and `G`. Fixing any two of the three coordinates of
`t₀·t₁·t₂ = 1` instantiates this (with `(u, w)` the surrounding fixed factors), so every
fix-two completion count on the minimal product gadget is `1` — `Γ`-blind. -/
theorem linear_eq_unique {G : Type*} [Group G] [Fintype G] [DecidableEq G] (u w : G) :
    Fintype.card {z : G // u * z * w = 1} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨u⁻¹ * w⁻¹, ?_⟩, ?_⟩
  · rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel]
  · rintro ⟨z, hz⟩
    refine Subtype.ext ?_
    have h2 : u * z = w⁻¹ := mul_eq_one_iff_eq_inv.mp hz
    exact eq_inv_mul_iff_mul_eq.mpr h2

/-- Fix-two completion counts on the minimal `d = 3` product gadget `t₀·t₁·t₂ = 1`
agree across all three coordinate pairs and all fixed values — each is `1`
(`linear_eq_unique`), so a 2-WL pair-refinement sees the same count regardless of `G`.
This is the degree-2 analogue of `product_coord_regular_indep`. -/
theorem product_fix_two_indep {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (a b a' b' : G) :
    Fintype.card {z : G // a * z * b = 1} = Fintype.card {z : G // a' * z * b' = 1} := by
  rw [linear_eq_unique, linear_eq_unique]

/-! ## Visibility heart — the commuting-degree separates abelian from non-abelian -/

/-- The **commuting-degree** of `g`: the number of elements commuting with `g`
(`= |C(g)|`). This is exactly the 1-WL degree of `g`'s value-vertex in a
commuting-pairs gadget (connect `a`–`b` iff `ab = ba`). -/
noncomputable def commDeg {G : Type*} [Group G] [Fintype G] [DecidableEq G] (g : G) : ℕ :=
  Fintype.card {h : G // g * h = h * g}

/-- **Abelian ⟹ the commuting-degree is constant** (`= |G|`): the commuting-pairs
gadget is *also* blind on an abelian group (it is the complete relation). -/
theorem commDeg_const_of_comm {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hab : ∀ a b : G, a * b = b * a) (g : G) : commDeg g = Fintype.card G :=
  Fintype.card_congr (Equiv.subtypeUnivEquiv (fun h => hab g h))

/-- **Non-abelian ⟹ the commuting-degree is NON-constant**: some `g` commutes with
strictly fewer elements than `1` does (and `1` commutes with all `|G|`). This is the
precise sense in which a commuting-pairs / commutator gadget makes non-abelian
structure 1-WL-VISIBLE — colour refinement splits the segment by centralizer size,
which the product gadget (coordinate-regular, hence constant-degree) cannot do. -/
theorem commDeg_nonconst_of_noncomm {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (h : ∃ a b : G, a * b ≠ b * a) : ∃ g : G, commDeg g < commDeg (1 : G) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a, ?_⟩
  have h1 : commDeg (1 : G) = Fintype.card G := by
    unfold commDeg
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun h => by rw [one_mul, mul_one]))
  rw [h1]
  unfold commDeg
  exact Fintype.card_subtype_lt (x := b) hab

/-- The dichotomy in one statement: the commuting-degree is constant **iff** the
group is abelian — i.e. the commuting-pairs gadget is 1-WL-blind exactly on abelian
groups, and 1-WL-visible exactly on non-abelian ones. -/
theorem commDeg_const_iff_comm {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    (∀ g : G, commDeg g = Fintype.card G) ↔ (∀ a b : G, a * b = b * a) := by
  constructor
  · intro hconst
    by_contra hnc
    push Not at hnc
    obtain ⟨g, hlt⟩ := commDeg_nonconst_of_noncomm hnc
    have hg := hconst g
    have h1 := hconst (1 : G)
    omega
  · intro hab g; exact commDeg_const_of_comm hab g

#print axioms product_coord_regular
#print axioms product_coord_regular_indep
#print axioms linear_eq_unique
#print axioms product_fix_two_indep
#print axioms commDeg_const_of_comm
#print axioms commDeg_nonconst_of_noncomm
#print axioms commDeg_const_iff_comm

end WLVis
