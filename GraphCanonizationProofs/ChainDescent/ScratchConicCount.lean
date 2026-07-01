/-
# Route A, Phase 1 — the binary-conic count crux (discharging `hspan`, the Gauss half — done ELEMENTARILY)

**What this module builds.** The remaining half of the `hspan` discharge (recovery doc §8 ITEM B): toward
`|L_c| = q − ε` (`ε = ±1`) for the level set of a nondegenerate binary form (`c ≠ 0`), this increment lands the crux
character sum `∑ₓ χ(x² − a) = −1` (`a ≠ 0`, `χ` the quadratic character) — proved **without additive Gauss sums**.

**The elementary route.** By `quadraticChar_card_sqrts` (`#{z : z²=b} = χ(b)+1`),
`∑ₓ χ(x²−a) = ∑ₓ (#{z:z²=x²−a} − 1) = #{(x,z) : x²−z²=a} − q`, and the hyperbola bijection `(x,z) ↦ (x−z, x+z)` sends
`{x²−z²=a}` to `{(u,v) : u·v = a}`, which has `q−1` points (`u ≠ 0`, `v = a·u⁻¹`). So the sum is `(q−1) − q = −1`.

Elementary finite-field counting (no Gauss, no Witt). Axiom-clean `[propext, Classical.choice, Quot.sound]`,
`lake env lean`, NOT in `build.sh`.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace ChainDescent.ConicCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The hyperbola count.** For `a ≠ 0`, `#{(u,v) : u·v = a} = q − 1` (`u ≠ 0`, `v = a·u⁻¹`). -/
theorem card_prod_eq {a : F} (ha : a ≠ 0) :
    (univ.filter (fun p : F × F => p.1 * p.2 = a)).card = Fintype.card F - 1 := by
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ (0 : F))]
  refine Finset.card_bij' (fun p _ => p.1) (fun u _ => (u, a * u⁻¹)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun hx => ha (by rw [← hp, hx, zero_mul])
  · rintro u hu
    rw [Finset.mem_erase] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_comm a u⁻¹, ← mul_assoc, mul_inv_cancel₀ hu.1, one_mul]
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hx : x ≠ 0 := fun hx => ha (by rw [← hp, hx, zero_mul])
    refine Prod.ext rfl ?_
    show a * x⁻¹ = y
    rw [← hp, mul_comm x y, mul_assoc, mul_inv_cancel₀ hx, mul_one]
  · rintro u hu
    rfl

/-- **The difference-of-squares count.** For char ≠ 2, `#{(x,z) : x² − z² = a} = #{(u,v) : u·v = a}` via the bijection
`(x,z) ↦ (x−z, x+z)` (inverse `(u,v) ↦ ((u+v)/2, (v−u)/2)`; `x²−z² = (x−z)(x+z)`). -/
theorem card_sq_sub_eq [Invertible (2 : F)] {a : F} :
    (univ.filter (fun p : F × F => p.1 ^ 2 - p.2 ^ 2 = a)).card
      = (univ.filter (fun p : F × F => p.1 * p.2 = a)).card := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  refine Finset.card_bij'
    (fun p _ => (p.1 - p.2, p.1 + p.2)) (fun p _ => ((p.1 + p.2) / 2, (p.2 - p.1) / 2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, z⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    linear_combination hp
  · rintro ⟨u, v⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    field_simp
    linear_combination 4 * hp
  · rintro ⟨x, z⟩ _
    refine Prod.ext ?_ ?_ <;> · dsimp only; field_simp; ring
  · rintro ⟨u, v⟩ _
    refine Prod.ext ?_ ?_ <;> · dsimp only; field_simp; ring

/-- **★ The crux character sum.** For `a ≠ 0` (char ≠ 2), `∑ₓ χ(x² − a) = −1`. Via `quadraticChar_card_sqrts`
(`#{z:z²=b} = χ(b)+1`) the sum telescopes to `#{(x,z):x²−z²=a} − q = (q−1) − q = −1` (the hyperbola count). No additive
Gauss sums. -/
theorem sum_quadraticChar_sq_sub (hF : ringChar F ≠ 2) [Invertible (2 : F)] {a : F} (ha : a ≠ 0) :
    ∑ x : F, quadraticChar F (x ^ 2 - a) = -1 := by
  have key : ∀ x : F, quadraticChar F (x ^ 2 - a)
      = ((univ.filter (fun z => z ^ 2 = x ^ 2 - a)).card : ℤ) - 1 := by
    intro x
    have h := quadraticChar_card_sqrts hF (x ^ 2 - a)
    rw [Set.toFinset_setOf] at h
    linarith
  have hMnat : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 - a)).card
      = ∑ x : F, (univ.filter (fun z => z ^ 2 = x ^ 2 - a)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)
  have hswap : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 - a)).card
      = (univ.filter (fun p : F × F => p.1 ^ 2 - p.2 ^ 2 = a)).card := by
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor <;> intro h <;> linear_combination -h
  calc ∑ x : F, quadraticChar F (x ^ 2 - a)
      = ∑ x : F, (((univ.filter (fun z => z ^ 2 = x ^ 2 - a)).card : ℤ) - 1) :=
        Finset.sum_congr rfl (fun x _ => key x)
    _ = (∑ x : F, ((univ.filter (fun z => z ^ 2 = x ^ 2 - a)).card : ℤ)) - Fintype.card F := by
        rw [Finset.sum_sub_distrib]; simp [Finset.card_univ]
    _ = ((univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 - a)).card : ℤ) - Fintype.card F := by
        rw [← Nat.cast_sum, ← hMnat]
    _ = ((univ.filter (fun p : F × F => p.1 * p.2 = a)).card : ℤ) - Fintype.card F := by
        rw [hswap, card_sq_sub_eq]
    _ = -1 := by
        rw [card_prod_eq ha]
        have hq : 1 ≤ Fintype.card F := Fintype.card_pos
        push_cast [Nat.cast_sub hq]; ring

/-- **★ The binary-conic count.** For a diagonal nondegenerate binary form `w₁x² + w₂y²` (`w₁,w₂ ≠ 0`) and `c ≠ 0`,
`#{(x,y) : w₁x² + w₂y² = c} = q − χ(−w₁w₂⁻¹)` (`ε := χ(−w₁w₂⁻¹) ∈ {±1}`). Via `quadraticChar_card_sqrts` the slice count
is `χ((c−w₁x²)w₂⁻¹) + 1`; summing and factoring the character (`map_mul`) reduces the `x`-sum to the crux
`sum_quadraticChar_sq_sub` (`∑ₓ χ(x²−cw₁⁻¹) = −1`). No Gauss sums. -/
theorem card_binary_form (hF : ringChar F ≠ 2) [Invertible (2 : F)] {w₁ w₂ c : F}
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hc : c ≠ 0) :
    ((univ.filter (fun p : F × F => w₁ * p.1 ^ 2 + w₂ * p.2 ^ 2 = c)).card : ℤ)
      = Fintype.card F - quadraticChar F (-(w₁ * w₂⁻¹)) := by
  have hfib : (univ.filter (fun p : F × F => w₁ * p.1 ^ 2 + w₂ * p.2 ^ 2 = c)).card
      = ∑ x : F, (univ.filter (fun y => w₁ * x ^ 2 + w₂ * y ^ 2 = c)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)
  -- each slice: `#{y : w₁x²+w₂y²=c} = χ((c−w₁x²)w₂⁻¹) + 1`.
  have hslice : ∀ x : F, ((univ.filter (fun y => w₁ * x ^ 2 + w₂ * y ^ 2 = c)).card : ℤ)
      = quadraticChar F ((c - w₁ * x ^ 2) * w₂⁻¹) + 1 := by
    intro x
    have hcard := quadraticChar_card_sqrts hF ((c - w₁ * x ^ 2) * w₂⁻¹)
    rw [Set.toFinset_setOf] at hcard
    rw [← hcard]
    congr 2
    apply Finset.filter_congr
    intro y _
    constructor
    · intro h
      have hw : w₂ * y ^ 2 = c - w₁ * x ^ 2 := by linear_combination h
      rw [← hw, mul_comm w₂ (y ^ 2), mul_assoc, mul_inv_cancel₀ hw₂, mul_one]
    · intro h
      have hw : w₂ * y ^ 2 = c - w₁ * x ^ 2 := by
        rw [h, ← mul_assoc, mul_comm w₂ (c - w₁ * x ^ 2), mul_assoc, mul_inv_cancel₀ hw₂, mul_one]
      linear_combination hw
  -- sum the slices; factor the character over the `x`-sum via the crux.
  have hxsum : ∑ x : F, quadraticChar F ((c - w₁ * x ^ 2) * w₂⁻¹)
      = - quadraticChar F (-(w₁ * w₂⁻¹)) := by
    have hstep : ∀ x : F, quadraticChar F ((c - w₁ * x ^ 2) * w₂⁻¹)
        = quadraticChar F (-(w₁ * w₂⁻¹)) * quadraticChar F (x ^ 2 - c * w₁⁻¹) := by
      intro x
      rw [← map_mul]
      congr 1
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum,
      sum_quadraticChar_sq_sub hF (a := c * w₁⁻¹) (by simp [hc, hw₁])]
    ring
  calc ((univ.filter (fun p : F × F => w₁ * p.1 ^ 2 + w₂ * p.2 ^ 2 = c)).card : ℤ)
      = ∑ x : F, ((univ.filter (fun y => w₁ * x ^ 2 + w₂ * y ^ 2 = c)).card : ℤ) := by
        rw [hfib]; push_cast; ring
    _ = ∑ x : F, (quadraticChar F ((c - w₁ * x ^ 2) * w₂⁻¹) + 1) :=
        Finset.sum_congr rfl (fun x _ => hslice x)
    _ = (∑ x : F, quadraticChar F ((c - w₁ * x ^ 2) * w₂⁻¹)) + Fintype.card F := by
        rw [Finset.sum_add_distrib]; simp [Finset.card_univ]
    _ = Fintype.card F - quadraticChar F (-(w₁ * w₂⁻¹)) := by rw [hxsum]; ring

end ChainDescent.ConicCount
