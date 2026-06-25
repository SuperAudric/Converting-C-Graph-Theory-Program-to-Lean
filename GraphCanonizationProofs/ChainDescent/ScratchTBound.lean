/-
# The `|T|` bound (increment 3, step 3e-ii — the assembly).

Bucket-splits `normT_le`'s RHS into nondegenerate (`|radical|=1`, magnitude `√|V|`, count ≤ `|K|²`) and degenerate
(`|radical|≤|V|/|K|` via `radical_card_mul_card_le`, magnitude `≤ |V|/√|K|`, count ≤ `d·|K|` via `degenerate_count_le`)
pencil members, yielding an explicit bound on `|K|·‖T‖`.

NOT in build (scratch; needs oleans of the imported scratch modules).
-/
import ChainDescent.ScratchPairSep
import ChainDescent.ScratchCorank
import ChainDescent.ScratchGoodAnchor
import ChainDescent.ScratchBucket
import ChainDescent.ScratchChiNorm

namespace ChainDescent

open Finset Module

/-- **The `|T|` bound (3e-ii).** For a good anchor with no zero member (`hnz`, `hgood`), the per-pair character sum `T`
satisfies `|K|·‖T‖ ≤ |K|²·√|V| + (d·|K|)·(|V|/√|K|)`. The nondeg bucket contributes `≤ |K|²·√|V|`, the deg bucket
`≤ (d·|K|)·(|V|/√|K|)`. -/
theorem normT_bucket_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
        + (d * Fintype.card K) * (Fintype.card V / Real.sqrt (Fintype.card K)) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  set P := pairForm Q (t₀ - u) with hP
  set R := pairForm Q (t₀ - v) with hR
  -- abbreviations
  set p : K × K → Prop := fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥ with hp
  set s : Finset (K × K) := Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0) with hs
  -- the per-term magnitude `g`
  set g : K × K → ℝ := fun x => Real.sqrt ((Fintype.card V : ℝ)
      * (Finset.univ.filter (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card)
    with hg
  -- pointwise: χ-weights collapse the summand onto the support `s`
  have hF0 : ∀ x : K × K, ‖χ x.1‖ * ‖χ x.2‖ * g x = if (x.1 ≠ 0 ∧ x.2 ≠ 0) then g x else 0 := by
    intro x
    rw [norm_quadraticChar, norm_quadraticChar]
    by_cases h1 : x.1 = 0
    · simp [h1]
    · by_cases h2 : x.2 = 0
      · simp [h1, h2]
      · simp [h1, h2]
  -- the double sum collapses to `∑ over s`
  have hsum : (∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z)) = ∑ x ∈ s, g x := by
    rw [← Finset.sum_product', Finset.univ_product_univ, hs, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun x _ => hF0 x)
  -- magnitude bounds
  have hMa : (0 : ℝ) ≤ Real.sqrt (Fintype.card V) := Real.sqrt_nonneg _
  have hMb : (0 : ℝ) ≤ (Fintype.card V : ℝ) / Real.sqrt (Fintype.card K) :=
    div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hcardK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  -- nondeg bucket: `g x = √|V|`
  have ha : ∀ x ∈ s, ¬ p x → g x ≤ Real.sqrt (Fintype.card V) := by
    intro x _ hx
    rw [hp] at hx
    have hbot : polarRad (x.1 • P + x.2 • R) = ⊥ := not_not.1 hx
    have hone : (Finset.univ.filter
        (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card = 1 := by
      rw [polarRad_card_filter, hbot]
      simp
    rw [hg]; simp only; rw [hone]; simp
  -- deg bucket: `g x ≤ |V|/√|K|`
  have hb : ∀ x ∈ s, p x → g x ≤ (Fintype.card V : ℝ) / Real.sqrt (Fintype.card K) := by
    intro x hxs _
    rw [hs, Finset.mem_filter] at hxs
    obtain ⟨_, h1, h2⟩ := hxs
    have hGne : x.1 • P + x.2 • R ≠ 0 := hnz x.1 x.2 h1 h2
    have hcount := radical_card_mul_card_le (x.1 • P + x.2 • R) hGne
    rw [hg]; simp only
    refine sqrt_mul_le_div (by positivity) hcardK ?_
    exact_mod_cast hcount
  -- count bounds
  have hca : ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 := by
    rw [sq]
    calc ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card (K × K) : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
      _ = (Fintype.card K : ℝ) * Fintype.card K := by rw [Fintype.card_prod]; push_cast; ring
  have hcb : ((s.filter p).card : ℝ) ≤ (d * Fintype.card K : ℝ) := by
    have hsub : s.filter p ⊆
        Finset.univ.filter (fun x : K × K => polarRad (x.1 • P + x.2 • R) ≠ ⊥) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    calc ((s.filter p).card : ℝ)
        ≤ ((Finset.univ.filter (fun x : K × K => polarRad (x.1 • P + x.2 • R) ≠ ⊥)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (d * Fintype.card K : ℝ) := by exact_mod_cast degenerate_count_le b P R hgood
  -- assemble
  calc (Fintype.card K : ℝ) * ‖∑ t : V, χ (P (t - u)) * χ (R (t - v))‖
      ≤ ∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z) := normT_le hF hψ Q u v t₀
    _ = ∑ x ∈ s, g x := hsum
    _ ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
          + (d * Fintype.card K) * (Fintype.card V / Real.sqrt (Fintype.card K)) :=
        sum_two_bucket_le s g p _ _ _ _ hMa hMb ha hb hca hcb

end ChainDescent

#print axioms ChainDescent.normT_bucket_bound
