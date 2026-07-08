/-
# Pencil polar-radical corank cap (ScratchPencilCorank2).

Two elementary linear-algebra lemmas about the pencil `F = y•pairForm Q a + z•pairForm Q b`:

* `polar_pairForm` — the polar of `pairForm Q a`:
  `polar (pairForm Q a) x h = 4·Q a·polar Q x h − 2·polar Q x a·polar Q h a`.
* `pencil_polarRad_finrank_le` — the geometric corank cap: for `a, b` linearly independent and `Q` with
  nondegenerate polar form (char ≠ 2), `finrank (polarRad F) ≤ finrank V − 2`.

NOT in build (scratch; verify with `lake env lean ChainDescent/ScratchPencilCorank2.lean`).
-/
import ChainDescent.PairForm
import ChainDescent.PencilTBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace ChainDescent

open Module

/-- The polar of `pairForm Q a`. -/
theorem polar_pairForm {K V} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a x h : V) :
    QuadraticMap.polar (pairForm Q a) x h
      = 4 * Q a * QuadraticMap.polar Q x h
        - 2 * QuadraticMap.polar Q x a * QuadraticMap.polar Q h a := by
  have hQadd : Q (x + h) = Q x + Q h + QuadraticMap.polar Q x h := by
    rw [QuadraticMap.polar]; ring
  have hpadd : QuadraticMap.polar Q (x + h) a
      = QuadraticMap.polar Q x a + QuadraticMap.polar Q h a :=
    QuadraticMap.polar_add_left Q x h a
  rw [QuadraticMap.polar, pairForm_apply, pairForm_apply, pairForm_apply, hQadd, hpadd]
  ring

/-- The polar of the pencil `F = y•pairForm Q a + z•pairForm Q b`, fully expanded. -/
theorem polar_pencil_pairForm {K V} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a b : V) (y z : K) (x h : V) :
    QuadraticMap.polar (y • pairForm Q a + z • pairForm Q b) x h
      = 4 * (y * Q a + z * Q b) * QuadraticMap.polar Q x h
        - 2 * (y * QuadraticMap.polar Q h a * QuadraticMap.polar Q x a
              + z * QuadraticMap.polar Q h b * QuadraticMap.polar Q x b) := by
  have key : QuadraticMap.polar (⇑(y • pairForm Q a + z • pairForm Q b)) x h
      = y * QuadraticMap.polar (pairForm Q a) x h + z * QuadraticMap.polar (pairForm Q b) x h := by
    simp only [QuadraticMap.polar, QuadraticMap.add_apply, QuadraticMap.smul_apply, smul_eq_mul]
    ring
  rw [key, polar_pairForm, polar_pairForm]
  ring

/-- **The geometric corank cap.** For the pencil `F = y•pairForm Q a + z•pairForm Q b` with `a, b` linearly
independent, `y, z ≠ 0`, and `Q.polarBilin` nondegenerate (char ≠ 2, `finrank V ≥ 4`), the polar-radical of `F`
has corank at least 2: `finrank (polarRad F) ≤ finrank V − 2`. -/
theorem pencil_polarRad_finrank_le {K V} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (a b : V) (y z : K)
    (hd : 4 ≤ Module.finrank K V)
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hQnd : Q.polarBilin.Nondegenerate)
    (hab : LinearIndependent K ![a, b]) :
    Module.finrank K (polarRad (y • pairForm Q a + z • pairForm Q b)) ≤ Module.finrank K V - 2 := by
  classical
  set F := y • pairForm Q a + z • pairForm Q b with hF
  set lam : K := y * Q a + z * Q b with hlam
  -- nondegeneracy helper
  have hnd : ∀ w : V, (∀ x, QuadraticMap.polar Q x w = 0) → w = 0 := by
    intro w hw
    apply hQnd.1 w
    intro n
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hw n
  -- (★) membership characterization
  have hstar : ∀ h ∈ polarRad F, ∀ x,
      4 * lam * QuadraticMap.polar Q x h
        = 2 * (y * QuadraticMap.polar Q h a * QuadraticMap.polar Q x a
              + z * QuadraticMap.polar Q h b * QuadraticMap.polar Q x b) := by
    intro h hh x
    have := hh x
    rw [hF, polar_pencil_pairForm] at this
    rw [hlam]
    linear_combination this
  by_cases hlam0 : lam = 0
  · -- CASE λ = 0
    -- independence property of the two functionals
    have hindep : ∀ α β : K, (∀ x, α * QuadraticMap.polar Q x a + β * QuadraticMap.polar Q x b = 0)
        → α = 0 ∧ β = 0 := by
      intro α β hαβ
      have hzero : α • a + β • b = 0 := by
        apply hnd
        intro x
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul]
        exact hαβ x
      rw [LinearIndependent.pair_iff] at hab
      exact hab α β hzero
    -- W = ker φa ⊓ ker φb, where φa x = polar Q x a
    set φa : V →ₗ[K] K := (LinearMap.flip Q.polarBilin) a with hφa
    set φb : V →ₗ[K] K := (LinearMap.flip Q.polarBilin) b with hφb
    have hφa_apply : ∀ x, φa x = QuadraticMap.polar Q x a := by
      intro x; rw [hφa, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
    have hφb_apply : ∀ x, φb x = QuadraticMap.polar Q x b := by
      intro x; rw [hφb, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
    set W := LinearMap.ker φa ⊓ LinearMap.ker φb with hW
    -- polarRad F ⊆ W
    have hsub : polarRad F ≤ W := by
      intro h hh
      have heq : ∀ x, (y * QuadraticMap.polar Q h a) * QuadraticMap.polar Q x a
          + (z * QuadraticMap.polar Q h b) * QuadraticMap.polar Q x b = 0 := by
        intro x
        have h0 := hstar h hh x
        rw [hlam0, mul_zero, zero_mul] at h0
        rcases mul_eq_zero.mp h0.symm with h2' | hS
        · exact absurd h2' (Invertible.ne_zero (2 : K))
        · linear_combination hS
      obtain ⟨hya, hzb⟩ := hindep _ _ heq
      have hpha : QuadraticMap.polar Q h a = 0 := by
        rcases mul_eq_zero.1 hya with h1 | h1
        · exact absurd h1 hy
        · exact h1
      have hphb : QuadraticMap.polar Q h b = 0 := by
        rcases mul_eq_zero.1 hzb with h1 | h1
        · exact absurd h1 hz
        · exact h1
      rw [hW, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, hφa_apply, hφb_apply]
      exact ⟨hpha, hphb⟩
    -- a ≠ 0, b ≠ 0
    have ha0 : a ≠ 0 := by
      intro h0
      rw [LinearIndependent.pair_iff] at hab
      have := (hab 1 0 (by rw [h0]; simp)).1
      norm_num at this
    -- φa ≠ 0
    have hφa0 : φa ≠ 0 := by
      intro h0
      apply ha0
      apply hnd
      intro x
      rw [← hφa_apply, h0, LinearMap.zero_apply]
    -- finrank (ker φa) = finrank V - 1
    have hkerφa : finrank K (LinearMap.ker φa) = finrank K V - 1 := by
      have hne : LinearMap.range φa ≠ ⊥ := by
        rw [Ne, LinearMap.range_eq_bot]; exact hφa0
      haveI : Nontrivial (LinearMap.range φa) := Submodule.nontrivial_iff_ne_bot.mpr hne
      have hpos : 0 < finrank K (LinearMap.range φa) := Module.finrank_pos
      have hle : finrank K (LinearMap.range φa) ≤ 1 := by
        have hh := Submodule.finrank_le (LinearMap.range φa)
        rwa [finrank_self] at hh
      have hrk := LinearMap.finrank_range_add_finrank_ker φa
      omega
    -- φb is not in span of φa: ∃ w0, polar w0 a = 0 ∧ polar w0 b ≠ 0
    have hexw0 : ∃ w0, QuadraticMap.polar Q w0 a = 0 ∧ QuadraticMap.polar Q w0 b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      -- then ker φa ⊆ ker φb, contradicting independence
      -- specifically: take w with φa w = 0 -> φb w = 0; build dependence
      -- Use independence: ∀ x, 1*polar x b - 0 ... need α polar x a + β polar x b = 0 nontrivial.
      -- Actually from hcon: polar w a = 0 → polar w b = 0.  Means ker φa ≤ ker φb.
      -- So φb = c • φa for some c, giving (-c) polar x a + 1 polar x b = 0 ∀ x, contra hindep.
      have hksub : LinearMap.ker φa ≤ LinearMap.ker φb := by
        intro w hw
        rw [LinearMap.mem_ker, hφb_apply]
        rw [LinearMap.mem_ker, hφa_apply] at hw
        exact hcon w hw
      have hmem : φb ∈ Submodule.span K (Set.range (fun _ : Unit => φa)) :=
        FiniteDimensional.mem_span_of_iInf_ker_le_ker (by simpa only [iInf_const] using hksub)
      simp only [Set.range_const, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      -- hc : c • φa = φb
      have hcontra : ∀ x, (-c) * QuadraticMap.polar Q x a + 1 * QuadraticMap.polar Q x b = 0 := by
        intro x
        have hcx : (c • φa) x = φb x := by rw [hc]
        rw [LinearMap.smul_apply, hφa_apply, hφb_apply, smul_eq_mul] at hcx
        linear_combination -hcx
      obtain ⟨_, hone⟩ := hindep (-c) 1 hcontra
      norm_num at hone
    obtain ⟨w0, hw0a, hw0b⟩ := hexw0
    -- w0 ∈ ker φa but w0 ∉ W, so W < ker φa
    have hWlt : W < LinearMap.ker φa := by
      rw [hW]
      refine lt_of_le_of_ne inf_le_left ?_
      intro heq
      have : w0 ∈ LinearMap.ker φa := by rw [LinearMap.mem_ker, hφa_apply]; exact hw0a
      rw [← heq, Submodule.mem_inf] at this
      have := this.2
      rw [LinearMap.mem_ker, hφb_apply] at this
      exact hw0b this
    have hWlt_fr : finrank K W < finrank K (LinearMap.ker φa) :=
      Submodule.finrank_lt_finrank_of_lt hWlt
    have : finrank K (polarRad F) ≤ finrank K W := Submodule.finrank_mono hsub
    omega
  · -- CASE λ ≠ 0 : polarRad F ⊆ span {a, b}
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero (Invertible.ne_zero (2 : K)) (Invertible.ne_zero (2 : K))
    have h4lam : (4 : K) * lam ≠ 0 := mul_ne_zero h4 hlam0
    have hsub : polarRad F ≤ Submodule.span K {a, b} := by
      intro h hh
      -- (4λ)•h − (2y·polar h a)•a − (2z·polar h b)•b lies in the radical, hence is 0
      have hwrad : ∀ x, QuadraticMap.polar Q x
          ((4 * lam) • h - (2 * y * QuadraticMap.polar Q h a) • a
            - (2 * z * QuadraticMap.polar Q h b) • b) = 0 := by
        intro x
        have hs := hstar h hh x
        rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right,
          QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        linear_combination hs
      have hz0 := hnd _ hwrad
      rw [sub_sub] at hz0
      have hheq : (4 * lam) • h = (2 * y * QuadraticMap.polar Q h a) • a
          + (2 * z * QuadraticMap.polar Q h b) • b := sub_eq_zero.mp hz0
      have hmem : (4 * lam) • h ∈ Submodule.span K {a, b} := by
        rw [hheq]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hsplit : h = (4 * lam)⁻¹ • ((4 * lam) • h) := by
        rw [smul_smul, inv_mul_cancel₀ h4lam, one_smul]
      rw [hsplit]
      exact Submodule.smul_mem _ _ hmem
    have hspan : finrank K (Submodule.span K {a, b}) ≤ 2 := by
      have hle : finrank K (Submodule.span K ({a, b} : Set V)) ≤ ({a, b} : Set V).toFinset.card :=
        finrank_span_le_card (R := K) ({a, b} : Set V)
      have hcard : ({a, b} : Set V).toFinset.card ≤ 2 := by
        classical
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    have hmono : finrank K (polarRad F) ≤ finrank K (Submodule.span K {a, b}) :=
      Submodule.finrank_mono hsub
    omega

/-- **The single-form corank-1 cap (the `z_u` sibling of the pencil cap).** For `Q.polarBilin` nondegenerate and a
non-isotropic anchor `Q a ≠ 0`, the polar-radical of `pairForm Q a` is `⊆ span{a}`, hence `finrank ≤ 1` — the corank is
exactly 1 (`radical = ⟨a⟩`), not the uniform `d−1`. This is what tightens the `z_u` (zero-count) bound's `n/√q` term to
`√n·√q`, dropping its threshold from `q ≥ 256` to `q ≥ 16`. -/
theorem single_polarRad_finrank_le {K V} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (a : V)
    (hQnd : Q.polarBilin.Nondegenerate) (hQa : Q a ≠ 0) :
    Module.finrank K (polarRad (pairForm Q a)) ≤ 1 := by
  classical
  have hnd : ∀ w : V, (∀ x, QuadraticMap.polar Q x w = 0) → w = 0 := by
    intro w hw
    apply hQnd.1 w
    intro n
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hw n
  have h2Qa : (2 : K) * Q a ≠ 0 := mul_ne_zero (Invertible.ne_zero (2 : K)) hQa
  have hsub : polarRad (pairForm Q a) ≤ Submodule.span K {a} := by
    intro h hh
    -- (2 Q a)•h − (polar h a)•a lies in the radical of Q, hence is 0
    have hwrad : ∀ x, QuadraticMap.polar Q x
        ((2 * Q a) • h - (QuadraticMap.polar Q h a) • a) = 0 := by
      intro x
      have hstar : QuadraticMap.polar (pairForm Q a) x h = 0 := hh x
      rw [polar_pairForm] at hstar
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul]
      have h2 : (2 : K) * ((2 * Q a) * QuadraticMap.polar Q x h
          - QuadraticMap.polar Q h a * QuadraticMap.polar Q x a) = 0 := by
        linear_combination hstar
      rcases mul_eq_zero.mp h2 with hc | hc
      · exact absurd hc (Invertible.ne_zero (2 : K))
      · exact hc
    have hz0 := hnd _ hwrad
    have hheq : (2 * Q a) • h = (QuadraticMap.polar Q h a) • a := sub_eq_zero.mp hz0
    have hmem : (2 * Q a) • h ∈ Submodule.span K {a} := by
      rw [hheq]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hsplit : h = (2 * Q a)⁻¹ • ((2 * Q a) • h) := by
      rw [smul_smul, inv_mul_cancel₀ h2Qa, one_smul]
    rw [hsplit]; exact Submodule.smul_mem _ _ hmem
  calc Module.finrank K (polarRad (pairForm Q a))
      ≤ Module.finrank K (Submodule.span K {a}) := Submodule.finrank_mono hsub
    _ ≤ 1 := by
        have := finrank_span_le_card (R := K) ({a} : Set V)
        simpa using this

end ChainDescent

#print axioms ChainDescent.polar_pairForm
#print axioms ChainDescent.pencil_polarRad_finrank_le
#print axioms ChainDescent.single_polarRad_finrank_le
