/-
# Increment 4 — NV: non-vacuity of the good anchor (SCRATCH).

The β machinery (`ScratchIncr4c.pencilDetPoly_ne_zero`/`beta_count_closed`/`beta_full_count_closed`) all carry the
hypothesis **`hgood`**: a witness anchor `t₀₀` and pencil coefficients `(y₀,z₀)` with
`polarRad (y₀ • pairForm Q (t₀₀ − u) + z₀ • pairForm Q (t₀₀ − v)) = ⊥`. **NV** discharges this: for every `u ≠ v`
(nondegenerate `Q`, `d ≥ 2`, `q ≥ q₀`) such a witness exists. This is the lone deep remaining increment-4 obligation.

## The reduction (worked on paper; the algebra closes)

Write `a = t₀₀ − u`, `b = t₀₀ − v = a − w`, `w = v − u ≠ 0`. For `B = y • pairForm Q a + z • pairForm Q b`,
`polar B s r = 4c · polar Q s r − 2y · polar(s,a)·polar(r,a) − 2z · polar(s,b)·polar(r,b)`, `c = y·Q(a) + z·Q(b)`
(**NV-1**, this file). Then:
- **NV-2:** if `c ≠ 0`, every `s ∈ polarRad B` lies in `⟨a,b⟩` (invert the nondegenerate `polar Q`).
- **NV-3:** within `⟨a,b⟩` the radical condition is a `2×2` system with `det M = 4yz · pairForm Q a b`; so
  `pairForm Q a b ≠ 0 ∧ y,z ≠ 0 ∧ c ≠ 0 ⟹ polarRad B = ⊥`.
- Key identity: `pairForm Q a b = 4·Q(a)·Q(b) − polar(a,b)² = det(polar Q |_{⟨a,b⟩})`, so `pairForm Q a b ≠ 0 ⟺`
  `⟨a,b⟩` is a **nondegenerate 2-plane**.
- **NV-4:** a nondegenerate plane through `w` always exists (`Q(w)≠0`: orthogonal sum of anisotropic lines;
  `Q(w)=0`: hyperbolic plane `⟨w,w''⟩`, `polar(w,w'')≠0`), with anisotropic generators `a, a−w` by counting (`q≥q₀`).
- **NV-5:** pick `y,z ≠ 0` with `c ≠ 0` (elementary) → capstone `t₀₀ = a + u`.

This file is the staged build. **NV-1 LANDED below; NV-2…NV-5 are the remaining stages.**

NOT in build (scratch; `lake env lean ChainDescent/ScratchIncr4d.lean`, after `lake build ChainDescent.ScratchIncr4c`).
-/
import ChainDescent.ScratchIncr4c

namespace ChainDescent

open Finset Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **NV-1 — the pencil polar formula.** The polar of a pencil member `y • pairForm Q a + z • pairForm Q b` is
`4c · polar Q s r − 2y · polar(s,a)·polar(r,a) − 2z · polar(s,b)·polar(r,b)` with `c = y·Q(a) + z·Q(b)`. Pure algebra
on `polar_pairForm_apply` + bilinearity (`polar` of a sum/scalar-multiple of forms). The foundation of NV-2/NV-3. -/
theorem polar_pencil_apply (Q : QuadraticForm K V) (a b : V) (y z : K) (s r : V) :
    QuadraticMap.polar (y • pairForm Q a + z • pairForm Q b) s r
      = 4 * (y * Q a + z * Q b) * QuadraticMap.polar Q s r
        - 2 * y * (QuadraticMap.polar Q s a * QuadraticMap.polar Q r a)
        - 2 * z * (QuadraticMap.polar Q s b * QuadraticMap.polar Q r b) := by
  have h : QuadraticMap.polar (y • pairForm Q a + z • pairForm Q b) s r
      = y * QuadraticMap.polar (pairForm Q a) s r + z * QuadraticMap.polar (pairForm Q b) s r := by
    simp only [QuadraticMap.polar, QuadraticMap.add_apply, QuadraticMap.smul_apply, smul_eq_mul]
    ring
  rw [h, polar_pairForm_apply, polar_pairForm_apply]; ring

/-- **The radical equation (shared by NV-2/NV-3).** For nondegenerate `Q`, `s ∈ polarRad B` forces
`(4c)·s = (2y·polar(s,a))·a + (2z·polar(s,b))·b` (`c = y·Q(a)+z·Q(b)`), by inverting the nondegenerate `polar Q`
against the NV-1 polar formula. -/
theorem pencil_radical_key [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥)
    (a b : V) (y z : K) {s : V} (hs : s ∈ polarRad (y • pairForm Q a + z • pairForm Q b)) :
    (4 * (y * Q a + z * Q b)) • s
      = (2 * y * QuadraticMap.polar Q s a) • a + (2 * z * QuadraticMap.polar Q s b) • b := by
  rw [mem_polarRad] at hs
  have hnondeg : ∀ m : V, (∀ x, QuadraticMap.polar Q x m = 0) → m = 0 := by
    intro m hm
    have hmem : m ∈ polarRad Q := mem_polarRad.mpr hm
    rw [hQ, Submodule.mem_bot] at hmem
    exact hmem
  rw [← sub_eq_zero]
  apply hnondeg
  intro r
  rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right]
  have hsr := hs r
  rw [polar_pencil_apply] at hsr
  simp only [smul_eq_mul]
  linear_combination hsr

/-- **NV-2 — the radical lands in `⟨a,b⟩`.** For nondegenerate `Q`, if `c = y·Q(a)+z·Q(b) ≠ 0` then every
`s ∈ polarRad (y • pairForm Q a + z • pairForm Q b)` lies in `span K {a,b}` (divide `pencil_radical_key` by `4c ≠ 0`). -/
theorem polarRad_pencil_subset_span [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥)
    (a b : V) (y z : K) (hc : y * Q a + z * Q b ≠ 0)
    {s : V} (hs : s ∈ polarRad (y • pairForm Q a + z • pairForm Q b)) :
    s ∈ Submodule.span K ({a, b} : Set V) := by
  have key := pencil_radical_key Q hQ a b y z hs
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4c : (4 * (y * Q a + z * Q b) : K) ≠ 0 := mul_ne_zero h4 hc
  have hs_eq : s = (4 * (y * Q a + z * Q b))⁻¹ •
      ((2 * y * QuadraticMap.polar Q s a) • a + (2 * z * QuadraticMap.polar Q s b) • b) := by
    rw [← key, smul_smul, inv_mul_cancel₀ h4c, one_smul]
  rw [hs_eq]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (show a ∈ ({a, b} : Set V) by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (show b ∈ ({a, b} : Set V) by simp))

/-- **NV-3 — the pencil member is nondegenerate.** For nondegenerate `Q` with `y,z ≠ 0`, `c = y·Q(a)+z·Q(b) ≠ 0`,
and `pairForm Q a b ≠ 0` (⟺ `⟨a,b⟩` a nondegenerate plane), the member `y • pairForm Q a + z • pairForm Q b` is
**nondegenerate** (`polarRad = ⊥`). Evaluating the radical equation at `r = a, b` gives a `2×2` system in
`(polar(s,a), polar(s,b))` with `det = 4yz·pairForm Q a b ≠ 0`, so both vanish; then `pencil_radical_key` gives `s = 0`. -/
theorem polarRad_pencil_eq_bot [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥)
    (a b : V) (y z : K) (hy : y ≠ 0) (hz : z ≠ 0) (hc : y * Q a + z * Q b ≠ 0)
    (hpf : pairForm Q a b ≠ 0) :
    polarRad (y • pairForm Q a + z • pairForm Q b) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [Submodule.eq_bot_iff]
  intro s hsmem
  have hs := hsmem
  rw [mem_polarRad] at hs
  -- the 2×2 system from `r = a` and `r = b`
  have ea : (4 * z * Q b) * QuadraticMap.polar Q s a
      - (2 * z * QuadraticMap.polar Q a b) * QuadraticMap.polar Q s b = 0 := by
    have h := hs a
    rw [polar_pencil_apply, QuadraticMap.polar_self, QuadraticMap.polar_comm Q a s] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
    linear_combination h
  have eb : -((2 * y * QuadraticMap.polar Q a b) * QuadraticMap.polar Q s a)
      + (4 * y * Q a) * QuadraticMap.polar Q s b = 0 := by
    have h := hs b
    rw [polar_pencil_apply, QuadraticMap.polar_self, QuadraticMap.polar_comm Q b s,
        QuadraticMap.polar_comm Q b a] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
    linear_combination h
  -- determinant coefficient = 4yz · pairForm Q a b ≠ 0
  have hpf' : 4 * Q a * Q b - QuadraticMap.polar Q a b * QuadraticMap.polar Q a b = pairForm Q a b := by
    rw [pairForm_apply, QuadraticMap.polar_comm Q b a]
  have hcoeff : (4 * y * z
      * (4 * Q a * Q b - QuadraticMap.polar Q a b * QuadraticMap.polar Q a b)) ≠ 0 := by
    rw [hpf']; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hy) hz) hpf
  have hσa : (4 * y * z * (4 * Q a * Q b - QuadraticMap.polar Q a b * QuadraticMap.polar Q a b))
      * QuadraticMap.polar Q s a = 0 := by
    linear_combination (4 * y * Q a) * ea + (2 * z * QuadraticMap.polar Q a b) * eb
  have hσb : (4 * y * z * (4 * Q a * Q b - QuadraticMap.polar Q a b * QuadraticMap.polar Q a b))
      * QuadraticMap.polar Q s b = 0 := by
    linear_combination (2 * y * QuadraticMap.polar Q a b) * ea + (4 * z * Q b) * eb
  have hsa0 : QuadraticMap.polar Q s a = 0 := (mul_eq_zero.mp hσa).resolve_left hcoeff
  have hsb0 : QuadraticMap.polar Q s b = 0 := (mul_eq_zero.mp hσb).resolve_left hcoeff
  -- plug into the radical equation
  have hkey := pencil_radical_key Q hQ a b y z hsmem
  rw [hsa0, hsb0, mul_zero, mul_zero, zero_smul, zero_smul, add_zero] at hkey
  have h4c : (4 * (y * Q a + z * Q b) : K) ≠ 0 := mul_ne_zero h4 hc
  rcases smul_eq_zero.mp hkey with h | h
  · exact absurd h h4c
  · exact h

end ChainDescent

#print axioms ChainDescent.polar_pencil_apply
#print axioms ChainDescent.pencil_radical_key
#print axioms ChainDescent.polarRad_pencil_subset_span
#print axioms ChainDescent.polarRad_pencil_eq_bot
