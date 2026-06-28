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

**NV is COMPLETE (14 axiom-clean lemmas).** Capstone `exists_hgood`: for `u ≠ v`, nondeg `Q`, `finrank V ≥ 2`,
`|K| ≥ 7`, the good-anchor witness exists — discharging the `hgood` hypothesis carried throughout the β machinery.

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

/-! ### NV-4 — the geometric witness + counting (an anisotropic-generator nondeg plane through `w`).

NV-3 reduces `hgood` to: `∃ a, pairForm Q a (a−w) ≠ 0 ∧ Q a ≠ 0 ∧ Q (a−w) ≠ 0`. The key simplification is the clean
**degree-2** formula `pairForm Q a (a−w) = 4·Q(a)·Q(w) − polar(a,w)²` (`pairForm_self_sub`): the "discriminant of the
plane `⟨a,w⟩`". NV-4a (`exists_pairForm_self_sub_ne_zero`) shows it is not identically zero (else `Q` would be a rank-≤1
form, contradicting nondegeneracy); NV-4b then counts the three quadric loci and finds a common non-vanishing point. -/

/-- **The plane-discriminant formula.** `pairForm Q a (a−w) = 4·Q(a)·Q(w) − polar(a,w)²` — the determinant of the Gram
of `⟨a, a−w⟩ = ⟨a, w⟩`, a **degree-2** polynomial in `a` (key for the NV-4 counting). -/
theorem pairForm_self_sub (Q : QuadraticForm K V) (a w : V) :
    pairForm Q a (a - w) = 4 * Q a * Q w - QuadraticMap.polar Q a w * QuadraticMap.polar Q a w := by
  have hQsub : Q (a - w) = Q a + Q w - QuadraticMap.polar Q a w := by
    have e1 : QuadraticMap.polar Q a (-w) = Q (a + -w) - Q a - Q (-w) := rfl
    rw [QuadraticMap.polar_neg_right, ← sub_eq_add_neg, QuadraticMap.map_neg] at e1
    linear_combination -e1
  have hpol : QuadraticMap.polar Q (a - w) a = 2 * Q a - QuadraticMap.polar Q a w := by
    rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, QuadraticMap.polar_comm Q w a,
        nsmul_eq_mul, Nat.cast_ofNat]
  rw [pairForm_apply, hQsub, hpol]; ring

/-- A nonzero vector orthogonal to `w` exists once `finrank V ≥ 2`: the functional `b ↦ polar Q b w` has a kernel of
positive dimension (rank-nullity, codomain `K` is `1`-dimensional). -/
theorem exists_ne_zero_polar_eq_zero [FiniteDimensional K V] (Q : QuadraticForm K V) (w : V)
    (hd : 2 ≤ Module.finrank K V) :
    ∃ b : V, b ≠ 0 ∧ QuadraticMap.polar Q b w = 0 := by
  set f : V →ₗ[K] K := (QuadraticMap.polarBilin Q).flip w with hf
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr1 : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have h := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at h
  have hker_pos : 0 < Module.finrank K (LinearMap.ker f) := by omega
  have hker_ne : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    exact absurd hker_pos (lt_irrefl 0)
  obtain ⟨b, hbmem, hb0⟩ := (Submodule.ne_bot_iff _).mp hker_ne
  refine ⟨b, hb0, ?_⟩
  have hfb : f b = 0 := LinearMap.mem_ker.mp hbmem
  rwa [hf, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply] at hfb

/-- **NV-4a — the geometric witness.** For nondegenerate `Q`, `w ≠ 0`, `finrank V ≥ 2`, the plane discriminant
`pairForm Q a (a−w) = 4 Q a Q w − polar(a,w)²` is **not identically zero** in `a`. Otherwise `Q` would satisfy
`4 Q a Q w = polar(a,w)²` for all `a` — a rank-≤1 form (its polar would vanish on a nonzero vector orthogonal to `w`),
contradicting `polarRad Q = ⊥`. -/
theorem exists_pairForm_self_sub_ne_zero [Invertible (2 : K)] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥) (w : V) (hw : w ≠ 0) (hd : 2 ≤ Module.finrank K V) :
    ∃ a : V, pairForm Q a (a - w) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  by_contra hcon
  simp only [not_exists, not_not, pairForm_self_sub] at hcon
  -- nondegeneracy
  have hnondeg : ∀ m : V, (∀ x, QuadraticMap.polar Q x m = 0) → m = 0 := by
    intro m hm
    have hmem : m ∈ polarRad Q := mem_polarRad.mpr hm
    rw [hQ, Submodule.mem_bot] at hmem
    exact hmem
  by_cases hQw : Q w = 0
  · -- `Q w = 0`: the identity forces `polar(·,w) ≡ 0`, so `w ∈ radical`
    apply hw
    apply hnondeg w
    intro x
    have hx := hcon x
    rw [hQw, mul_zero, zero_sub, neg_eq_zero] at hx
    exact mul_self_eq_zero.mp hx
  · -- `Q w ≠ 0`: a nonzero `b ⊥ w` lies in the radical
    obtain ⟨b, hb0, hbw⟩ := exists_ne_zero_polar_eq_zero Q w hd
    apply hb0
    apply hnondeg b
    intro x
    -- `Q b = 0`
    have hQb : Q b = 0 := by
      have hb := hcon b
      rw [hbw, mul_zero, sub_zero] at hb
      rcases mul_eq_zero.mp hb with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h4
        · exact h'
      · exact absurd h hQw
    -- `Q (x + b) = Q x`
    have hQxb : Q (x + b) = Q x := by
      have hx := hcon x
      have hxb := hcon (x + b)
      have hpxb : QuadraticMap.polar Q (x + b) w = QuadraticMap.polar Q x w := by
        rw [QuadraticMap.polar_add_left, hbw, add_zero]
      rw [hpxb] at hxb
      have hzero : 4 * Q w * (Q (x + b) - Q x) = 0 := by linear_combination hxb - hx
      have h4Qw : (4 * Q w : K) ≠ 0 := mul_ne_zero h4 hQw
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h h4Qw
      · exact sub_eq_zero.mp h
    rw [QuadraticMap.polar, hQxb, hQb]; ring

/-- A nondegenerate `Q` over a nontrivial space is **not the zero form** — `∃ a, Q a ≠ 0` (else `polar Q ≡ 0`, so
`polarRad Q = ⊤ ≠ ⊥`). -/
theorem exists_anisotropic (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥) [Nontrivial V] :
    ∃ a : V, Q a ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  have hmem : v ∈ polarRad Q := by
    rw [mem_polarRad]
    intro x
    rw [QuadraticMap.polar, hcon (x + v), hcon x, hcon v]; ring
  rw [hQ, Submodule.mem_bot] at hmem
  exact hmem

section NV4bCount
open MvPolynomial
variable {d : ℕ} (b : Basis (Fin d) K V)

/-- `gramQuadPoly b Q ≠ 0` when `Q` is nonzero somewhere (`gramQuadPoly_eval = Q t₀`). -/
theorem gramQuadPoly_ne_zero [Invertible (2 : K)] (Q : QuadraticForm K V) (hex : ∃ w₀, Q w₀ ≠ 0) :
    gramQuadPoly b Q ≠ 0 := by
  obtain ⟨w₀, hw₀⟩ := hex
  intro h0
  apply hw₀
  have hev := gramQuadPoly_eval b Q w₀
  rw [h0, map_zero] at hev
  exact hev.symm

/-- The polynomial representing the plane discriminant `pairForm Q a (a−w) = 4·Q(a)·Q(w) − polar(a,w)²`. -/
noncomputable def planeDiscPoly [Invertible (2 : K)] (Q : QuadraticForm K V) (w : V) :
    MvPolynomial (Fin d) K :=
  C (4 * Q w) * gramQuadPoly b Q
    - (coordPoly (fun k => QuadraticMap.polar Q (b k) w)) ^ 2

theorem planeDiscPoly_eval [Invertible (2 : K)] (Q : QuadraticForm K V) (w a : V) :
    MvPolynomial.eval (b.equivFun a) (planeDiscPoly b Q w) = pairForm Q a (a - w) := by
  have hcoord : MvPolynomial.eval (b.equivFun a) (coordPoly (fun k => QuadraticMap.polar Q (b k) w))
      = QuadraticMap.polar Q a w := by
    have h := coordPoly_eval_linFunc b ((QuadraticMap.polarBilin Q).flip w) a
    simp only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply] at h
    exact h
  rw [planeDiscPoly, map_sub, map_mul, eval_C, gramQuadPoly_eval, map_pow, hcoord, pairForm_self_sub]
  ring

theorem planeDiscPoly_totalDegree_le [Invertible (2 : K)] (Q : QuadraticForm K V) (w : V) :
    (planeDiscPoly b Q w).totalDegree ≤ 2 := by
  rw [planeDiscPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact gramQuadPoly_totalDegree_le b Q
  · rw [pow_two]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h := coordPoly_totalDegree_le (fun k => QuadraticMap.polar Q (b k) w)
    omega

theorem planeDiscPoly_ne_zero [Invertible (2 : K)] (Q : QuadraticForm K V) (w a₀ : V)
    (h : pairForm Q a₀ (a₀ - w) ≠ 0) : planeDiscPoly b Q w ≠ 0 := by
  intro h0
  apply h
  have hev := planeDiscPoly_eval b Q w a₀
  rw [h0, map_zero] at hev
  exact hev.symm

/-- **NV-4 — an anisotropic-generator nondegenerate plane through `w`.** For nondegenerate `Q`, `w ≠ 0`,
`finrank V ≥ 2`, `|K| ≥ 7`: there is `a` with `Q a ≠ 0`, `Q (a−w) ≠ 0`, and `pairForm Q a (a−w) ≠ 0`. The three bad
loci are quadrics (each `≤ 2·|V|/|K|` by Schwartz–Zippel on `gramQuadPoly`/`QPoly`/`planeDiscPoly`), with `planeDiscPoly`
nonvanishing by NV-4a; their union has `< |V|` points for `|K| > 6`, so a common good point exists. -/
theorem exists_good_plane_anchor [Invertible (2 : K)] [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥) (w : V) (hw : w ≠ 0)
    (hd : 2 ≤ Module.finrank K V) (hq : 7 ≤ Fintype.card K) :
    ∃ a : V, Q a ≠ 0 ∧ Q (a - w) ≠ 0 ∧ pairForm Q a (a - w) ≠ 0 := by
  classical
  have hntv : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (show 0 < Module.finrank K V by omega)
  obtain ⟨w₀, hw₀⟩ := exists_anisotropic Q hQ
  obtain ⟨a₀, ha₀⟩ := exists_pairForm_self_sub_ne_zero Q hQ w hw hd
  let b : Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  have c1 : (univ.filter (fun a : V => Q a = 0)).card * Fintype.card K ≤ 2 * Fintype.card V := by
    calc (univ.filter (fun a : V => Q a = 0)).card * Fintype.card K
        ≤ (gramQuadPoly b Q).totalDegree * Fintype.card V :=
          bad_anchor_count_le_of_poly b (fun a => Q a = 0) (gramQuadPoly b Q)
            (gramQuadPoly_ne_zero b Q ⟨w₀, hw₀⟩) (fun a h => by rw [gramQuadPoly_eval]; exact h)
      _ ≤ 2 * Fintype.card V := by gcongr; exact gramQuadPoly_totalDegree_le b Q
  have c2 : (univ.filter (fun a : V => Q (a - w) = 0)).card * Fintype.card K ≤ 2 * Fintype.card V :=
    qZero_count_le b Q w w₀ hw₀
  have c3 : (univ.filter (fun a : V => pairForm Q a (a - w) = 0)).card * Fintype.card K
      ≤ 2 * Fintype.card V := by
    calc (univ.filter (fun a : V => pairForm Q a (a - w) = 0)).card * Fintype.card K
        ≤ (planeDiscPoly b Q w).totalDegree * Fintype.card V :=
          bad_anchor_count_le_of_poly b (fun a => pairForm Q a (a - w) = 0) (planeDiscPoly b Q w)
            (planeDiscPoly_ne_zero b Q w a₀ ha₀) (fun a h => by rw [planeDiscPoly_eval]; exact h)
      _ ≤ 2 * Fintype.card V := by gcongr; exact planeDiscPoly_totalDegree_le b Q w
  set B1 := univ.filter (fun a : V => Q a = 0) with hB1
  set B2 := univ.filter (fun a : V => Q (a - w) = 0) with hB2
  set B3 := univ.filter (fun a : V => pairForm Q a (a - w) = 0) with hB3
  have hsum : (B1 ∪ B2 ∪ B3).card ≤ B1.card + B2.card + B3.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hScard : (B1 ∪ B2 ∪ B3).card * Fintype.card K ≤ 6 * Fintype.card V := by
    calc (B1 ∪ B2 ∪ B3).card * Fintype.card K
        ≤ (B1.card + B2.card + B3.card) * Fintype.card K := Nat.mul_le_mul_right _ hsum
      _ = B1.card * Fintype.card K + B2.card * Fintype.card K + B3.card * Fintype.card K := by ring
      _ ≤ 2 * Fintype.card V + 2 * Fintype.card V + 2 * Fintype.card V :=
          Nat.add_le_add (Nat.add_le_add c1 c2) c3
      _ = 6 * Fintype.card V := by ring
  have h7 : 7 * (B1 ∪ B2 ∪ B3).card ≤ 6 * Fintype.card V := by
    calc 7 * (B1 ∪ B2 ∪ B3).card ≤ Fintype.card K * (B1 ∪ B2 ∪ B3).card :=
          Nat.mul_le_mul_right _ hq
      _ = (B1 ∪ B2 ∪ B3).card * Fintype.card K := Nat.mul_comm _ _
      _ ≤ 6 * Fintype.card V := hScard
  have hVpos : 0 < Fintype.card V := Fintype.card_pos
  have hSlt : (B1 ∪ B2 ∪ B3).card < Fintype.card V := by omega
  have hSne : B1 ∪ B2 ∪ B3 ≠ univ := by
    intro h; rw [h, Finset.card_univ] at hSlt; exact absurd hSlt (lt_irrefl _)
  have hexnm : ∃ a, a ∉ B1 ∪ B2 ∪ B3 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hSne (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨a, ha⟩ := hexnm
  simp only [hB1, hB2, hB3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at ha
  exact ⟨a, ha.1.1, ha.1.2, ha.2⟩

/-- **`pairForm` nonvanishing ⟹ linear independence.** `pairForm Q a b = 4·Q(a)·Q(b) − polar(a,b)²` is the Gram
determinant of `{a,b}` under `polar Q`, so it vanishes whenever `a, b` are linearly dependent (if `b = c•a` then
`pairForm Q a (c•a) = 4c²Q(a)² − (2cQ(a))² = 0`). Contrapositive: a nonzero pair invariant forces `![a, b]`
linearly independent. Pure bilinearity — no `Invertible 2`. (Used to expose `hab` from `exists_hgood`'s `hpf`.) -/
theorem linearIndependent_of_pairForm_ne_zero (Q : QuadraticForm K V) {a b : V}
    (hab : pairForm Q a b ≠ 0) : LinearIndependent K ![a, b] := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hab (by rw [pairForm_apply]; simp [QuadraticMap.polar, map_zero])
  rw [LinearIndependent.pair_iff' ha]
  intro c hc
  apply hab
  rw [← hc, pairForm_apply, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_self]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **NV (capstone) — non-vacuity of `hgood`.** For `u ≠ v`, nondegenerate `Q`, `finrank V ≥ 2`, `|K| ≥ 7`: there is a
good anchor `t₀₀` and pencil coefficients `(y₀,z₀)` with `polarRad(y₀•pairForm Q(t₀₀−u) + z₀•pairForm Q(t₀₀−v)) = ⊥`,
**and** `t₀₀−u` is anisotropic (`Q(t₀₀−u) ≠ 0`) **and** `![t₀₀−u, t₀₀−v]` is linearly independent — exactly the carried
hypotheses (`hgood`/`hQu`/`hab`) of `ScratchIncr4c.beta_full_count_closed` AND the Route-0 capstone
`ScratchTBoundCorank2.c0_le_threequarters_corank2`. Take `t₀₀ = a+u` for the anisotropic-generator nondeg plane `a`
of NV-4 (so `t₀₀−u = a`, `t₀₀−v = a−w`): `Q a ≠ 0` gives `hQu`; `pairForm Q a (a−w) ≠ 0` (the plane is nondegenerate)
gives `hab` via `linearIndependent_of_pairForm_ne_zero`. NV-5 then picks `(y₀,z₀)`: `(1,1)` if `Q a + Q(a−w) ≠ 0`,
else `(1,−1)` (giving `c = 2·Q a ≠ 0`), and NV-3 (`polarRad_pencil_eq_bot`) seals the radical. -/
theorem exists_hgood [Invertible (2 : K)] [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
    (Q : QuadraticForm K V) (hQ : polarRad Q = ⊥) (u v : V) (huv : u ≠ v)
    (hd : 2 ≤ Module.finrank K V) (hq : 7 ≤ Fintype.card K) :
    ∃ (t₀₀ : V) (y₀ z₀ : K),
      polarRad (y₀ • pairForm Q (t₀₀ - u) + z₀ • pairForm Q (t₀₀ - v)) = ⊥
        ∧ Q (t₀₀ - u) ≠ 0
        ∧ LinearIndependent K ![t₀₀ - u, t₀₀ - v] := by
  set w := v - u with hwdef
  have hw : w ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  obtain ⟨a, hQa, hQaw, hpf⟩ := exists_good_plane_anchor Q hQ w hw hd hq
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have htu : (a + u) - u = a := by abel
  have htv : (a + u) - v = a - w := by rw [hwdef]; abel
  have hQu : Q ((a + u) - u) ≠ 0 := by rw [htu]; exact hQa
  have hindep : LinearIndependent K ![(a + u) - u, (a + u) - v] := by
    rw [htu, htv]; exact linearIndependent_of_pairForm_ne_zero Q hpf
  by_cases hsum : Q a + Q (a - w) = 0
  · refine ⟨a + u, 1, -1, ?_, hQu, hindep⟩
    rw [htu, htv]
    refine polarRad_pencil_eq_bot Q hQ a (a - w) 1 (-1) one_ne_zero (by norm_num) ?_ hpf
    have hQval : Q (a - w) = - Q a := by linear_combination hsum
    have heq : (1 : K) * Q a + (-1) * Q (a - w) = 2 * Q a := by rw [hQval]; ring
    rw [heq]; exact mul_ne_zero h2 hQa
  · refine ⟨a + u, 1, 1, ?_, hQu, hindep⟩
    rw [htu, htv]
    refine polarRad_pencil_eq_bot Q hQ a (a - w) 1 1 one_ne_zero one_ne_zero ?_ hpf
    rw [one_mul, one_mul]; exact hsum

end NV4bCount

end ChainDescent

#print axioms ChainDescent.polar_pencil_apply
#print axioms ChainDescent.pencil_radical_key
#print axioms ChainDescent.polarRad_pencil_subset_span
#print axioms ChainDescent.polarRad_pencil_eq_bot
#print axioms ChainDescent.pairForm_self_sub
#print axioms ChainDescent.exists_ne_zero_polar_eq_zero
#print axioms ChainDescent.exists_pairForm_self_sub_ne_zero
#print axioms ChainDescent.exists_anisotropic
#print axioms ChainDescent.gramQuadPoly_ne_zero
#print axioms ChainDescent.planeDiscPoly_eval
#print axioms ChainDescent.planeDiscPoly_totalDegree_le
#print axioms ChainDescent.planeDiscPoly_ne_zero
#print axioms ChainDescent.exists_good_plane_anchor
#print axioms ChainDescent.linearIndependent_of_pairForm_ne_zero
#print axioms ChainDescent.exists_hgood
