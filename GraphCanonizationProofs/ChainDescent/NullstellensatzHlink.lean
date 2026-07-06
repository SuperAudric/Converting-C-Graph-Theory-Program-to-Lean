import ChainDescent.NullstellensatzCount

namespace ChainDescent.Nullstellensatz

open QuadraticMap

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

/-- **Upper mirror of `cone_card_lower`**: `|cone|·q ≤ |V| + (q−1)·√|V|`. -/
theorem cone_card_upper {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) * (Fintype.card K)
      ≤ (Fintype.card V : ℝ) + ((Fintype.card K : ℝ) - 1) * Real.sqrt (Fintype.card V) := by
  have hsq := zeroCount_sq_le hψ Q
  rw [radical_card_one Q hQnd, Nat.cast_one, mul_one] at hsq
  set z : ℝ := ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) with hz
  set q : ℝ := (Fintype.card K : ℝ) with hq
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast Fintype.card_pos
    linarith
  have habs : |z * q - N| ≤ (q - 1) * Real.sqrt N := by
    have hrhs : ((q - 1) * Real.sqrt N) ^ 2 = (q - 1) ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt hNnonneg]
    have hle2 : (z * q - N) ^ 2 ≤ ((q - 1) * Real.sqrt N) ^ 2 := by rw [hrhs]; exact hsq
    have hle := Real.sqrt_le_sqrt hle2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hle
  have := (abs_le.mp habs).2
  linarith

/-- **Hyperplane count**: a nonzero linear functional `f : V → K` has `|ker f|·q = |V|`. -/
theorem hyperplane_card (f : V →ₗ[K] K) (hf : f ≠ 0) :
    (Finset.univ.filter (fun z : V => f z = 0)).card * Fintype.card K = Fintype.card V := by
  classical
  have hkc : (Finset.univ.filter (fun z : V => f z = 0)).card
      = Fintype.card (LinearMap.ker f) := by
    rw [Fintype.card_subtype]; congr 1; ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker]
  have hrank : Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hker : Fintype.card (LinearMap.ker f)
      = Fintype.card K ^ Module.finrank K (LinearMap.ker f) := Module.card_eq_pow_finrank
  have hV : Fintype.card V = Fintype.card K ^ Module.finrank K V := Module.card_eq_pow_finrank
  rw [hkc, hker, hV, ← hrank, pow_succ]

set_option maxHeartbeats 800000 in
open Module in
/-- **`hlink`: anisotropic `polar`-diameter ≤ 2.** For anisotropic `y, y'` there is an anisotropic `z`
with `polar Q y z ≠ 0` and `polar Q z y' ≠ 0`. Counting: `V = T ∪ cone ∪ y^⊥ ∪ y'^⊥`; the two hyperplanes
have `|V|/q` each, `cone ≤ |V|/q + (q−1)√|V|` (upper), and the saving `|cone ∩ y^⊥| = |V|/q²` (exact, `sec_aniso`)
brings the `q=3` boundary strictly positive: `r(q²−3q+1) > q(q−1)` with `r = √|V| ≥ q² ≥ 9`, `q ≥ 3`. -/
theorem aniso_polar_diameter_two {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (heven : Even (Module.finrank K V)) (hdim : 4 ≤ Module.finrank K V)
    (hq : 3 ≤ Fintype.card K) {y y' : V} (hy : Q y ≠ 0) (hy' : Q y' ≠ 0) :
    ∃ z, Q z ≠ 0 ∧ QuadraticMap.polar Q y z ≠ 0 ∧ QuadraticMap.polar Q z y' ≠ 0 := by
  classical
  have h2ne : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  -- the two hyperplane functionals `polarBilin Q y`, `polarBilin Q y'` are nonzero (aniso ⟹ f y = 2Q y ≠ 0)
  have hfyne : Q.polarBilin y ≠ 0 := by
    intro h
    have : QuadraticMap.polar Q y y = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply, h, LinearMap.zero_apply]
    rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at this
    exact (mul_ne_zero h2ne hy) this
  have hfy'ne : Q.polarBilin y' ≠ 0 := by
    intro h
    have : QuadraticMap.polar Q y' y' = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply, h, LinearMap.zero_apply]
    rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at this
    exact (mul_ne_zero h2ne hy') this
  -- the four Finsets
  set Tset := Finset.univ.filter
    (fun z : V => Q z ≠ 0 ∧ QuadraticMap.polar Q y z ≠ 0 ∧ QuadraticMap.polar Q z y' ≠ 0) with hT
  set Aset := Finset.univ.filter (fun z : V => Q z = 0) with hA
  set Bset := Finset.univ.filter (fun z : V => QuadraticMap.polar Q y z = 0) with hB
  set Cset := Finset.univ.filter (fun z : V => QuadraticMap.polar Q z y' = 0) with hC
  set ABset := Finset.univ.filter
    (fun z : V => Q z = 0 ∧ QuadraticMap.polar Q y z = 0) with hAB
  -- suffices to show `Tset` is nonempty
  suffices hpos : 0 < Tset.card by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    rw [hT, Finset.mem_filter] at hz
    exact ⟨z, hz.2.1, hz.2.2.1, hz.2.2.2⟩
  -- covering: `univ ⊆ Tset ∪ (Aset ∪ Bset) ∪ Cset`
  have hcover : (Finset.univ : Finset V) ⊆ Tset ∪ (Aset ∪ Bset) ∪ Cset := by
    intro z _
    simp only [hT, hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hQz : Q z = 0
    · left; right; left; exact hQz
    by_cases hbz : QuadraticMap.polar Q y z = 0
    · left; right; right; exact hbz
    by_cases hcz : QuadraticMap.polar Q z y' = 0
    · right; exact hcz
    · left; left; exact ⟨hQz, hbz, hcz⟩
  -- `Aset ∩ Bset = ABset`
  have hABinter : Aset ∩ Bset = ABset := by
    rw [hA, hB, hAB, Finset.filter_and]
  -- count facts as ℕ then cast
  have hBcard : Bset.card * Fintype.card K = Fintype.card V := by
    rw [hB]
    have := hyperplane_card (Q.polarBilin y) hfyne
    simp only [QuadraticMap.polarBilin_apply_apply] at this ⊢
    exact this
  have hCcard : Cset.card * Fintype.card K = Fintype.card V := by
    have hfC : (Finset.univ.filter (fun z : V => QuadraticMap.polar Q z y' = 0)).card
        = (Finset.univ.filter (fun z : V => QuadraticMap.polar Q y' z = 0)).card := by
      congr 1; ext z; simp only [Finset.mem_filter, QuadraticMap.polar_comm]
    rw [hC, hfC]
    have := hyperplane_card (Q.polarBilin y') hfy'ne
    simp only [QuadraticMap.polarBilin_apply_apply] at this ⊢
    exact this
  have hABcard : ABset.card * Fintype.card K * Fintype.card K = Fintype.card V := by
    rw [hAB]; exact sec_aniso hF hψ Q hQnd heven hy
  have hAupper := cone_card_upper hψ Q hQnd
  rw [← hA] at hAupper
  -- move everything to ℝ
  set N : ℝ := (Fintype.card V : ℝ) with hNe
  set q : ℝ := (Fintype.card K : ℝ) with hqe
  set r : ℝ := Real.sqrt (Fintype.card V) with hre
  have hq3 : (3 : ℝ) ≤ q := by rw [hqe]; exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hNpos : (0 : ℝ) < N := by rw [hNe]; exact_mod_cast Fintype.card_pos
  have hr0 : (0 : ℝ) < r := by rw [hre]; exact Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hrr : r * r = N := by rw [hre, hNe]; exact Real.mul_self_sqrt (Nat.cast_nonneg _)
  -- `r ≥ q²` from `|V| = q^d`, `d ≥ 4`
  have hVpow : (Fintype.card V : ℝ) = (Fintype.card K : ℝ) ^ Module.finrank K V := by
    rw [Module.card_eq_pow_finrank (K := K)]; push_cast; ring
  have hrq2 : q ^ 2 ≤ r := by
    have hq2sq : (q ^ 2) ^ 2 ≤ N := by
      rw [hNe, hVpow, ← hqe, ← pow_mul]
      have : q ^ (2 * 2) ≤ q ^ Module.finrank K V :=
        pow_le_pow_right₀ (by linarith) (by omega)
      simpa using this
    have h2 := Real.sqrt_le_sqrt hq2sq
    rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ q ^ 2), hNe] at h2
    rwa [← hre] at h2
  -- cast count facts (all over the shared monomials)
  have e2 : (Bset.card : ℝ) * q = N := by rw [hqe, hNe, ← Nat.cast_mul, hBcard]
  have e3 : (Cset.card : ℝ) * q = N := by rw [hqe, hNe, ← Nat.cast_mul, hCcard]
  have e4 : (ABset.card : ℝ) * q * q = N := by
    rw [hqe, hNe]; exact_mod_cast hABcard
  -- covering cardinal inequality (ℕ then ℝ)
  have hcov1 : Fintype.card V ≤ Tset.card + (Aset ∪ Bset).card + Cset.card := by
    have h0 := Finset.card_le_card hcover
    rw [Finset.card_univ] at h0
    calc Fintype.card V ≤ (Tset ∪ (Aset ∪ Bset) ∪ Cset).card := h0
      _ ≤ (Tset ∪ (Aset ∪ Bset)).card + Cset.card := Finset.card_union_le _ _
      _ ≤ Tset.card + (Aset ∪ Bset).card + Cset.card := by
          gcongr; exact Finset.card_union_le _ _
  have hunion : ((Aset ∪ Bset).card : ℝ) + ABset.card = Aset.card + Bset.card := by
    have := Finset.card_union_add_card_inter Aset Bset
    rw [hABinter] at this
    exact_mod_cast this
  -- assemble in ℝ
  have e1 : N ≤ (Tset.card : ℝ) + (Aset.card + Bset.card - ABset.card) + Cset.card := by
    have hcast : (Fintype.card V : ℝ) ≤ Tset.card + (Aset ∪ Bset).card + Cset.card := by
      exact_mod_cast hcov1
    rw [hNe]; linarith [hunion]
  have e5 : (Aset.card : ℝ) * q ≤ N + (q - 1) * r := by rw [hNe, hqe, hre]; exact hAupper
  -- make `N, q, r` opaque atoms so `nlinarith` does not unfold `Fintype.card` (heartbeat blowup)
  clear_value N q r
  -- positivity certificate, staged low-degree
  have hq2pos : (0 : ℝ) < q ^ 2 := by positivity
  -- multiply the count facts up to the `q²` scale
  have e2q : (Bset.card : ℝ) * q * q = N * q := by rw [e2]
  have e3q : (Cset.card : ℝ) * q * q = N * q := by rw [e3]
  have e5q : (Aset.card : ℝ) * q * q ≤ (N + (q - 1) * r) * q :=
    mul_le_mul_of_nonneg_right e5 (le_of_lt hq0)
  -- multiply the covering inequality by `q²`
  have e1q : N * q ^ 2 ≤ ((Tset.card : ℝ) + (Aset.card + Bset.card - ABset.card) + Cset.card) * q ^ 2 :=
    mul_le_mul_of_nonneg_right e1 (le_of_lt hq2pos)
  -- `Tcard·q² ≥ N(q²−3q+1) − q(q−1)r`
  have hkey : N * (q ^ 2 - 3 * q + 1) - q * (q - 1) * r ≤ (Tset.card : ℝ) * q ^ 2 := by
    nlinarith [e1q, e2q, e3q, e4, e5q]
  -- the RHS bound is strictly positive
  have hpoly : (1 : ℝ) ≤ q ^ 2 - 3 * q + 1 := by nlinarith [hq3]
  have hqq : q * (q - 1) < q ^ 2 * (q ^ 2 - 3 * q + 1) := by
    nlinarith [mul_nonneg (sq_nonneg q) (by linarith [hq3] : (0:ℝ) ≤ q - 3), hq0, hq3]
  have hstep : q * (q - 1) < r * (q ^ 2 - 3 * q + 1) := by
    have hmono := mul_le_mul_of_nonneg_right hrq2 (by linarith [hpoly] : (0:ℝ) ≤ q ^ 2 - 3 * q + 1)
    linarith [hqq, hmono]
  have hrhs : (0 : ℝ) < N * (q ^ 2 - 3 * q + 1) - q * (q - 1) * r := by
    nlinarith [hrr, mul_lt_mul_of_pos_left hstep hr0]
  have hTq2 : (0 : ℝ) < (Tset.card : ℝ) * q ^ 2 := lt_of_lt_of_le hrhs hkey
  have hgoal : (0 : ℝ) < (Tset.card : ℝ) := by
    rcases mul_pos_iff.mp hTq2 with ⟨hT, _⟩ | ⟨_, hq2neg⟩
    · exact hT
    · exact absurd hq2neg (not_lt.mpr (le_of_lt hq2pos))
  exact_mod_cast hgoal

open Module in
/-- **Even-dimensional quadric Nullstellensatz — FULLY DISCHARGED (general finite field).** For a finite
field `K` of odd characteristic and even `finrank ≥ 4`, a nondegenerate quadratic form `Q` is determined up
to a nonzero scalar by its isotropic cone. This is the mathematical content of `NondegQuadricDeterminesForm`.
Route: `nullstellensatz_of_structural` fed by the two purely-geometric bricks `cone_punctured_span` (hspan)
and `aniso_polar_diameter_two` (hlink), with a primitive ℂ-valued additive character constructed internally
(`AddChar.FiniteField.primitiveChar_to_Complex`). No citation, no `native_decide`. -/
theorem nondegQuadric_determines_of_even [Nontrivial V]
    (hF : ringChar K ≠ 2) (heven : Even (Module.finrank K V)) (hdim : 4 ≤ Module.finrank K V)
    (hq : 3 ≤ Fintype.card K)
    (Q R : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcone : ∀ v, Q v = 0 ↔ R v = 0) :
    ∃ μ : Kˣ, ∀ v, R v = (μ : K) * Q v := by
  have hψ : (AddChar.FiniteField.primitiveChar_to_Complex K).IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive K
  exact nullstellensatz_of_structural Q R hQnd hcone
    (fun y hy => cone_punctured_span hF hψ Q hQnd heven hdim hq hy)
    (fun y y' hy hy' => aniso_polar_diameter_two hF hψ Q hQnd heven hdim hq hy hy')

/-- **The `ZMod p` instance — proves the exact `NondegQuadricDeterminesForm` predicate (even `d`).** For
odd prime `p` and even `4 ≤ d`, the cone of a nondegenerate quadric on `(ZMod p)^d` determines the form up
to a `(ZMod p)ˣ` scalar. This is definitionally `NondegQuadricDeterminesForm p d` once `p ≠ 2`, `4 ≤ d`
are supplied; it discharges the carried citation for every (even-dimensional) instantiation Route C uses. -/
theorem nondegQuadric_zmod_of_even (p d : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hev : Even d)
    (hd : 4 ≤ d) (Q R : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcone : ∀ v, Q v = 0 ↔ R v = 0) :
    ∃ μ : (ZMod p)ˣ, ∀ v, R v = (μ : ZMod p) * Q v := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hpge2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  have hpge3 : 3 ≤ p := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    simpa using h
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero h2ne
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hfr : Module.finrank (ZMod p) (Fin d → ZMod p) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heven : Even (Module.finrank (ZMod p) (Fin d → ZMod p)) := by rw [hfr]; exact hev
  have hdim : 4 ≤ Module.finrank (ZMod p) (Fin d → ZMod p) := by rw [hfr]; exact hd
  have hq : 3 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; exact hpge3
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin d → ZMod p) := inferInstance
  exact nondegQuadric_determines_of_even hF heven hdim hq Q R hQnd hcone

end ChainDescent.Nullstellensatz
