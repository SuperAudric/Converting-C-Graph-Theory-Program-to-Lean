/-
# Route 0 — the `q ≳ d² → q ≳ const` second tightening (cap `d−2`, threshold `256 → 16`).

The corank tightening (`ScratchTBoundCorank`) charges every degenerate pencil member the corank-`d−1` proper-subspace
bound, giving deg term `2·|V|/√q` (threshold `hq3 : q ≥ 256`). Route 0 sharpens this to corank `d−2` — the geometric
fact that the pencil polar `4λB − 2(y φ_a⊗φ_a + z φ_b⊗φ_b)` is a *rank-2* perturbation of `4λB`
(`ScratchPencilCorank2.pencil_polarRad_finrank_le`) — giving deg term `2·|V|/q`, i.e. the binding threshold drops to
`q ≥ 16`.

This module assembles:
* `le_two_pow_sub_two` / `concentration_bound2` — the cap-`d−2` concentration (`∑ s^{c_t} ≤ 2 s^{D−2}`), including the
  all-ones case via `D ≤ 2^{D−2}`.
* `deg_bucket_le2` — the deg bucket for the pencil `y•pairForm Q p + z•pairForm Q r`, bounded by `2·|V|` (one `√q`
  better than `deg_bucket_le`), using the geometric cap.

NOT in build (scratch; `lake env lean ChainDescent/ScratchTBoundCorank2.lean`).
-/
import ChainDescent.ScratchTBoundCorank
import ChainDescent.ScratchPencilCorank2

namespace ChainDescent

open Polynomial Matrix Finset Module

variable {K : Type*} [Field K] {d : ℕ}

/-- `D ≤ 2^(D-2)` for `D ≥ 4` (the all-ones concentration helper). -/
theorem le_two_pow_sub_two {D : ℕ} (hD : 4 ≤ D) : D ≤ 2 ^ (D - 2) := by
  induction D, hD using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk2 : 1 ≤ 2 ^ (k - 2) := Nat.one_le_pow (k - 2) 2 (by norm_num)
    have he : 2 ^ (k + 1 - 2) = 2 ^ (k - 2) * 2 := by
      rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]
    omega

/-- **CONCENTRATION, cap `D−2`.** If `s ≥ 2`, `D ≥ 4`, the exponents satisfy `1 ≤ c t ≤ D − 2` and `∑ c t ≤ D`, then
`∑ s^(c t) ≤ 2·s^(D−2)`. (Two cases: some `c t ≥ 2` — peel it, the rest sums to `≤ D−2`; or all `c t = 1` — then
`∑ = |T|·s ≤ D·s ≤ 2 s^(D−2)` by `le_two_pow_sub_two`.) One `√q` sharper than `concentration_bound`. -/
theorem concentration_bound2 {ι : Type*} {s : ℝ} (hs : 2 ≤ s) {c : ι → ℕ} {T : Finset ι} {D : ℕ}
    (hD : 4 ≤ D) (hsum : ∑ t ∈ T, c t ≤ D) (hlo : ∀ t ∈ T, 1 ≤ c t) (hhi : ∀ t ∈ T, c t ≤ D - 2) :
    ∑ t ∈ T, s ^ (c t) ≤ 2 * s ^ (D - 2) := by
  classical
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hspos : (0 : ℝ) ≤ s ^ (D - 2) := by positivity
  by_cases hbig : ∃ t ∈ T, 2 ≤ c t
  · -- peel a big (corank ≥ 2) term
    obtain ⟨a, haT, hca2⟩ := hbig
    rw [← Finset.add_sum_erase T (fun t => s ^ (c t)) haT]
    have h1 : s ^ (c a) ≤ s ^ (D - 2) := pow_le_pow_right₀ hs1 (hhi a haT)
    have he : c a + ∑ t ∈ T.erase a, c t = ∑ t ∈ T, c t := Finset.add_sum_erase T c haT
    have hrest : ∑ t ∈ T.erase a, c t ≤ D - 2 := by omega
    have h2 : ∑ t ∈ T.erase a, s ^ (c t) ≤ s ^ (D - 2) :=
      le_trans (pow_sum_mul_bound hs (fun t ht => hlo t (Finset.mem_of_mem_erase ht)))
        (pow_le_pow_right₀ hs1 hrest)
    linarith
  · -- all corank = 1
    push_neg at hbig
    have hsumeq : ∑ t ∈ T, s ^ (c t) = (T.card : ℝ) * s := by
      rw [Finset.sum_congr rfl (fun t ht => by
        have h1 := hbig t ht; have h2 := hlo t ht
        rw [show c t = 1 by omega, pow_one]), Finset.sum_const, nsmul_eq_mul]
    have hcardle : (T.card : ℝ) ≤ (D : ℝ) := by
      have hc1 : T.card ≤ ∑ t ∈ T, c t := by
        rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hlo
      exact_mod_cast le_trans hc1 hsum
    have hhelp : (D : ℝ) * s ≤ 2 * s ^ (D - 2) := by
      have hDr : (D : ℝ) ≤ 2 ^ (D - 2) := by exact_mod_cast le_two_pow_sub_two hD
      have hpow2 : (2 : ℝ) ^ (D - 3) ≤ s ^ (D - 3) := pow_le_pow_left₀ (by norm_num) hs (D - 3)
      have he1 : (2 : ℝ) ^ (D - 2) = 2 * 2 ^ (D - 3) := by
        rw [show D - 2 = (D - 3) + 1 by omega, pow_succ]; ring
      have he2 : s ^ (D - 2) = s ^ (D - 3) * s := by
        rw [show D - 2 = (D - 3) + 1 by omega, pow_succ]
      have hD3 : (D : ℝ) ≤ 2 * s ^ (D - 3) := by
        calc (D : ℝ) ≤ 2 ^ (D - 2) := hDr
          _ = 2 * 2 ^ (D - 3) := he1
          _ ≤ 2 * s ^ (D - 3) := by linarith [hpow2]
      calc (D : ℝ) * s ≤ (2 * s ^ (D - 3)) * s := by nlinarith [hD3, hs0]
        _ = 2 * (s ^ (D - 3) * s) := by ring
        _ = 2 * s ^ (D - 2) := by rw [he2]
    rw [hsumeq]
    calc (T.card : ℝ) * s ≤ (D : ℝ) * s := by nlinarith [hcardle, hs0]
      _ ≤ 2 * s ^ (D - 2) := hhelp

/-- **The cap-`d−2` degenerate bucket bound (Route 0 A-assembly).** For the pencil `y•pairForm Q p + z•pairForm Q r`
with `p, r` independent and `Q.polarBilin` nondegenerate (`d ≥ 4`), the degenerate-bucket sum is at most `2·|V|` — one
`√q` sharper than `deg_bucket_le`'s `2·|K|·(|V|/√|K|)`. Same regroup machinery, but the per-ratio corank is capped at
`d−2` (`pencil_polarRad_finrank_le`) and concentrated via `concentration_bound2`. -/
theorem deg_bucket_le2 {V : Type*} [AddCommGroup V] [Module K V] [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] [Invertible (2 : K)] [FiniteDimensional K V]
    (b : Basis (Fin d) K V) (Q : QuadraticForm K V) (p r : V) (hd4 : 4 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hab : LinearIndependent K ![p, r]) (hQnd : Q.polarBilin.Nondegenerate)
    (hp : (pencilPoly (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q p)))
            (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q r)))).det ≠ 0) :
    ∑ x ∈ ((Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0)).filter
        (fun x => polarRad (x.1 • pairForm Q p + x.2 • pairForm Q r) ≠ ⊥)),
      Real.sqrt ((Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V =>
            ∀ w, QuadraticMap.polar (x.1 • pairForm Q p + x.2 • pairForm Q r) w h = 0)).card)
      ≤ 2 * (Fintype.card V : ℝ) := by
  classical
  set P := pairForm Q p with hPdef
  set R := pairForm Q r with hRdef
  set A := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P) with hA
  set B := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) with hB
  set q : ℕ := Fintype.card K with hq
  set n : ℕ := Fintype.card V with hn
  set ρ : K × K → K := fun x => x.2 * x.1⁻¹ with hρ
  set cork : K → ℕ := fun t => finrank K (LinearMap.ker ((A + t • B).mulVecLin)) with hcork
  set S := (Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0)).filter
      (fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥) with hS
  have hxne : ∀ x ∈ S, x.1 ≠ 0 ∧ x.2 ≠ 0 := by
    intro x hx; exact (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
  have hxrad : ∀ x ∈ S, polarRad (x.1 • P + x.2 • R) ≠ ⊥ := by
    intro x hx; exact (Finset.mem_filter.1 hx).2
  have hsqrtq2 : (2 : ℝ) ≤ Real.sqrt q := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq4)
  have hqpos : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  have hnq : (n : ℝ) = (q : ℝ) ^ d := by
    rw [hn, hq, Module.card_eq_pow_finrank (K := K) (V := V), Module.finrank_eq_card_basis b,
      Fintype.card_fin]; push_cast; ring
  have hfin : finrank K V = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hgx : ∀ x ∈ S, Real.sqrt ((n : ℝ)
      * (Finset.univ.filter (fun h : V =>
          ∀ w, QuadraticMap.polar (x.1 • P + x.2 • R) w h = 0)).card)
        = Real.sqrt n * Real.sqrt q ^ (cork (ρ x)) := by
    intro x hx
    have h1 : ((Finset.univ.filter (fun h : V =>
        ∀ w, QuadraticMap.polar (x.1 • P + x.2 • R) w h = 0)).card : ℝ)
        = (q : ℝ) ^ (cork (ρ x)) := by
      rw [radicalCard_eq_pow b P R (hxne x hx).1, ← hA, ← hB]
      push_cast
      rfl
    rw [h1, Real.sqrt_mul (by positivity), sqrt_natpow _ (le_of_lt hqpos)]
  rw [Finset.sum_congr rfl hgx, ← Finset.mul_sum]
  have hN : ∀ t : K, ((S.filter (fun x => ρ x = t)).card : ℝ) ≤ (q : ℝ) := by
    intro t
    rw [hρ]
    exact_mod_cast fiber_fst_card_le S (fun x hx => (hxne x hx).1) t
  have hstep2 : ∑ x ∈ S, Real.sqrt q ^ (cork (ρ x))
      ≤ (q : ℝ) * ∑ t ∈ S.image ρ, Real.sqrt q ^ (cork t) :=
    sum_comp_ratio_le S ρ (fun t => Real.sqrt q ^ (cork t)) (fun t => by positivity) q hN
  set T := S.image ρ with hT
  have hce : ∀ x ∈ S, cork (ρ x) = finrank K (polarRad (x.1 • P + x.2 • R)) := fun x hxS =>
    corank_ratio_eq b P R (hxne x hxS).1
  have hlo : ∀ t ∈ T, 1 ≤ cork t := by
    intro t ht
    rw [hT, Finset.mem_image] at ht
    obtain ⟨x, hxS, hxt⟩ := ht
    rw [← hxt, hce x hxS, Nat.one_le_iff_ne_zero]
    intro hzero
    exact hxrad x hxS (Submodule.finrank_eq_zero.1 hzero)
  have hhi : ∀ t ∈ T, cork t ≤ d - 2 := by
    intro t ht
    rw [hT, Finset.mem_image] at ht
    obtain ⟨x, hxS, hxt⟩ := ht
    rw [← hxt, hce x hxS]
    have hle := pencil_polarRad_finrank_le Q p r x.1 x.2 (by rw [hfin]; exact hd4)
      (hxne x hxS).1 (hxne x hxS).2 hQnd hab
    rw [hfin] at hle
    exact hle
  have hsumcork : ∑ t ∈ T, cork t ≤ d := by
    rw [hT]; exact sum_finrankKer_le A B (S.image ρ) hp
  have hstep3 : ∑ t ∈ T, Real.sqrt q ^ (cork t) ≤ 2 * Real.sqrt q ^ (d - 2) :=
    concentration_bound2 hsqrtq2 hd4 hsumcork hlo hhi
  have hkey : Real.sqrt n * ((q : ℝ) * (2 * Real.sqrt q ^ (d - 2))) = 2 * (n : ℝ) := by
    obtain ⟨m, hm⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
    subst hm
    have hu2 : Real.sqrt q ^ 2 = (q : ℝ) := Real.sq_sqrt (le_of_lt hqpos)
    have hsqn : Real.sqrt (n : ℝ) = Real.sqrt q ^ (m + 2) := by
      rw [hnq, sqrt_natpow _ (le_of_lt hqpos)]
    rw [hsqn, Nat.add_sub_cancel, hnq]
    generalize Real.sqrt q = u at hu2 ⊢
    rw [← hu2]
    ring
  calc Real.sqrt n * ∑ x ∈ S, Real.sqrt q ^ (cork (ρ x))
      ≤ Real.sqrt n * ((q : ℝ) * ∑ t ∈ T, Real.sqrt q ^ (cork t)) :=
        mul_le_mul_of_nonneg_left hstep2 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * ((q : ℝ) * (2 * Real.sqrt q ^ (d - 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hstep3 (le_of_lt hqpos)
    _ = 2 * (n : ℝ) := hkey

/-- **The `c₀ ≤ ¾` arithmetic at threshold `q ≥ 16` (Route 0).** With the corank-stratified deg term `2n/q` (`deg_bucket_le2`)
AND the corank-1 `z_u` bound `zu·q ≤ n + (q−1)·√n·√q` (`single_polarRad_finrank_le`), the threshold drops from `q ≥ 256`
to `q ≥ 16`: `n` and `(q−1)√n√q` both fit under `qn/16` for `q ≥ 16` (using `√n ≥ 8q` from `hq1`, `√q ≥ 4`). -/
theorem c0_le2 {n q T zu NS : ℝ} (hn : 0 < n) (hq : 0 < q)
    (hcount : 2 * NS ≤ 2 * zu + n + T)
    (hT : T ≤ q * Real.sqrt n + 2 * n / q)
    (hzu : zu * q ≤ n + (q - 1) * Real.sqrt n * Real.sqrt q)
    (hq1 : 64 * q ^ 2 ≤ n) (hq3 : 16 ≤ q) :
    NS ≤ 3 / 4 * n := by
  set r := Real.sqrt q with hrdef
  set m := Real.sqrt n with hmdef
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hnn : m * m = n := Real.mul_self_sqrt hn.le
  have hrr : r * r = q := Real.mul_self_sqrt hq.le
  have h8q : 8 * q ≤ m := by
    rw [hmdef, show (8 : ℝ) * q = Real.sqrt ((8 * q) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq1])
  have h4 : (4 : ℝ) ≤ r := by
    rw [hrdef, show (4 : ℝ) = Real.sqrt (4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq3])
  -- T ≤ n/4
  have hA : q * m ≤ n / 8 := by nlinarith [mul_le_mul_of_nonneg_right h8q hm, hnn]
  have hB : 2 * n / q ≤ n / 8 := by
    rw [div_le_iff₀ hq]; nlinarith [hq3, hn]
  have hTb : T ≤ n / 4 := by linarith [hT, hA, hB]
  -- z_u ≤ n/8
  have hrm : 32 * q ≤ r * m := by
    have := mul_le_mul h4 h8q (by positivity) (by linarith)
    linarith [this]
  have h16qrm : 16 * (q - 1) ≤ r * m := by linarith [hrm, hq.le]
  have hrmsq : (r * m) * (m * r) = q * n := by
    rw [show (r * m) * (m * r) = (r * r) * (m * m) by ring, hrr, hnn]
  have hkey : (q - 1) * m * r ≤ q * n / 16 := by
    nlinarith [h16qrm, mul_nonneg hm hr.le, hrmsq]
  have hzub : zu ≤ n / 8 := by
    have hzq : zu * q ≤ n / 8 * q := by nlinarith [hzu, hkey, hq3, hn]
    exact le_of_mul_le_mul_right hzq hq
  linarith [hcount, hTb, hzub]

/-- **The `|T|` bound with the cap-`d−2` deg bucket.** `|K|·‖T‖ ≤ |K|²·√|V| + 2·|V|` — the deg bucket is now `2·|V|`
(via `deg_bucket_le2`), one `√q` smaller than `normT_bucket_bound_corank`'s `2·|K|·(|V|/√|K|)`. -/
theorem normT_bucket_bound_corank2 {V : Type*} [AddCommGroup V] [Module K V]
    [Fintype K] [DecidableEq K] [Invertible (2 : K)] [Fintype V] [DecidableEq V] [FiniteDimensional K V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) (b : Basis (Fin d) K V)
    (hd4 : 4 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hab : LinearIndependent K ![t₀ - u, t₀ - v]) (hQnd : Q.polarBilin.Nondegenerate)
    (hp : (pencilPoly (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q (t₀ - u))))
            (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q (t₀ - v))))).det ≠ 0) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) + 2 * (Fintype.card V : ℝ) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  set P := pairForm Q (t₀ - u) with hP
  set R := pairForm Q (t₀ - v) with hR
  set p : K × K → Prop := fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥ with hp'
  set s : Finset (K × K) := Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0) with hs
  set g : K × K → ℝ := fun x => Real.sqrt ((Fintype.card V : ℝ)
      * (Finset.univ.filter (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card)
    with hg
  have hF0 : ∀ x : K × K, ‖χ x.1‖ * ‖χ x.2‖ * g x = if (x.1 ≠ 0 ∧ x.2 ≠ 0) then g x else 0 := by
    intro x
    rw [norm_quadraticChar, norm_quadraticChar]
    by_cases h1 : x.1 = 0
    · simp [h1]
    · by_cases h2 : x.2 = 0
      · simp [h1, h2]
      · simp [h1, h2]
  have hsum : (∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z)) = ∑ x ∈ s, g x := by
    rw [← Finset.sum_product', Finset.univ_product_univ, hs, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun x _ => hF0 x)
  have ha : ∀ x ∈ s, ¬ p x → g x ≤ Real.sqrt (Fintype.card V) := by
    intro x _ hx
    rw [hp'] at hx
    have hbot : polarRad (x.1 • P + x.2 • R) = ⊥ := not_not.1 hx
    have hone : (Finset.univ.filter
        (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card = 1 := by
      rw [polarRad_card_filter, hbot]; simp
    rw [hg]; simp only; rw [hone]; simp
  have hca : ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 := by
    rw [_root_.sq]
    calc ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card (K × K) : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
      _ = (Fintype.card K : ℝ) * Fintype.card K := by rw [Fintype.card_prod]; push_cast; ring
  have hnondeg : ∑ x ∈ s.filter (fun x => ¬ p x), g x
      ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) := by
    calc ∑ x ∈ s.filter (fun x => ¬ p x), g x
        ≤ ∑ _x ∈ s.filter (fun x => ¬ p x), Real.sqrt (Fintype.card V) :=
          Finset.sum_le_sum (fun x hx =>
            ha x (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx).2)
      _ = ((s.filter (fun x => ¬ p x)).card : ℝ) * Real.sqrt (Fintype.card V) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) :=
          mul_le_mul_of_nonneg_right hca (Real.sqrt_nonneg _)
  have hdeg : ∑ x ∈ s.filter p, g x ≤ 2 * (Fintype.card V : ℝ) :=
    deg_bucket_le2 b Q (t₀ - u) (t₀ - v) hd4 hq4 hab hQnd hp
  calc (Fintype.card K : ℝ) * ‖∑ t : V, χ (P (t - u)) * χ (R (t - v))‖
      ≤ ∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z) := normT_le hF hψ Q u v t₀
    _ = ∑ x ∈ s, g x := hsum
    _ = ∑ x ∈ s.filter p, g x + ∑ x ∈ s.filter (fun x => ¬ p x), g x :=
        (Finset.sum_filter_add_sum_filter_not s p g).symm
    _ ≤ 2 * (Fintype.card V : ℝ) + (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) :=
        add_le_add hdeg hnondeg
    _ = (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) + 2 * (Fintype.card V : ℝ) := by ring

/-- **THE PER-ANCHOR `c₀ ≤ ¾` BOUND — Route 0 (threshold `q ≥ 16`).** Drops `c0_le_threequarters_corank`'s `hq3 : 256 ≤ q`
to `hq3 : 16 ≤ q`, by feeding the cap-`d−2` deg bucket (`normT_bucket_bound_corank2`) AND the corank-1 `z_u` bound
(`single_polarRad_finrank_le`) into `c0_le2`. New hypotheses vs `_corank`: `4 ≤ d`, `t₀−u, t₀−v` independent (`hab`),
`Q.polarBilin` nondegenerate (`hQnd`), and the anchor is non-isotropic (`Q (t₀−u) ≠ 0`, `hQu`, which subsumes `hPu`). -/
theorem c0_le_threequarters_corank2 {V : Type*} [AddCommGroup V] [Module K V]
    [Fintype K] [DecidableEq K] [Invertible (2 : K)] [Fintype V] [DecidableEq V] [FiniteDimensional K V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) (b : Basis (Fin d) K V)
    (hd4 : 4 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hab : LinearIndependent K ![t₀ - u, t₀ - v]) (hQnd : Q.polarBilin.Nondegenerate)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
    (hQu : Q (t₀ - u) ≠ 0)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card V)
    (hq3 : 16 ≤ (Fintype.card K : ℝ)) :
    ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ)
      ≤ 3 / 4 * Fintype.card V := by
  classical
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  set T : ℝ := ‖∑ t : V,
      ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖ with hTdef
  have hcount := card_agree_le (K := K) (V := V)
    (fun t => pairForm Q (t₀ - u) (t - u)) (fun t => pairForm Q (t₀ - v) (t - v))
  rw [← hTdef] at hcount
  have hbt := normT_bucket_bound_corank2 hF hψ Q u v t₀ b hd4 hq4 hab hQnd
    (pencilDet_ne_zero_of_good b (pairForm Q (t₀ - u)) (pairForm Q (t₀ - v)) hgood)
  rw [← hTdef] at hbt
  have hT : T ≤ (Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
      + 2 * (Fintype.card V) / (Fintype.card K) := by
    have heq : (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
          + 2 * (Fintype.card V) / (Fintype.card K))
        = (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) + 2 * (Fintype.card V) := by
      field_simp
    refine le_of_mul_le_mul_left ?_ hqpos
    rw [heq]; exact hbt
  -- the corank-1 z_u bound
  have hreindex : (Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
      = (Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card := by
    apply Finset.card_nbij' (fun t => t - u) (fun x => x + u) <;> intro x hx <;> simp_all
  have hzc := zeroCount_sq_le hψ (pairForm Q (t₀ - u))
  have hradnat : (Finset.univ.filter
      (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card
      ≤ Fintype.card K := by
    rw [polarRad_card_filter, Module.natCard_eq_pow_finrank (K := K)
        (V := polarRad (pairForm Q (t₀ - u))), ← Nat.card_eq_fintype_card (α := K)]
    calc Nat.card K ^ finrank K (polarRad (pairForm Q (t₀ - u)))
        ≤ Nat.card K ^ 1 :=
          Nat.pow_le_pow_right Nat.card_pos (single_polarRad_finrank_le Q (t₀ - u) hQnd hQu)
      _ = Nat.card K := by rw [pow_one]
  set zP : ℝ := ((Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card : ℝ) with hzPdef
  set radP : ℝ := ((Finset.univ.filter
      (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card : ℝ) with hradPdef
  have hradle : radP ≤ (Fintype.card K : ℝ) := by rw [hradPdef]; exact_mod_cast hradnat
  have hsq : (zP * Fintype.card K - Fintype.card V) ^ 2
      ≤ ((Fintype.card K - 1 : ℝ) * Real.sqrt (Fintype.card V) * Real.sqrt (Fintype.card K)) ^ 2 := by
    have hrhs : ((Fintype.card K - 1 : ℝ) * Real.sqrt (Fintype.card V) * Real.sqrt (Fintype.card K)) ^ 2
        = (Fintype.card K - 1 : ℝ) ^ 2 * ((Fintype.card V) * (Fintype.card K)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le, Real.sq_sqrt hqpos.le]; ring
    rw [hrhs]
    refine le_trans hzc ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hradle hnpos.le
  have hzu : zP * Fintype.card K ≤ (Fintype.card V : ℝ)
      + (Fintype.card K - 1) * Real.sqrt (Fintype.card V) * Real.sqrt (Fintype.card K) := by
    have hnn0 : (0 : ℝ) ≤ (Fintype.card K - 1) * Real.sqrt (Fintype.card V) * Real.sqrt (Fintype.card K) :=
      mul_nonneg (mul_nonneg (by linarith [hq3]) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have := (abs_le_of_sq_le_sq' hsq hnn0).2
    linarith
  have hfinal := c0_le2 (n := (Fintype.card V : ℝ)) (q := (Fintype.card K : ℝ))
    (T := T) (zu := zP)
    (NS := ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ))
    hnpos hqpos ?_ hT hzu hq1 hq3
  · exact hfinal
  · have hzeq : zP = ((Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card : ℝ) := by
      rw [hzPdef, ← hreindex]
    rw [hzeq]; exact hcount

end ChainDescent

#print axioms ChainDescent.le_two_pow_sub_two
#print axioms ChainDescent.concentration_bound2
#print axioms ChainDescent.deg_bucket_le2
#print axioms ChainDescent.c0_le2
#print axioms ChainDescent.normT_bucket_bound_corank2
#print axioms ChainDescent.c0_le_threequarters_corank2
