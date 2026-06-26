/-
# The corank-stratified `|T|` bound (corank tightening, step C).

The uniform `ScratchTBound.normT_bucket_bound` charges the degenerate bucket `(d·|K|)·(|V|/√|K|)` (whose `d` forces
`ScratchBucket.c0_le`'s `hq2 : 64d²≤q`). Replacing that bucket with `ScratchPencilRegroup.deg_bucket_le` (the corank-
stratified `2·|K|·(|V|/√|K|)`) gives the `d`-free bound here. Feeding it to `c0_le` **with `dR := 2`** makes the
threshold hypothesis `hq2 : 64·2²≤q` become `256 ≤ q` — *exactly the existing `hq3`* — so the `d`-dependent threshold
is removed (no separate `c0_le` needed; the constant case is already covered).

NOT in build (scratch).
-/
import ChainDescent.ScratchTBound
import ChainDescent.ScratchC0
import ChainDescent.ScratchPencilRegroup

namespace ChainDescent

open Finset Module QuadraticMap

/-- **The corank-stratified `|T|` bound (C).** For a good anchor (`hp`: the univariate pencil determinant is nonzero)
with no zero member (`hnz`), `d ≥ 1` and `|K| ≥ 4`, the per-pair character sum `T` satisfies
`|K|·‖T‖ ≤ |K|²·√|V| + 2·|K|·(|V|/√|K|)` — the deg bucket coefficient is the constant `2`, not `d`. -/
theorem normT_bucket_bound_corank {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hd : 1 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hp : (pencilPoly (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q (t₀ - u))))
            (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (pairForm Q (t₀ - v))))).det ≠ 0) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
        + 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K)) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  set P := pairForm Q (t₀ - u) with hP
  set R := pairForm Q (t₀ - v) with hR
  set p : K × K → Prop := fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥ with hp'
  set s : Finset (K × K) := Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0) with hs
  set g : K × K → ℝ := fun x => Real.sqrt ((Fintype.card V : ℝ)
      * (Finset.univ.filter (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card)
    with hg
  -- χ-weight collapse onto the support `s`
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
  -- nondeg bucket magnitude (`g = √|V|`) and count (`≤ |K|²`)
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
  -- nondeg bucket bound
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
  -- degenerate bucket bound (the corank-stratified `2·|K|·(|V|/√|K|)`)
  have hdeg : ∑ x ∈ s.filter p, g x
      ≤ 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K)) :=
    deg_bucket_le b P R hd hq4 hnz hp
  -- assemble
  calc (Fintype.card K : ℝ) * ‖∑ t : V, χ (P (t - u)) * χ (R (t - v))‖
      ≤ ∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z) := normT_le hF hψ Q u v t₀
    _ = ∑ x ∈ s, g x := hsum
    _ = ∑ x ∈ s.filter p, g x + ∑ x ∈ s.filter (fun x => ¬ p x), g x :=
        (Finset.sum_filter_add_sum_filter_not s p g).symm
    _ ≤ 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K))
          + (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V) := add_le_add hdeg hnondeg
    _ = (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
          + 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K)) := by ring

/-- **The `c₀ ≤ ¾` bound with the constant (corank-stratified) deg coefficient — NO `hq2`.** Instantiating
`ScratchBucket.c0_le` at `dR := 2` (the constant from `normT_bucket_bound_corank`): the original `hq2 : 64·dR² ≤ q`
becomes `64·2² = 256 ≤ q`, which is exactly the already-present `hq3`. So the `d`-dependent threshold is gone — the
binding hypotheses are just `hq1` (`d ≥ 3`) and `hq3 : 256 ≤ q`. -/
theorem c0_le_const {n q T zu NS : ℝ} (hn : 0 < n) (hq : 0 < q)
    (hcount : 2 * NS ≤ 2 * zu + n + T)
    (hT : T ≤ q * Real.sqrt n + 2 * n / Real.sqrt q)
    (hzu : zu * q ≤ n + (q - 1) * n / Real.sqrt q)
    (hq1 : 64 * q ^ 2 ≤ n) (hq3 : 256 ≤ q) :
    NS ≤ 3 / 4 * n :=
  c0_le hn hq (by norm_num) hcount hT hzu hq1 (by norm_num; linarith) hq3

/-- **THE PER-ANCHOR `c₀ ≤ ¾` BOUND — corank-tightened (NO `hq2`).** Identical to `ScratchC0Final.c0_le_threequarters`
except the deg bucket is the corank-stratified `normT_bucket_bound_corank` and the final arithmetic is `c0_le_const`
(`dR := 2`): the `64·d² ≤ q` threshold is **gone**, replaced by `d ≥ 1`/`|K| ≥ 4` (subsumed by the surviving
`hq1, hq3`). Determines the family threshold: `VO⁻₄(q)` drops from `q ≥ 1024` to `q ≥ 256`. -/
theorem c0_le_threequarters_corank {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hd : 1 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
    (hPu : pairForm Q (t₀ - u) ≠ 0)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card V)
    (hq3 : 256 ≤ (Fintype.card K : ℝ)) :
    ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ)
      ≤ 3 / 4 * Fintype.card V := by
  classical
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsqqpos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.2 hqpos
  set T : ℝ := ‖∑ t : V,
      ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖ with hTdef
  -- (1) counting identity
  have hcount := card_agree_le (K := K) (V := V)
    (fun t => pairForm Q (t₀ - u) (t - u)) (fun t => pairForm Q (t₀ - v) (t - v))
  rw [← hTdef] at hcount
  -- (2) the corank-stratified |T| bound, divided by q
  have hbt := normT_bucket_bound_corank hF hψ Q u v t₀ b hd hq4 hnz
    (pencilDet_ne_zero_of_good b (pairForm Q (t₀ - u)) (pairForm Q (t₀ - v)) hgood)
  rw [← hTdef] at hbt
  have hT : T ≤ (Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
      + 2 * (Fintype.card V) / Real.sqrt (Fintype.card K) := by
    have heq : (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
          + 2 * (Fintype.card V) / Real.sqrt (Fintype.card K))
        = (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
          + 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K)) := by ring
    refine le_of_mul_le_mul_left ?_ hqpos
    rw [heq]; exact hbt
  -- (3) the z_u bound (verbatim from `c0_le_threequarters`)
  have hreindex : (Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
      = (Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card := by
    apply Finset.card_nbij' (fun t => t - u) (fun x => x + u) <;> intro x hx <;> simp_all
  have hzc := zeroCount_sq_le hψ (pairForm Q (t₀ - u))
  have hradR : ((Finset.univ.filter
        (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card : ℝ)
        * (Fintype.card K : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast radical_card_mul_card_le (pairForm Q (t₀ - u)) hPu
  set zP : ℝ := ((Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card : ℝ) with hzPdef
  set radP : ℝ := ((Finset.univ.filter
      (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card : ℝ) with hradPdef
  have hKnn : 0 ≤ (Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K) :=
    div_nonneg (by nlinarith [hq3, hnpos.le]) hsqqpos.le
  have hsq : (zP * Fintype.card K - Fintype.card V) ^ 2
      ≤ ((Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K)) ^ 2 := by
    have hKsq : ((Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K)) ^ 2
        = (Fintype.card K - 1 : ℝ) ^ 2 * ((Fintype.card V) * (Fintype.card V / Fintype.card K)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hqpos.le]; ring
    rw [hKsq]
    refine le_trans hzc ?_
    have hradle : radP ≤ (Fintype.card V : ℝ) / Fintype.card K :=
      (le_div_iff₀ hqpos).2 (by linarith [hradR])
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hradle hnpos.le) (by positivity)
  have hzu : zP * Fintype.card K ≤ (Fintype.card V : ℝ)
      + (Fintype.card K - 1) * (Fintype.card V) / Real.sqrt (Fintype.card K) := by
    have := (abs_le_of_sq_le_sq' hsq hKnn).2
    linarith
  -- assemble via `c0_le_const` (dR = 2, no hq2)
  have hfinal := c0_le_const (n := (Fintype.card V : ℝ)) (q := (Fintype.card K : ℝ))
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

#print axioms ChainDescent.normT_bucket_bound_corank
#print axioms ChainDescent.c0_le_const
#print axioms ChainDescent.c0_le_threequarters_corank
