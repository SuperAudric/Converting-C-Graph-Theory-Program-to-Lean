/-
# Route 2 tail — the triangle `T`-bound (piece 2) and the capstone (piece 4).

The small-q tail closes via `card_agree_le_tight` (`2·NS ≤ z_u + |V| + T`, `ScratchCountTight`) + tight `z_u = |V|/q` +
the **triangle `T`-bound** built here: `q·T ≤ (q−1)²·q^{d−1}`, i.e. `T ≤ (1−1/q)²·|V|`. From `normT_le`
(`q·T ≤ ∑_{y,z} ‖χy‖‖χz‖·√(|V|·|radical F_{y,z}|)`), bound each term by `(e y)(e z)·q^{d−1}` where `e y = [y≠0]`:
the `‖χy‖=0` rows vanish, and on `y,z≠0` the pencil radical has `corank ≤ d−2` (`pencil_polarRad_finrank_le`), so
`√(|V|·|radical|) ≤ √(q^d·q^{d−2}) = q^{d−1}`. Then `∑ e y = q−1` gives the `(q−1)²` factor. NO `hq3`.

NOT in build (scratch; `lake env lean ChainDescent/ScratchRoute2.lean`). -/
import ChainDescent.ScratchPairSep
import ChainDescent.ScratchPencilCorank2
import ChainDescent.ScratchCorank
import ChainDescent.ScratchCountTight
import ChainDescent.ScratchRoute2Arith

namespace ChainDescent

open Finset Module

section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `‖χ y‖ ≤ [y ≠ 0]` (`= 1` for `y ≠ 0`, `= 0` for `y = 0`), for `χ = (quadraticChar K).ringHomComp (Int.cast ℂ)`. -/
theorem chi_norm_le (y : K) :
    ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖ ≤ (if y = 0 then (0 : ℝ) else 1) := by
  by_cases hy : y = 0
  · simp [hy, MulChar.ringHomComp_apply]
  · rw [if_neg hy]
    rcases quadraticChar_dichotomy hy with h | h <;>
      simp [MulChar.ringHomComp_apply, h]

/-- `∑_y [y ≠ 0] = q − 1`. -/
theorem sum_chi_indicator :
    (∑ y : K, (if y = 0 then (0 : ℝ) else 1)) = (Fintype.card K : ℝ) - 1 := by
  have hsplit : ∀ y : K, (if y = 0 then (0 : ℝ) else 1) = 1 - (if y = 0 then (1 : ℝ) else 0) := by
    intro y; by_cases hy : y = 0 <;> simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq' univ (0 : K) (fun _ => (1 : ℝ))]
  simp

end

section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [FiniteDimensional K V]

/-- **The triangle `T`-bound (Route 2, piece 2).** For a good anchor (`t₀−u, t₀−v` independent, `Q` nondegenerate,
`d ≥ 4`): `q·T ≤ (q−1)²·q^{d−1}`, i.e. `T ≤ (1−1/q)²·|V|`. Each `normT_le` term `‖χy‖‖χz‖·√(|V|·|radical F_{y,z}|)`
is `≤ (e y)(e z)·q^{d−1}` — the `χ=0` rows vanish, and on `y,z≠0` the pencil `corank ≤ d−2` gives `√(…) ≤ q^{d−1}`. -/
theorem normT_triangle (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V)
    (hd : 4 ≤ finrank K V) (hQnd : Q.polarBilin.Nondegenerate)
    (hab : LinearIndependent K ![t₀ - u, t₀ - v]) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ ((Fintype.card K : ℝ) - 1) ^ 2 * (Fintype.card K : ℝ) ^ (finrank K V - 1) := by
  classical
  set qr : ℝ := (Fintype.card K : ℝ) with hqr
  set d : ℕ := finrank K V with hd_def
  have hqpos : (0 : ℝ) < qr := by rw [hqr]; exact_mod_cast Fintype.card_pos
  -- card V = q^d (as ℝ)
  have hcardV : (Fintype.card V : ℝ) = qr ^ d := by
    rw [hqr, hd_def, ← Nat.card_eq_fintype_card (α := K), ← Nat.card_eq_fintype_card (α := V),
      Module.natCard_eq_pow_finrank (K := K) (V := V)]
    push_cast; ring
  -- the per-term bound
  have hterm : ∀ y z : K,
      ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖
        * ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) z‖
        * Real.sqrt ((Fintype.card V : ℝ)
            * (Finset.univ.filter (fun h : V =>
                ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card)
      ≤ (if y = 0 then (0 : ℝ) else 1) * (if z = 0 then (0 : ℝ) else 1) * qr ^ (d - 1) := by
    intro y z
    by_cases hy : y = 0
    · simp [hy, MulChar.ringHomComp_apply]
    by_cases hz : z = 0
    · simp [hz, MulChar.ringHomComp_apply]
    rw [if_neg hy, if_neg hz, one_mul, one_mul]
    -- radical card ≤ q^{d-2}
    have hradNat : (Finset.univ.filter (fun h : V =>
          ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card
        ≤ Fintype.card K ^ (d - 2) := by
      rw [polarRad_card_filter, Module.natCard_eq_pow_finrank (K := K)
            (V := polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v))),
        ← Nat.card_eq_fintype_card (α := K)]
      exact Nat.pow_le_pow_right Nat.card_pos
        (pencil_polarRad_finrank_le Q (t₀ - u) (t₀ - v) y z hd hy hz hQnd hab)
    have hradR : ((Finset.univ.filter (fun h : V =>
          ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card : ℝ)
        ≤ qr ^ (d - 2) := by rw [hqr]; exact_mod_cast hradNat
    -- |V| · radcard ≤ (q^{d-1})²
    have hprod : (Fintype.card V : ℝ)
          * ((Finset.univ.filter (fun h : V =>
              ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card : ℝ)
        ≤ (qr ^ (d - 1)) ^ 2 := by
      rw [hcardV]
      calc qr ^ d * _ ≤ qr ^ d * qr ^ (d - 2) :=
            mul_le_mul_of_nonneg_left hradR (by positivity)
        _ = (qr ^ (d - 1)) ^ 2 := by
            rw [← pow_add, ← pow_mul]; congr 1; omega
    have hsqrt : Real.sqrt ((Fintype.card V : ℝ)
          * ((Finset.univ.filter (fun h : V =>
              ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card : ℝ))
        ≤ qr ^ (d - 1) := by
      rw [show qr ^ (d - 1) = Real.sqrt ((qr ^ (d - 1)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hprod
    calc ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖
            * ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) z‖ * Real.sqrt _
        ≤ 1 * 1 * qr ^ (d - 1) := by
          gcongr
          · exact (chi_norm_le y).trans (by rw [if_neg hy])
          · exact (chi_norm_le z).trans (by rw [if_neg hz])
      _ = qr ^ (d - 1) := by ring
  -- assemble
  calc (Fintype.card K : ℝ) * ‖_‖
      ≤ ∑ y : K, ∑ z : K,
          ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖
            * ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) z‖
            * Real.sqrt ((Fintype.card V : ℝ)
              * (Finset.univ.filter (fun h : V =>
                  ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card) :=
        normT_le hF hψ Q u v t₀
    _ ≤ ∑ y : K, ∑ z : K, (if y = 0 then (0 : ℝ) else 1) * (if z = 0 then (0 : ℝ) else 1) * qr ^ (d - 1) :=
        Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun z _ => hterm y z))
    _ = ((Fintype.card K : ℝ) - 1) ^ 2 * qr ^ (d - 1) := by
        rw [← sum_chi_indicator (K := K), sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_mul]

/-- **Route 2 tail capstone (piece 4).** For a good anchor (`t₀−u, t₀−v` independent, `Q` nondegenerate,
`Q(t₀−u) ≠ 0`, `d ≥ 4`, `|K| ≥ 3` odd) the agreement count `NS = #{t : χ(I_u t) = χ(I_v t)}` satisfies
`4q²·NS ≤ (4q²−1)·|V|`, i.e. `NS ≤ (1 − 1/(4q²))·|V| < |V|` — **NO threshold `hq3`**, closing the odd-char small-q
tail uniformly. Combines `card_agree_le_tight` (count), `normT_triangle` (triangle `T`-bound), the corank-1
`zeroCount_sq_le` (zero count), and `c0_route2_arith` (assembly). -/
theorem c0_le_route2 (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V)
    (hd4 : 4 ≤ finrank K V) (hQnd : Q.polarBilin.Nondegenerate)
    (hab : LinearIndependent K ![t₀ - u, t₀ - v]) (hQu : Q (t₀ - u) ≠ 0)
    (hq3 : 3 ≤ Fintype.card K) :
    4 * (Fintype.card K : ℝ) ^ 2
        * ((Finset.univ.filter (fun t : V =>
            quadraticChar K (pairForm Q (t₀ - u) (t - u))
              = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ)
      ≤ (4 * (Fintype.card K : ℝ) ^ 2 - 1) * Fintype.card V := by
  classical
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  set T : ℝ := ‖∑ t : V,
      ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖ with hTdef
  -- count: 2·NS ≤ #{I_u=0} + |V| + T
  have hcount := card_agree_le_tight (K := K)
    (fun t => pairForm Q (t₀ - u) (t - u)) (fun t => pairForm Q (t₀ - v) (t - v))
  rw [← hTdef] at hcount
  -- card V = q^d
  have hcardpow : (Fintype.card K : ℝ) ^ finrank K V = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card (α := K), ← Nat.card_eq_fintype_card (α := V),
      Module.natCard_eq_pow_finrank (K := K) (V := V)]
    push_cast; ring
  -- triangle: T·q² ≤ (q−1)²·|V|
  have htri := normT_triangle hF hψ Q u v t₀ hd4 hQnd hab
  rw [← hTdef] at htri
  have he : (Fintype.card K : ℝ) * (Fintype.card K) ^ (finrank K V - 1) = Fintype.card V := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ finrank K V), hcardpow]
  have hT : T * (Fintype.card K : ℝ) ^ 2 ≤ (Fintype.card K - 1) ^ 2 * Fintype.card V := by
    have h := mul_le_mul_of_nonneg_left htri hqpos.le
    calc T * (Fintype.card K : ℝ) ^ 2 = (Fintype.card K : ℝ) * ((Fintype.card K) * T) := by ring
      _ ≤ (Fintype.card K : ℝ) * ((Fintype.card K - 1) ^ 2 * (Fintype.card K) ^ (finrank K V - 1)) := h
      _ = (Fintype.card K - 1) ^ 2 * ((Fintype.card K) * (Fintype.card K) ^ (finrank K V - 1)) := by ring
      _ = (Fintype.card K - 1) ^ 2 * Fintype.card V := by rw [he]
  -- zero-count: zP·q ≤ |V| + (q−1)·√|V|·√q  (corank-1)
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
    have hq3R : (3 : ℝ) ≤ Fintype.card K := by exact_mod_cast hq3
    have hnn0 : (0 : ℝ) ≤ (Fintype.card K - 1) * Real.sqrt (Fintype.card V) * Real.sqrt (Fintype.card K) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have := (abs_le_of_sq_le_sq' hsq hnn0).2
    linarith
  -- q⁴ ≤ |V|  (d ≥ 4)
  have hq1 : (Fintype.card K : ℝ) ^ 4 ≤ Fintype.card V := by
    rw [← hcardpow]
    exact pow_le_pow_right₀ (by exact_mod_cast (show (1 : ℕ) ≤ Fintype.card K by omega)) hd4
  -- assemble
  have hfinal := c0_route2_arith (n := (Fintype.card V : ℝ)) (q := (Fintype.card K : ℝ))
    (NS := ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ))
    (zu := zP) (T := T) hnpos hqpos ?_ hzu hT hq1 (by exact_mod_cast hq3)
  · exact hfinal
  · have hzeq : zP = ((Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card : ℝ) := by
      rw [hzPdef, ← hreindex]
    rw [hzeq]; exact hcount

end

#print axioms ChainDescent.chi_norm_le
#print axioms ChainDescent.sum_chi_indicator
#print axioms ChainDescent.normT_triangle
#print axioms ChainDescent.c0_le_route2

end ChainDescent
