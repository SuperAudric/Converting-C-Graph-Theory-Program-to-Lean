/-
# Increment 4 — constructing the bad-anchor representing polynomial `P` (SCRATCH).

`ScratchIncr4b` reduced the bad-anchor count `β` to ONE obligation: a nonzero `P : MvPolynomial (Fin d) K` that
*represents the pencil determinant* — `eval (b.equivFun t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u +
z₀•pairForm_v)))` — at a fixed witness `(y₀,z₀)`. **This module BUILDS that `P` (12 lemmas, all axiom-clean), closing
`β` modulo non-vacuity.**

* **Layer 1 — coordinatization workhorse.** A linear functional `f : V →ₗ[K] K` ↦ `coordPoly (fun k => f (b k)) =
  ∑ₖ C(f bₖ)·Xₖ`, evaluating at `x = b.equivFun t₀` to `f t₀` (`coordPoly_eval_linFunc`).
* **Layer 2 — the quadratic `Q(t₀)`** via the diagonal double-sum `polar_t0_t0_sum` (`polar Q t₀ t₀ = ∑_{k,l}
  xₖxₗ·polar Q bₖ bₗ`) + `gramQuadPoly_eval` (`Q = ½·polar`, needs `Invertible 2`).
* **Layer 3 — the affine `LPoly`/`QPoly`** (`polar Q w (t₀−c)`, `Q(t₀−c)`).
* **Layer 4 — the Gram entry + determinant**: `polar_pairForm_apply`, `entryPoly`/`entryPoly_eval`, then
  `pencilDetPoly := det(Matrix.of (C y₀·entryPoly_u + C z₀·entryPoly_v))` with `pencilDetPoly_eval` (`eval`-correct by
  `RingHom.map_det`) + `pencilDetPoly_ne_zero` (good-anchor witness). Capstone **`badHgood_count_le`:
  `#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`** (= `O(d/q)` density).

`β` is thereby CLOSED modulo: (i) non-vacuity `hgood` (∃ good anchor for `u≠v` = distinct radicals, a hypothesis);
(ii) the trivial `β ≤ #{¬hgood}+2` composition with `ScratchIncr4b.bad_anchor_card_le_hgood` (deferred to inc-5 to dodge
a cosmetic cross-module `Classical.propDecidable` mismatch on the `{¬hgood}` filter); (iii) an optional
`totalDegree(pencilDetPoly) ≤ 2d` polish (for the explicit `O(d/q)`).

NOT in build (scratch; `lake env lean ChainDescent/ScratchIncr4c.lean`, after `lake build ChainDescent.ScratchIncr4b`).
-/
import ChainDescent.BadAnchorCount

namespace ChainDescent

open Finset Module MvPolynomial Matrix

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {d : ℕ} (b : Basis (Fin d) K V)

/-- The degree-`≤1` polynomial with coefficient function `g` on the coordinate variables. -/
noncomputable def coordPoly (g : Fin d → K) : MvPolynomial (Fin d) K :=
  ∑ k, C (g k) * X k

@[simp] theorem coordPoly_eval (g : Fin d → K) (x : Fin d → K) :
    MvPolynomial.eval x (coordPoly g) = ∑ k, g k * x k := by
  simp only [coordPoly, map_sum, map_mul, eval_C, eval_X]

/-- A linear functional expanded over the basis: `f t₀ = ∑ₖ f(bₖ)·(coords t₀)ₖ`. -/
theorem linFunc_eq_sum (f : V →ₗ[K] K) (t₀ : V) :
    f t₀ = ∑ k, f (b k) * b.equivFun t₀ k := by
  conv_lhs => rw [← b.sum_repr t₀]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, b.equivFun_apply, mul_comm]

/-- **The coordinatization workhorse.** A linear functional `f` is represented by `coordPoly (f ∘ b)`: its evaluation
at the coordinates of `t₀` is `f t₀`. -/
theorem coordPoly_eval_linFunc (f : V →ₗ[K] K) (t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (coordPoly (fun k => f (b k))) = f t₀ := by
  rw [coordPoly_eval, ← linFunc_eq_sum b f t₀]

/-- The diagonal bilinear expansion `polar Q t₀ t₀ = ∑_{k,l} polar Q bₖ bₗ · xₗ · xₖ` (`x = coords t₀`), by applying
the linear-functional expansion twice (`polarBilin Q` is bilinear). -/
theorem polar_t0_t0_sum (Q : QuadraticForm K V) (t₀ : V) :
    QuadraticMap.polar Q t₀ t₀
      = ∑ k, ∑ l, QuadraticMap.polar Q (b k) (b l) * b.equivFun t₀ l * b.equivFun t₀ k := by
  have h1 : QuadraticMap.polar Q t₀ t₀
      = ∑ k, QuadraticMap.polar Q (b k) t₀ * b.equivFun t₀ k := by
    have h := linFunc_eq_sum b ((QuadraticMap.polarBilin Q).flip t₀) t₀
    simpa only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply] using h
  rw [h1]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h2 : QuadraticMap.polar Q (b k) t₀
      = ∑ l, QuadraticMap.polar Q (b k) (b l) * b.equivFun t₀ l := by
    have h := linFunc_eq_sum b (QuadraticMap.polarBilin Q (b k)) t₀
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  rw [h2, Finset.sum_mul]

/-- The polynomial representing `Q(t₀)` (the diagonal Gram quadratic, scaled by `⅟2`). -/
noncomputable def gramQuadPoly [Invertible (2 : K)] (Q : QuadraticForm K V) : MvPolynomial (Fin d) K :=
  C (⅟(2 : K)) * ∑ k, ∑ l, C (QuadraticMap.polar Q (b k) (b l)) * (X l * X k)

theorem gramQuadPoly_eval [Invertible (2 : K)] (Q : QuadraticForm K V) (t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (gramQuadPoly b Q) = Q t₀ := by
  rw [gramQuadPoly, eval_mul, eval_C]
  have hsum : MvPolynomial.eval (b.equivFun t₀)
      (∑ k, ∑ l, C (QuadraticMap.polar Q (b k) (b l)) * (X l * X k))
      = QuadraticMap.polar Q t₀ t₀ := by
    rw [polar_t0_t0_sum b Q t₀, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, eval_C, map_mul, eval_X, eval_X, mul_assoc]
  rw [hsum, QuadraticMap.polar_self, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, invOf_mul_self, one_mul]

/-- The polynomial representing the affine-linear `polar Q w (t₀ − c)`. -/
noncomputable def LPoly (Q : QuadraticForm K V) (w c : V) : MvPolynomial (Fin d) K :=
  coordPoly (fun k => QuadraticMap.polar Q w (b k)) - C (QuadraticMap.polar Q w c)

theorem LPoly_eval (Q : QuadraticForm K V) (w c t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (LPoly b Q w c) = QuadraticMap.polar Q w (t₀ - c) := by
  rw [LPoly, map_sub, eval_C,
    show (fun k => QuadraticMap.polar Q w (b k)) = (fun k => (QuadraticMap.polarBilin Q w) (b k)) from
      by funext k; rw [QuadraticMap.polarBilin_apply_apply],
    coordPoly_eval_linFunc b (QuadraticMap.polarBilin Q w) t₀, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_sub_right]

/-- The polynomial representing the quadratic `Q (t₀ − c)`. -/
noncomputable def QPoly [Invertible (2 : K)] (Q : QuadraticForm K V) (c : V) : MvPolynomial (Fin d) K :=
  gramQuadPoly b Q + C (Q c) - coordPoly (fun k => QuadraticMap.polar Q c (b k))

theorem QPoly_eval [Invertible (2 : K)] (Q : QuadraticForm K V) (c t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (QPoly b Q c) = Q (t₀ - c) := by
  have hid : Q (t₀ - c) = Q t₀ + Q c - QuadraticMap.polar Q t₀ c := by
    have e1 : QuadraticMap.polar Q t₀ (-c) = Q (t₀ + -c) - Q t₀ - Q (-c) := rfl
    rw [QuadraticMap.polar_neg_right, ← sub_eq_add_neg, QuadraticMap.map_neg] at e1
    linear_combination -e1
  rw [QPoly, map_sub, map_add, eval_C, gramQuadPoly_eval,
    show (fun k => QuadraticMap.polar Q c (b k)) = (fun k => (QuadraticMap.polarBilin Q c) (b k)) from
      by funext k; rw [QuadraticMap.polarBilin_apply_apply],
    coordPoly_eval_linFunc b (QuadraticMap.polarBilin Q c) t₀, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm Q c t₀, hid]

/-- The general polar of `pairForm Q a`: `polar(pairForm Q a) s r = 4 Q(a)·polar Q s r − 2·polar Q s a·polar Q r a`
(the `r = a` case is `pairForm_polar_anchor`). -/
theorem polar_pairForm_apply (Q : QuadraticForm K V) (a s r : V) :
    QuadraticMap.polar (pairForm Q a) s r
      = 4 * Q a * QuadraticMap.polar Q s r
        - 2 * (QuadraticMap.polar Q s a * QuadraticMap.polar Q r a) := by
  rw [QuadraticMap.polar, pairForm_apply, pairForm_apply, pairForm_apply]
  have hQ : Q (s + r) = Q s + Q r + QuadraticMap.polar Q s r := by rw [QuadraticMap.polar]; ring
  have hp : QuadraticMap.polar Q (s + r) a
      = QuadraticMap.polar Q s a + QuadraticMap.polar Q r a := QuadraticMap.polar_add_left Q s r a
  rw [hQ, hp]; ring

/-- The polynomial representing the Gram entry `polar(pairForm Q (t₀−a))(bᵢ)(bⱼ)`. -/
noncomputable def entryPoly [Invertible (2 : K)] (Q : QuadraticForm K V) (a : V) (i j : Fin d) :
    MvPolynomial (Fin d) K :=
  C (4 * QuadraticMap.polar Q (b i) (b j)) * QPoly b Q a
    - C 2 * (LPoly b Q (b i) a * LPoly b Q (b j) a)

theorem entryPoly_eval [Invertible (2 : K)] (Q : QuadraticForm K V) (a : V) (i j : Fin d) (t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (entryPoly b Q a i j)
      = QuadraticMap.polar (pairForm Q (t₀ - a)) (b i) (b j) := by
  rw [entryPoly, map_sub, map_mul, eval_C, map_mul, eval_C, map_mul, QPoly_eval, LPoly_eval,
    LPoly_eval, polar_pairForm_apply]
  ring

/-- **The representing polynomial `P`** for the pencil determinant at witness `(y₀,z₀)`: the determinant of the
`d×d` matrix of Gram-entry polynomials. -/
noncomputable def pencilDetPoly [Invertible (2 : K)] (Q : QuadraticForm K V) (y₀ z₀ : K) (u v : V) :
    MvPolynomial (Fin d) K :=
  (Matrix.of (fun i j => C y₀ * entryPoly b Q u i j + C z₀ * entryPoly b Q v i j)).det

/-- **`P` represents the pencil determinant** — `eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u +
z₀•pairForm_v)))`. Via `RingHom.map_det` (eval is a ring hom) + the per-entry `entryPoly_eval` + `polar_pencil`. -/
theorem pencilDetPoly_eval [Invertible (2 : K)] (Q : QuadraticForm K V) (y₀ z₀ : K) (u v t₀ : V) :
    MvPolynomial.eval (b.equivFun t₀) (pencilDetPoly b Q y₀ z₀ u v)
      = (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin
          (y₀ • pairForm Q (t₀ - u) + z₀ • pairForm Q (t₀ - v)))).det := by
  rw [pencilDetPoly, RingHom.map_det (MvPolynomial.eval (b.equivFun t₀))]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, LinearMap.toMatrix₂_apply,
    QuadraticMap.polarBilin_apply_apply, polar_pencil, map_add, map_mul, map_mul, eval_C, eval_C,
    entryPoly_eval, entryPoly_eval]

/-- **`P ≠ 0`** when there is a good anchor `t₀₀` with witness `(y₀,z₀)` (`polarRad = ⊥` there): the determinant is
nonzero at `t₀₀`'s coordinates (`polarRad_ne_bot_iff_det_eq_zero`), so the polynomial cannot vanish identically. -/
theorem pencilDetPoly_ne_zero [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (y₀ z₀ : K) (u v t₀₀ : V)
    (hgood : polarRad (y₀ • pairForm Q (t₀₀ - u) + z₀ • pairForm Q (t₀₀ - v)) = ⊥) :
    pencilDetPoly b Q y₀ z₀ u v ≠ 0 := by
  intro h0
  have hev : MvPolynomial.eval (b.equivFun t₀₀) (pencilDetPoly b Q y₀ z₀ u v) = 0 := by
    rw [h0]; simp
  rw [pencilDetPoly_eval] at hev
  exact (polarRad_ne_bot_iff_det_eq_zero b _).mpr hev hgood

/-! ### B-iii — the explicit degree bound `totalDegree (pencilDetPoly) ≤ 2·d`.

`badHgood_count_le`'s `#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|` is only an *explicit* `O(d/q)` density once
the determinant's degree is pinned. The layers cap cleanly: `coordPoly`/`LPoly` are linear (`≤ 1`),
`gramQuadPoly`/`QPoly`/`entryPoly` are quadratic (`≤ 2`), and the determinant of a `d × d` matrix of quadratic
entries has `totalDegree ≤ 2·d` (`det_totalDegree_le_gen`, the bounded-degree generalization of
`ScratchGoodAnchor.det_totalDegree_le`). -/

/-- **Per-entry degree bound for a determinant (general `D`).** Generalizes `ScratchGoodAnchor.det_totalDegree_le`
(linear pencil, `D = 1`, `Fin 2` variables) to entries of `totalDegree ≤ D` over any variable type: the determinant
of a `d × d` matrix has `totalDegree ≤ D · d`. -/
theorem det_totalDegree_le_gen {R : Type*} [CommRing R] {n : ℕ} {τ : Type*}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial τ R)) (D : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    M.det.totalDegree ≤ D * n := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun σ _ => ?_))
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i : Fin n, (M (σ i) i).totalDegree
      ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = D * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; exact mul_comm n D

theorem coordPoly_totalDegree_le (g : Fin d → K) : (coordPoly g).totalDegree ≤ 1 := by
  rw [coordPoly]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun k _ => ?_))
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hX := MvPolynomial.totalDegree_X (σ := Fin d) (R := K) k
  rw [MvPolynomial.totalDegree_C]; omega

theorem gramQuadPoly_totalDegree_le [Invertible (2 : K)] (Q : QuadraticForm K V) :
    (gramQuadPoly b Q).totalDegree ≤ 2 := by
  rw [gramQuadPoly]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun k _ => ?_))
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun l _ => ?_))
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hX1 := MvPolynomial.totalDegree_X (σ := Fin d) (R := K) l
  have hX2 := MvPolynomial.totalDegree_X (σ := Fin d) (R := K) k
  omega

theorem LPoly_totalDegree_le (Q : QuadraticForm K V) (w c : V) :
    (LPoly b Q w c).totalDegree ≤ 1 := by
  rw [LPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  exact ⟨coordPoly_totalDegree_le _, by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1⟩

theorem QPoly_totalDegree_le [Invertible (2 : K)] (Q : QuadraticForm K V) (c : V) :
    (QPoly b Q c).totalDegree ≤ 2 := by
  rw [QPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, (coordPoly_totalDegree_le _).trans (by norm_num)⟩
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  exact ⟨gramQuadPoly_totalDegree_le b Q, by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 2⟩

theorem entryPoly_totalDegree_le [Invertible (2 : K)] (Q : QuadraticForm K V) (a : V) (i j : Fin d) :
    (entryPoly b Q a i j).totalDegree ≤ 2 := by
  rw [entryPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact QPoly_totalDegree_le b Q a
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := LPoly_totalDegree_le b Q (b i) a
    have h2 := LPoly_totalDegree_le b Q (b j) a
    omega

/-- **`totalDegree (pencilDetPoly) ≤ 2·d`** (B-iii). The determinant of the `d × d` matrix of quadratic Gram-entry
polynomials, via `det_totalDegree_le_gen` at `D = 2` (each entry `C y₀·entryPoly_u + C z₀·entryPoly_v` is quadratic). -/
theorem pencilDetPoly_totalDegree_le [Invertible (2 : K)] (Q : QuadraticForm K V) (y₀ z₀ : K) (u v : V) :
    (pencilDetPoly b Q y₀ z₀ u v).totalDegree ≤ 2 * d := by
  rw [pencilDetPoly]
  refine det_totalDegree_le_gen _ 2 (fun i j => ?_)
  rw [Matrix.of_apply]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩ <;>
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact entryPoly_totalDegree_le b Q _ i j

open scoped Classical in
/-- **`#{¬hgood}` bounded — the bad-anchor Schwartz–Zippel count.** Instantiating `bad_anchor_count_le_of_poly` at the
constructed `P = pencilDetPoly` (nonzero by the good-anchor witness, representing by `pencilDetPoly_eval`):
`#{t₀ : ¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`, i.e. density `≤ totalDegree/q = O(d/q)`. -/
theorem badHgood_count_le [Fintype K] [DecidableEq K] [Fintype V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (y₀ z₀ : K) (u v t₀₀ : V)
    (hgood : polarRad (y₀ • pairForm Q (t₀₀ - u) + z₀ • pairForm Q (t₀₀ - v)) = ⊥) :
    (univ.filter (fun t₀ : V =>
        ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card
        * Fintype.card K
      ≤ (pencilDetPoly b Q y₀ z₀ u v).totalDegree * Fintype.card V :=
  bad_anchor_count_le_of_poly b _ (pencilDetPoly b Q y₀ z₀ u v)
    (pencilDetPoly_ne_zero b Q y₀ z₀ u v t₀₀ hgood)
    (notHgood_eval_zero_of_repr b Q y₀ z₀ u v _ (pencilDetPoly_eval b Q y₀ z₀ u v))

include b in
open scoped Classical in
/-- **B-ii — `β` closed to an explicit `O(d/q)` bound.** Composing `badHgood_count_le` (`#{¬hgood}·|K| ≤
(pencilDetPoly).totalDegree·|V|`) with B-iii (`pencilDetPoly_totalDegree_le`, `totalDegree ≤ 2d`) and the landed
`ScratchIncr4b.bad_anchor_card_le_hgood` (`β ≤ #{¬hgood} + 2`): the **full** bad-anchor count
`β = #{t₀ : ¬(hnz ∧ hgood ∧ hPu ∧ hPv)}` obeys `β·|K| ≤ 2d·|V| + 2·|K|`, i.e. density `β/|V| ≤ 2d/q + 2/|V| = O(d/q)`.
The only premise is **non-vacuity** `hgood` (∃ good anchor for `u≠v`, the "distinct radicals" condition — increment-4
item NV). Both `{¬hgood}` filters use `Classical.propDecidable` (`open scoped Classical`), so the composition is clean. -/
theorem beta_count_closed [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (y₀ z₀ : K) (u v t₀₀ : V)
    (hgood : polarRad (y₀ • pairForm Q (t₀₀ - u) + z₀ • pairForm Q (t₀₀ - v)) = ⊥) :
    (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card * Fintype.card K
      ≤ 2 * d * Fintype.card V + 2 * Fintype.card K := by
  -- restate the cross-module reduction with *this* module's `Classical.propDecidable` instances
  -- (the predicates are identical; only the `DecidablePred` instances differ, and they are subsingletons)
  have h1 : (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
      ≤ (univ.filter (fun t₀ : V => ¬ ∃ y z : K,
            polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2 := by
    convert bad_anchor_card_le_hgood (K := K) Q u v using 2 <;> congr!
  have key : (univ.filter (fun t₀ : V => ¬ ∃ y z : K,
        polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card * Fintype.card K
      ≤ 2 * d * Fintype.card V :=
    le_trans (badHgood_count_le b Q y₀ z₀ u v t₀₀ hgood)
      (Nat.mul_le_mul_right _ (pencilDetPoly_totalDegree_le b Q y₀ z₀ u v))
  calc (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card * Fintype.card K
      ≤ ((univ.filter (fun t₀ : V => ¬ ∃ y z : K,
            polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2)
          * Fintype.card K :=
        Nat.mul_le_mul_right _ h1
    _ = (univ.filter (fun t₀ : V => ¬ ∃ y z : K,
            polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card * Fintype.card K
          + 2 * Fintype.card K := by ring
    _ ≤ 2 * d * Fintype.card V + 2 * Fintype.card K := Nat.add_le_add_right key _

/-! ### C-corr — the corr-killing anchor conditions `Q(t₀−u) ≠ 0`, `Q(t₀−v) ≠ 0`.

The bridge `ScratchBridgeD.jointIsoCount_ne_of_chiSep_pair` carries `hcorru/hcorrv` — `¬(Q(t−u)=0 ∧ Q(t₀−u)=0)` for
every probe `t`. A *good anchor* with `Q(t₀−u) ≠ 0` discharges this for ALL `t` (the second conjunct is false), so
`corr` is killed at the anchor level (`corr_zero_of_anchor`). The price is two more bad-anchor loci `{t₀ : Q(t₀−u)=0}`,
`{t₀ : Q(t₀−v)=0}`, each a quadric counted by the SAME Schwartz–Zippel engine on `QPoly` (`QPoly_eval = Q(t₀−c)`,
`QPoly_totalDegree_le : ≤ 2`), folding `corr` into `β` at density `O(1/q)`. -/

/-- A good anchor (`Q(t₀−u) ≠ 0`) kills the bridge's `corr` condition for every probe `t`: `¬(Q(t−u)=0 ∧ Q(t₀−u)=0)`. -/
theorem corr_zero_of_anchor (Q : QuadraticForm K V) (u t₀ : V) (h : Q (t₀ - u) ≠ 0) (t : V) :
    ¬ (Q (t - u) = 0 ∧ Q (t₀ - u) = 0) := fun hc => h hc.2

/-- `QPoly b Q c ≠ 0` whenever the form is nonzero somewhere (`Q w₀ ≠ 0`): its value at `t₀ = w₀ + c` is `Q w₀ ≠ 0`. -/
theorem QPoly_ne_zero [Invertible (2 : K)] (Q : QuadraticForm K V) (c w₀ : V) (hw₀ : Q w₀ ≠ 0) :
    QPoly b Q c ≠ 0 := by
  intro h0
  have hev := QPoly_eval b Q c (w₀ + c)
  rw [h0, map_zero, add_sub_cancel_right] at hev
  exact hw₀ hev.symm

include b in
/-- **The corr-locus count.** `#{t₀ : Q(t₀−c)=0}·|K| ≤ 2·|V|` (a quadric in `t₀`), via the SZ engine on `QPoly`
(`QPoly_eval`/`QPoly_totalDegree_le`). -/
theorem qZero_count_le [Fintype K] [DecidableEq K] [Fintype V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (c w₀ : V) (hw₀ : Q w₀ ≠ 0) :
    (univ.filter (fun t₀ : V => Q (t₀ - c) = 0)).card * Fintype.card K ≤ 2 * Fintype.card V := by
  calc (univ.filter (fun t₀ : V => Q (t₀ - c) = 0)).card * Fintype.card K
      ≤ (QPoly b Q c).totalDegree * Fintype.card V :=
        bad_anchor_count_le_of_poly b (fun t₀ => Q (t₀ - c) = 0) (QPoly b Q c)
          (QPoly_ne_zero b Q c w₀ hw₀) (fun t₀ h => by rw [QPoly_eval]; exact h)
    _ ≤ 2 * Fintype.card V := by gcongr; exact QPoly_totalDegree_le b Q c

include b in
open scoped Classical in
/-- **C-corr capstone — the FULL bad-anchor count, including the two corr-killing loci.** The bridge's good-anchor
predicate is `hnz ∧ hgood ∧ hPu ∧ hPv ∧ Q(t₀−u)≠0 ∧ Q(t₀−v)≠0` (the last two kill `corr`, `corr_zero_of_anchor`). Its
complement `β_full ⊆ {¬(hnz∧hgood∧hPu∧hPv)} ∪ {Q(t₀−u)=0} ∪ {Q(t₀−v)=0}`, so `beta_count_closed` (`≤ 2d·|V|+2·|K|`) +
two `qZero_count_le` (`≤ 2·|V|` each) give **`β_full·|K| ≤ (2d+4)·|V| + 2·|K| = O(d/q)`**. Premises: non-vacuity `hgood`
(item NV) + the form is nonzero somewhere (`Q w₀ ≠ 0`, automatic for a nondegenerate `Q`). -/
theorem beta_full_count_closed [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (y₀ z₀ : K) (u v t₀₀ w₀ : V)
    (hgood : polarRad (y₀ • pairForm Q (t₀₀ - u) + z₀ • pairForm Q (t₀₀ - v)) = ⊥)
    (hw₀ : Q w₀ ≠ 0) :
    (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0
          ∧ Q (t₀ - u) ≠ 0 ∧ Q (t₀ - v) ≠ 0))).card * Fintype.card K
      ≤ (2 * d + 4) * Fintype.card V + 2 * Fintype.card K := by
  have hb := beta_count_closed b Q y₀ z₀ u v t₀₀ hgood
  have hu := qZero_count_le b Q u w₀ hw₀
  have hv' := qZero_count_le b Q v w₀ hw₀
  have hcard : (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0
          ∧ Q (t₀ - u) ≠ 0 ∧ Q (t₀ - v) ≠ 0))).card
      ≤ (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
        + (univ.filter (fun t₀ : V => Q (t₀ - u) = 0)).card
        + (univ.filter (fun t₀ : V => Q (t₀ - v) = 0)).card := by
    have hsub : (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0
            ∧ Q (t₀ - u) ≠ 0 ∧ Q (t₀ - v) ≠ 0)))
        ⊆ (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0)))
          ∪ (univ.filter (fun t₀ : V => Q (t₀ - u) = 0))
          ∪ (univ.filter (fun t₀ : V => Q (t₀ - v) = 0)) := by
      intro t₀ ht
      simp only [mem_filter, mem_univ, true_and, mem_union] at ht ⊢
      by_cases hE : Q (t₀ - u) = 0
      · exact Or.inl (Or.inr hE)
      · by_cases hF : Q (t₀ - v) = 0
        · exact Or.inr hF
        · exact Or.inl (Or.inl (fun hbase =>
            ht ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, hE, hF⟩))
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ + (univ.filter (fun t₀ : V => Q (t₀ - v) = 0)).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  calc (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0
            ∧ Q (t₀ - u) ≠ 0 ∧ Q (t₀ - v) ≠ 0))).card * Fintype.card K
      ≤ ((univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
          + (univ.filter (fun t₀ : V => Q (t₀ - u) = 0)).card
          + (univ.filter (fun t₀ : V => Q (t₀ - v) = 0)).card) * Fintype.card K :=
        Nat.mul_le_mul_right _ hcard
    _ = (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card * Fintype.card K
          + (univ.filter (fun t₀ : V => Q (t₀ - u) = 0)).card * Fintype.card K
          + (univ.filter (fun t₀ : V => Q (t₀ - v) = 0)).card * Fintype.card K := by ring
    _ ≤ (2 * d * Fintype.card V + 2 * Fintype.card K) + 2 * Fintype.card V + 2 * Fintype.card V :=
        Nat.add_le_add (Nat.add_le_add hb hu) hv'
    _ = (2 * d + 4) * Fintype.card V + 2 * Fintype.card K := by ring

/-! ### C-basis — the ortho-anisotropic basis the bridge carries (`hv`/`hw`).

`ScratchBridgeD.jointIsoCount_ne_of_chiSep_pair` carries an orthogonal basis `vb` for `associated Q` with every
`Q (vb i) ≠ 0` (`hv : (associated Q).IsOrthoᵢ vb`, `hw : ∀ i, Q (vb i) ≠ 0`). These are NOT anchor/probe-dependent —
they are a property of the form `Q` itself, available from nondegeneracy (`SeparatingLeft`):
- `vb`/`hv` from Mathlib's `exists_orthogonal_basis` (a symmetric bilinear form over a field with `2` invertible
  diagonalizes);
- `hw` from `IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft` — a diagonal basis vector with `(associated Q)(vb i)(vb i)=0`
  would lie in the left radical, contradicting nondegeneracy; and `(associated Q)(vb i)(vb i) = Q (vb i)`. -/

/-- **C-basis.** A nondegenerate (`SeparatingLeft`) quadratic form `Q` over a finite-dimensional space (char ≠ 2) has an
**orthogonal basis of anisotropic vectors** — exactly the `vb`/`hv`/`hw` the bridge `jointIsoCount_ne_of_chiSep_pair`
carries. A `Q`-level fact (no anchor/probe), discharged once when the family supplies its nondegenerate form. -/
theorem exists_orthoAnisotropic_basis [Invertible (2 : K)] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hsep : (QuadraticMap.associated Q).SeparatingLeft) :
    ∃ vb : Basis (Fin (Module.finrank K V)) K V,
      (QuadraticMap.associated Q).IsOrthoᵢ vb ∧ ∀ i, Q (vb i) ≠ 0 := by
  obtain ⟨vb, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm K Q)
  refine ⟨vb, hv, fun i hQ0 => hv.not_isOrtho_basis_self_of_separatingLeft hsep i ?_⟩
  change (QuadraticMap.associated Q) (vb i) (vb i) = 0
  rw [QuadraticMap.associated_eq_self_apply]
  exact hQ0

/-- **Bridge to the project-native nondegeneracy.** `polarRad Q = ⊥` (the form used throughout — `hgood`,
`degenerate_count_le`, `polarRad_ne_bot_iff_det_eq_zero`) gives `(associated Q).SeparatingLeft`, the hypothesis of
`exists_orthoAnisotropic_basis`. Chain: `polarRad = ⊥ ↔ (polarBilin Q).SeparatingRight` (`polarRad_eq_bot_iff_separatingRight`),
and `polarBilin Q x z = 2 • associated Q x z` (`two_nsmul_associated`) makes the two separating conditions agree (char ≠ 2),
modulo `polar`-symmetry. -/
theorem associated_separatingLeft_of_polarRad [Invertible (2 : K)] (Q : QuadraticForm K V)
    (h : polarRad Q = ⊥) : (QuadraticMap.associated Q).SeparatingLeft := by
  rw [polarRad_eq_bot_iff_separatingRight] at h
  intro x hx
  refine h x ?_
  intro z
  have e2 : (QuadraticMap.polarBilin Q) x z = (2 : ℕ) • (QuadraticMap.associated Q) x z := by
    conv_lhs => rw [← QuadraticMap.two_nsmul_associated (S := K)]
    simp only [two_nsmul, LinearMap.add_apply]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, e2, hx z, smul_zero]

end ChainDescent

--#print axioms ChainDescent.coordPoly_eval
--#print axioms ChainDescent.linFunc_eq_sum
--#print axioms ChainDescent.coordPoly_eval_linFunc
--#print axioms ChainDescent.polar_t0_t0_sum
--#print axioms ChainDescent.gramQuadPoly_eval
--#print axioms ChainDescent.LPoly_eval
--#print axioms ChainDescent.QPoly_eval
--#print axioms ChainDescent.polar_pairForm_apply
--#print axioms ChainDescent.entryPoly_eval
--#print axioms ChainDescent.pencilDetPoly_eval
--#print axioms ChainDescent.pencilDetPoly_ne_zero
--#print axioms ChainDescent.det_totalDegree_le_gen
--#print axioms ChainDescent.coordPoly_totalDegree_le
--#print axioms ChainDescent.gramQuadPoly_totalDegree_le
--#print axioms ChainDescent.LPoly_totalDegree_le
--#print axioms ChainDescent.QPoly_totalDegree_le
--#print axioms ChainDescent.entryPoly_totalDegree_le
--#print axioms ChainDescent.pencilDetPoly_totalDegree_le
--#print axioms ChainDescent.badHgood_count_le
--#print axioms ChainDescent.beta_count_closed
--#print axioms ChainDescent.corr_zero_of_anchor
--#print axioms ChainDescent.QPoly_ne_zero
--#print axioms ChainDescent.qZero_count_le
--#print axioms ChainDescent.beta_full_count_closed
--#print axioms ChainDescent.exists_orthoAnisotropic_basis
--#print axioms ChainDescent.associated_separatingLeft_of_polarRad
