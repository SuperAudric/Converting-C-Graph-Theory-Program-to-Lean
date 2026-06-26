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
import ChainDescent.ScratchIncr4b

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

/- **β CLOSED (modulo non-vacuity).** Composing `badHgood_count_le` (`#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`,
this module) with the landed `ScratchIncr4b.bad_anchor_card_le_hgood` (`β ≤ #{¬hgood} + 2`) bounds the full bad-anchor
count `β·|K| ≤ (pencilDetPoly).totalDegree·|V| + 2·|K|` — density `β/|V| ≤ totalDegree/q + O(1/|V|) = O(d/q)`. The only
premise is the **non-vacuity** `hgood` (∃ good anchor for `u≠v`, the "distinct radicals" condition). This final Nat-
arithmetic composition is deferred to the increment-5 assembly, where the matching's `fail`/good-anchor `DecidablePred`
instances are fixed in one place (combining the two lemmas here hits a cross-module `Classical.propDecidable` mismatch
on the `{¬hgood}` filter — cosmetic, not mathematical). -/

end ChainDescent

#print axioms ChainDescent.coordPoly_eval
#print axioms ChainDescent.linFunc_eq_sum
#print axioms ChainDescent.coordPoly_eval_linFunc
#print axioms ChainDescent.polar_t0_t0_sum
#print axioms ChainDescent.gramQuadPoly_eval
#print axioms ChainDescent.LPoly_eval
#print axioms ChainDescent.QPoly_eval
#print axioms ChainDescent.polar_pairForm_apply
#print axioms ChainDescent.entryPoly_eval
#print axioms ChainDescent.pencilDetPoly_eval
#print axioms ChainDescent.pencilDetPoly_ne_zero
#print axioms ChainDescent.badHgood_count_le
