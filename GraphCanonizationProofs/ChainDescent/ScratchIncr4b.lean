/-
# Increment 4 — the bad-anchor count `β` (Schwartz–Zippel in `t₀`) (SCRATCH).

`good_anchor_fail_le_const` (`ScratchIncr4`) gives the per-good-anchor fail bound `c/|V| ≤ 15/16`. The matching
`F = c·|V| + |V|·β` then needs the **bad-anchor count** `β = #{t₀ : ¬good t₀}` to be `O(|V|/q)`.

**The structural reduction (key).** Because `pairForm Q (t₀−v)` is *always* degenerate (`pairForm_polar_anchor`:
`t₀−v` lies in its radical), a *nondegenerate* pencil member can only arise from a genuine `(y,z)`-combination —
so **`hgood` alone forces `hnz`, `hPu`, `hPv`** (a zero member, or `pairForm_u ∝ pairForm_v`, would make the whole
pencil a scalar multiple of one degenerate form). Hence the good-anchor predicate collapses (modulo the negligible
points `t₀ ∈ {u,v}`) to

    good t₀  ⟺  hgood t₀ ∧ Q(t₀−u) ≠ 0 ∧ Q(t₀−v) ≠ 0,

so `β`'s bad set is `{¬hgood} ∪ {Q(t₀−u)=0} ∪ {Q(t₀−v)=0}` (+ two points). The two quadric loci are immediate from
`zeroCountShift_card_le` (applied to `Q` itself); the meaty piece is **`{¬hgood} = {t₀ : pencilDisc(·,·;t₀) ≡ 0}`**,
bounded by Schwartz–Zippel **in `t₀`**: some coefficient of `pencilDisc` (a polynomial in `(y,z)`) is a nonzero
polynomial in `t₀`'s coordinates, of bounded total degree, so `#{¬hgood} ≤ deg·|V|/q`.

**This module lands the Schwartz–Zippel-in-`Fin d` engine** `mvPoly_zeros_count_le_dim` (the `t₀`-variable count;
`ScratchGoodAnchor.mvPoly_zeros_count_le` was the `Fin 2`/`(y,z)` form) + the coordinatized count wrapper. The
per-condition polynomial constructions (`{¬hgood}` as `eval = 0` of a nonzero `t₀`-polynomial; `hgood ⟹ hnz∧hPu∧hPv`)
are the remaining bad-anchor work, on top of this engine.

NOT in build (scratch; `lake env lean ChainDescent/ScratchIncr4b.lean`).
-/
import ChainDescent.ScratchIncr4
import ChainDescent.ScratchGoodAnchor

namespace ChainDescent

open Finset Module

/-- **Schwartz–Zippel in `Fin d` — the bad-anchor counting engine.** For a *nonzero* `d`-variable polynomial `p`, the
zero set over `K^d` satisfies `#{f : Fin d → K | eval f p = 0} · |K| ≤ p.totalDegree · |K^d|`, i.e.
`#{zeros}/|K^d| ≤ totalDegree/|K| = O(1/q)`. Generalizes `ScratchGoodAnchor.mvPoly_zeros_count_le` (the `Fin 2` case)
to arbitrary arity — the form needed to count bad anchors `t₀ ∈ V ≅ K^d`. Direct from
`MvPolynomial.schwartz_zippel_totalDegree` with `S = univ`. -/
theorem mvPoly_zeros_count_le_dim {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    {p : MvPolynomial (Fin d) K} (hp : p ≠ 0) :
    (univ.filter (fun f : Fin d → K => MvPolynomial.eval f p = 0)).card * Fintype.card K
      ≤ p.totalDegree * Fintype.card (Fin d → K) := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  set Sz : ℕ := (univ.filter (fun f : Fin d → K => MvPolynomial.eval f p = 0)).card with hSz
  set q : ℕ := Fintype.card K with hqdef
  have hqQ : (0 : ℚ≥0) < (q : ℚ≥0) := by exact_mod_cast hq
  -- `hsz : (Sz : ℚ≥0) / q^d ≤ totalDegree / q`; cross-multiply
  rw [div_le_div_iff₀ (by positivity) hqQ] at hsz
  -- `hsz : (Sz : ℚ≥0) * q ≤ totalDegree * q^d`
  have hcard : Fintype.card (Fin d → K) = q ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  exact_mod_cast hsz

section Reduction
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Every scalar multiple `c • pairForm Q a` has the anchor `a` in its polar-radical (`pairForm_polar_anchor`
transports through `polar_smul`). -/
theorem mem_polarRad_smul_pairForm (Q : QuadraticForm K V) (a : V) (c : K) :
    a ∈ polarRad (c • pairForm Q a) := by
  rw [mem_polarRad]
  intro x
  have h : QuadraticMap.polar (c • pairForm Q a) x a
      = c • QuadraticMap.polar (pairForm Q a) x a := by
    simp only [QuadraticMap.polar, QuadraticMap.smul_apply, smul_sub]
  rw [h, pairForm_polar_anchor, smul_zero]

/-- A nonzero scalar-multiple-of-`pairForm` form has nontrivial radical (the anchor `a ≠ 0`), hence is degenerate. -/
theorem polarRad_smul_pairForm_ne_bot (Q : QuadraticForm K V) {a : V} (ha : a ≠ 0) (c : K) :
    polarRad (c • pairForm Q a) ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨a, mem_polarRad_smul_pairForm Q a c, ha⟩

variable (Q : QuadraticForm K V) (u v t₀ : V)

/-- **`hgood ⟹ hPu`.** A nondeg pencil member forces `pairForm Q (t₀−u) ≠ 0`: if it were `0` the pencil would reduce
to `z • pairForm Q (t₀−v)`, degenerate (anchor `t₀−v ≠ 0`). -/
theorem hPu_of_hgood (hv : t₀ ≠ v)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    pairForm Q (t₀ - u) ≠ 0 := by
  intro hPu0
  obtain ⟨y, z, hyz⟩ := hg
  rw [hPu0, smul_zero, zero_add] at hyz
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hv) z hyz

/-- **`hgood ⟹ hPv`** (symmetric to `hPu_of_hgood`). -/
theorem hPv_of_hgood (hu : t₀ ≠ u)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    pairForm Q (t₀ - v) ≠ 0 := by
  intro hPv0
  obtain ⟨y, z, hyz⟩ := hg
  rw [hPv0, smul_zero, add_zero] at hyz
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hu) y hyz

/-- **`hgood ⟹ hnz`.** A nondeg pencil member forbids a zero member on `y,z ≠ 0`: a zero member makes
`pairForm Q (t₀−u) ∝ pairForm Q (t₀−v)`, collapsing the *whole* pencil to a scalar multiple of the (degenerate)
`pairForm Q (t₀−v)` — so no member could be nondegenerate. -/
theorem hnz_of_hgood (hv : t₀ ≠ v)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    ∀ y z : K, y ≠ 0 → z ≠ 0 → y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0 := by
  intro y₁ z₁ hy1 _ hyz1
  have h1 : y₁ • pairForm Q (t₀ - u) = -(z₁ • pairForm Q (t₀ - v)) :=
    eq_neg_of_add_eq_zero_left hyz1
  have hPueq : pairForm Q (t₀ - u) = (y₁⁻¹ * (-z₁)) • pairForm Q (t₀ - v) := by
    rw [mul_smul, neg_smul, ← h1, smul_smul, inv_mul_cancel₀ hy1, one_smul]
  obtain ⟨y₀, z₀, hyz0⟩ := hg
  rw [hPueq, smul_smul, ← add_smul] at hyz0
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hv) _ hyz0

open scoped Classical in
/-- **The bad-anchor reduction (input `β`).** The full good-anchor predicate `hnz ∧ hgood ∧ hPu ∧ hPv` (what
`good_anchor_fail_le_const` consumes) fails on at most `#{t₀ : ¬hgood} + 2` anchors — i.e. `β ≤ #{¬hgood} + 2`. By the
three implications, the only way to fail `hnz`/`hPu`/`hPv` while `hgood` holds is `t₀ ∈ {u,v}` (two points). So the
bad-anchor count is governed by the single locus `{¬hgood} = {t₀ : pencilDisc(·;t₀) ≡ 0}`, the remaining
Schwartz–Zippel-in-`t₀` target (via `mvPoly_zeros_count_le_dim`). -/
theorem bad_anchor_card_le_hgood [Fintype V] [DecidableEq V] (Q : QuadraticForm K V) (u v : V) :
    (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
      ≤ (univ.filter (fun t₀ : V =>
          ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2 := by
  classical
  have hsub : (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0)))
      ⊆ (univ.filter (fun t₀ : V =>
          ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)) ∪ {u, v} := by
    intro t₀ ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases hgt : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥
    · refine Or.inr ?_
      by_contra hne
      rw [not_or] at hne
      exact ht ⟨hnz_of_hgood Q u v t₀ hne.2 hgt, hgt,
        hPu_of_hgood Q u v t₀ hne.2 hgt, hPv_of_hgood Q u v t₀ hne.1 hgt⟩
    · exact Or.inl hgt
  calc (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
      ≤ ((univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥))
          ∪ ({u, v} : Finset V)).card := Finset.card_le_card hsub
    _ ≤ (univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card
          + ({u, v} : Finset V).card := Finset.card_union_le _ _
    _ ≤ (univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2 :=
        Nat.add_le_add_left ((Finset.card_insert_le _ _).trans (by simp)) _

end Reduction

section SchwartzZippelCount
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

/-- **Bad-anchor count via a representing polynomial — the rigorous Schwartz–Zippel reduction.** If a bad-anchor
predicate `badpred` is contained in the zero set of a *nonzero* polynomial `P` read off the anchor's coordinates
(`hrep : badpred t₀ → eval (b.equivFun t₀) P = 0`), then `#{t₀ : badpred} · |K| ≤ P.totalDegree · |V|`, i.e.
density `≤ totalDegree/q`. Coordinatize `V ≅ K^d` via `b.equivFun`, then `mvPoly_zeros_count_le_dim`. For `β` this is
applied with `badpred = ¬hgood` and `P` = the pencil determinant at a fixed nondeg witness `(y₀,z₀)` (which a good
anchor makes `≠ 0`); `hrep` then holds because `¬hgood ⟹` every pencil member is degenerate
(`polarRad_ne_bot_iff_det_eq_zero`). -/
theorem bad_anchor_count_le_of_poly {d : ℕ} (b : Basis (Fin d) K V)
    (badpred : V → Prop) [DecidablePred badpred]
    (P : MvPolynomial (Fin d) K) (hP : P ≠ 0)
    (hrep : ∀ t₀, badpred t₀ → MvPolynomial.eval (b.equivFun t₀) P = 0) :
    (univ.filter badpred).card * Fintype.card K ≤ P.totalDegree * Fintype.card V := by
  classical
  have hsub : univ.filter badpred
      ⊆ univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0) := by
    intro t₀ ht
    rw [mem_filter] at ht ⊢
    exact ⟨ht.1, hrep t₀ ht.2⟩
  have hreindex : (univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0)).card
      = (univ.filter (fun f : Fin d → K => MvPolynomial.eval f P = 0)).card := by
    apply Finset.card_nbij' (fun t₀ => b.equivFun t₀) (fun f => b.equivFun.symm f)
    · intro t₀ ht
      rw [Finset.mem_coe, mem_filter] at ht ⊢
      exact ⟨mem_univ _, ht.2⟩
    · intro f hf
      rw [Finset.mem_coe, mem_filter] at hf ⊢
      exact ⟨mem_univ _, by rw [LinearEquiv.apply_symm_apply]; exact hf.2⟩
    · intro t₀ _; simp only [LinearEquiv.symm_apply_apply]
    · intro f _; simp only [LinearEquiv.apply_symm_apply]
  calc (univ.filter badpred).card * Fintype.card K
      ≤ (univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0)).card * Fintype.card K :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ = (univ.filter (fun f : Fin d → K => MvPolynomial.eval f P = 0)).card * Fintype.card K := by
        rw [hreindex]
    _ ≤ P.totalDegree * Fintype.card (Fin d → K) := mvPoly_zeros_count_le_dim hP
    _ = P.totalDegree * Fintype.card V := by
        rw [← Fintype.card_congr b.equivFun.toEquiv]

omit [Fintype K] [DecidableEq K] [Fintype V] in
/-- **`hrep` for `¬hgood`, from a representing polynomial.** If `P` represents the pencil-determinant at a fixed witness
`(y₀,z₀)` — `eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u + z₀•pairForm_v)))` — then on every
`¬hgood` anchor `eval (coords t₀) P = 0` (the witness member is degenerate there, `polarRad_ne_bot_iff_det_eq_zero`).
This discharges `bad_anchor_count_le_of_poly`'s `hrep`, so the ONLY remaining obligation to close `β` is **constructing
such a `P` (with `P ≠ 0`)** — i.e. coordinatizing the pencil determinant + nonzero by a good-anchor witness. -/
theorem notHgood_eval_zero_of_repr {d : ℕ} (b : Basis (Fin d) K V) (Q : QuadraticForm K V)
    (y₀ z₀ : K) (u v : V) (P : MvPolynomial (Fin d) K)
    (hrepP : ∀ t₀, MvPolynomial.eval (b.equivFun t₀) P
      = (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin
          (y₀ • pairForm Q (t₀ - u) + z₀ • pairForm Q (t₀ - v)))).det) :
    ∀ t₀, (¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) →
      MvPolynomial.eval (b.equivFun t₀) P = 0 := by
  intro t₀ hbad
  rw [hrepP t₀]
  apply (polarRad_ne_bot_iff_det_eq_zero b _).mp
  intro hbot
  exact hbad ⟨y₀, z₀, hbot⟩

end SchwartzZippelCount

end ChainDescent

#print axioms ChainDescent.mvPoly_zeros_count_le_dim
#print axioms ChainDescent.hPu_of_hgood
#print axioms ChainDescent.hPv_of_hgood
#print axioms ChainDescent.hnz_of_hgood
#print axioms ChainDescent.bad_anchor_card_le_hgood
#print axioms ChainDescent.bad_anchor_count_le_of_poly
#print axioms ChainDescent.notHgood_eval_zero_of_repr
