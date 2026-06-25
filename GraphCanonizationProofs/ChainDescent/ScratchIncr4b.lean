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

end ChainDescent

#print axioms ChainDescent.mvPoly_zeros_count_le_dim
