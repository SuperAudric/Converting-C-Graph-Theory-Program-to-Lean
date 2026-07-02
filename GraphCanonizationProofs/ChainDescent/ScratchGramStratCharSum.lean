/-
# Route A, Step C — Piece 1b: the character-sum identity for `gramStratCount`

**What this module builds (recovery doc §9.7 "LEAN BUILD STARTED", Piece 1b).** The round-3 observable
`gramStratCount Q a b u g = #{z : gramK z = g ∧ Q(u−z)=0}` (Piece 1a, `ScratchGramStratCount`) is expressed as a finite
**character sum**, the analytic form the K-non-degeneracy crux (`GramCountsRecoverOrbit`) is proved from. This is a pure
*assembly* of the field-generic `GaussCount` toolkit — no new Gauss theory:

* **`gramStratCount_charsum`** — the raw four-constraint expansion via `countk_eq_sum_charsum` (Brick Aₖ). The four
  simultaneous constraints `Q z = g₀`, `polar z a = g₁`, `polar z b = g₂`, `Q(u−z) = 0` Fourier-expand to
  `gramStratCount · |K|⁴ = ∑_{r:Fin 4→K} ψ(−(r₀g₀+r₁g₁+r₂g₂)) · ∑_z ψ(r₀·Qz + r₁·polar z a + r₂·polar z b + r₃·Q(u−z))`.
* **`gramStrat_inner_normalize`** — the inner z-sum exponent, put in the `Q`-plus-linear normal form
  `(r₀+r₃)·Qz + polar Q z (r₁•a + r₂•b − r₃•u) + r₃·Qu` (via `quad_sub` + polar bilinearity). This is exactly the shape
  `sum_addChar_quadForm_linear` (Brick D1, `r₀+r₃ ≠ 0`) / `sum_addChar_multiQuad_zero` (`r₀+r₃ = 0`) evaluate, isolating
  `u` into a phase — the entry point for Piece 1c (the Fourier non-degeneracy, `u`'s dual Gram → orbit).
* **`gramStratCount_charsum_normalized`** — the two combined: `gramStratCount · |K|⁴` as a sum whose inner z-sum is in
  the D1-ready normal form.

Reuses `ScratchGramStratCount` (`gramStratCount`/`gramK`) and `GaussCount` (`countk_eq_sum_charsum`, `quad_sub`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratCount
import ChainDescent.GaussCount

namespace ChainDescent.GramStrat

open QuadraticMap Finset ChainDescent

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **Piece 1b, the raw expansion.** `gramStratCount Q a b u g`, scaled by `|K|⁴`, equals the four-fold Fourier sum of
the count's four defining constraints (`Q z = g₀`, `polar z a = g₁`, `polar z b = g₂`, `Q(u−z) = 0`). Direct instance of
`countk_eq_sum_charsum` (Brick Aₖ) with the constraint family `f = (Q·, polar·a, polar·b, Q(u−·))`. -/
theorem gramStratCount_charsum (Q : QuadraticForm K V) (a b u : V) (g : K × K × K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    (gramStratCount Q a b u g : R') * (Fintype.card K : R') ^ 4
      = ∑ r : Fin 4 → K, ψ (-(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2))
          * ∑ z : V, ψ (r 0 * Q z + r 1 * QuadraticMap.polar Q z a
              + r 2 * QuadraticMap.polar Q z b + r 3 * Q (u - z)) := by
  -- the constraint family and target values (`set`, not `let`, to keep `f`/`c` opaque fvars — so the
  -- `DecidablePred` instance in `hk` and in the restatements below is literally the same term)
  set f : Fin 4 → V → K :=
    ![fun z => Q z, fun z => QuadraticMap.polar Q z a, fun z => QuadraticMap.polar Q z b,
      fun z => Q (u - z)] with hf
  set c : Fin 4 → K := ![g.1, g.2.1, g.2.2, 0] with hc
  have hk := countk_eq_sum_charsum (F := K) (R' := R') hψ f c
  rw [Fintype.card_fin] at hk
  -- the RHS of `hk` matches the target RHS (unfold the two explicit `Fin 4` sums)
  have hrhs : (∑ r : Fin 4 → K, ψ (-(∑ j, r j * c j)) * ∑ x : V, ψ (∑ j, r j * f j x))
      = ∑ r : Fin 4 → K, ψ (-(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2))
          * ∑ z : V, ψ (r 0 * Q z + r 1 * QuadraticMap.polar Q z a
              + r 2 * QuadraticMap.polar Q z b + r 3 * Q (u - z)) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    · congr 1
      rw [Fin.sum_univ_four]
      simp only [hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
        mul_zero, add_zero]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      congr 1
      rw [Fin.sum_univ_four]
      simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val]
  -- assemble: the goal's RHS is `hk`'s RHS (via `hrhs`); the only difference from `hk` is the count
  -- (`gramStratCount` vs the countk filter card), which `convert` turns into the `hcard_eq` subgoal —
  -- absorbing the `DecidablePred`-instance mismatch that blocks a plain `rw`/`exact`.
  rw [← hrhs]
  convert hk using 3
  -- subgoal: `gramStratCount Q a b u g = (countk filter).card`; proved by `ext` (instance-agnostic,
  -- so it matches whichever `DecidablePred` instance `convert` produced from `hk`)
  rw [gramStratCount]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hg, h3⟩ j
    rw [gramK, Prod.ext_iff, Prod.ext_iff] at hg
    fin_cases j <;>
      simp only [hf, hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val]
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2
    · exact h3
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [hf, hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val] at h0 h1 h2 h3
    refine ⟨?_, h3⟩
    rw [gramK, Prod.ext_iff, Prod.ext_iff]
    exact ⟨h0, h1, h2⟩

/-- **Piece 1b, the inner-sum normal form.** The inner z-exponent
`r₀·Qz + r₁·polar z a + r₂·polar z b + r₃·Q(u−z)` equals `(r₀+r₃)·Qz + polar Q z (r₁•a + r₂•b − r₃•u) + r₃·Qu`. This is
the `Q`-plus-linear shape `sum_addChar_quadForm_linear` (D1, `r₀+r₃≠0`) / `sum_addChar_multiQuad_zero` (`=0`) evaluate —
after which `u` sits inside the quadratic `Q(r₁•a+r₂•b−r₃•u)` and the `r₃·Qu` phase (Piece 1c's entry point). -/
theorem gramStrat_inner_normalize (Q : QuadraticForm K V) (a b u z : V) (r : Fin 4 → K) :
    r 0 * Q z + r 1 * QuadraticMap.polar Q z a + r 2 * QuadraticMap.polar Q z b + r 3 * Q (u - z)
      = (r 0 + r 3) * Q z + QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u) + r 3 * Q u := by
  have hpolar : QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u)
      = r 1 * QuadraticMap.polar Q z a + r 2 * QuadraticMap.polar Q z b - r 3 * QuadraticMap.polar Q z u := by
    rw [sub_eq_add_neg, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hpolar, quad_sub Q u z, QuadraticMap.polar_comm Q u z]
  ring

/-- **Piece 1b, combined.** `gramStratCount · |K|⁴` as a Fourier sum whose inner z-sum is in the D1-ready normal form.
The endpoint of Piece 1b: `sum_addChar_quadForm_linear`/`sum_addChar_multiQuad_zero` now apply to each inner sum, and the
Fourier inversion of the resulting profile (over `g`) is Piece 1c. -/
theorem gramStratCount_charsum_normalized (Q : QuadraticForm K V) (a b u : V) (g : K × K × K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    (gramStratCount Q a b u g : R') * (Fintype.card K : R') ^ 4
      = ∑ r : Fin 4 → K, ψ (-(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2))
          * ∑ z : V, ψ ((r 0 + r 3) * Q z
              + QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u) + r 3 * Q u) := by
  rw [gramStratCount_charsum Q a b u g hψ]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [gramStrat_inner_normalize Q a b u z r]

end ChainDescent.GramStrat
