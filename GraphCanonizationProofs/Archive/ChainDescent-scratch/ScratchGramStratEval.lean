/-
# Route A, Step C — Piece 1c(i): evaluate the inner z-sum of the `gramStratCount` character sum

**What this module builds (recovery doc §9.7, Piece 1c).** Piece 1b (`ScratchGramStratCharSum`) put the round-3 count in
the Fourier form `gramStratCount u g · |K|⁴ = ∑_r ψ(−⟨r,g⟩) · ∑_z ψ((r₀+r₃)·Qz + polar z wᵣ + r₃·Qu)`, with the inner
z-sum in the `Q`-plus-linear normal form (`wᵣ = r₁•a + r₂•b − r₃•u`). This module **evaluates that inner z-sum** — the
first concrete step of the Fourier non-degeneracy (`GramCountsRecoverOrbit`). The `GaussCount` bricks apply verbatim:

* **`gramStrat_inner_eval_ne`** — the bulk (`ρ := r₀+r₃ ≠ 0`): complete the square (`sum_addChar_quadForm_linear`, D1),
  `∑_z ψ(ρ·Qz + polar z wᵣ + r₃·Qu) = ψ(r₃·Qu) · ψ(−ρ⁻¹·Q wᵣ) · ∑_z ψ(ρ·Qz)`. Here `u` enters through the phase
  `ψ(r₃·Qu)` **and** through `Q wᵣ = Q(r₁•a+r₂•b−r₃•u)` — the seed of `u`'s dual Gram that the `g`-profile inversion
  (next step) extracts.
* **`gramStrat_inner_eval_zero`** — the boundary (`ρ = 0`): the quadratic part drops, leaving the linear character sum
  `∑_z ψ(polar z wᵣ)`, evaluated by `sum_addChar_linearMap` to `|V|` if `polar Q · wᵣ = 0` (radical / `wᵣ = 0` when `Q`
  nondegenerate) and `0` otherwise.

These two are the entry point for the profile inversion (Piece 1c(ii)) and the count→Gauss-sum dual
(`multiCharSum_eq_sum_count`) that together give `GramCountsRecoverOrbit` (modulo the Witt-on-`W^⊥` geometry).

Reuses `GaussCount` (`sum_addChar_quadForm_linear`, `sum_addChar_linearMap`) and `ScratchGramStratCharSum`.
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratCharSum

namespace ChainDescent.GramStrat

open QuadraticMap Finset ChainDescent

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **Piece 1c(i), the bulk (`ρ = r₀+r₃ ≠ 0`).** Complete the square in the inner z-sum: `u` factors out into the phase
`ψ(r₃·Qu)` and enters the completed-square constant through `Q(r₁•a+r₂•b−r₃•u)`. Direct application of `GaussCount`'s
Brick D1 (`sum_addChar_quadForm_linear`). -/
theorem gramStrat_inner_eval_ne (Q : QuadraticForm K V) (a b u : V) (r : Fin 4 → K)
    (hρ : r 0 + r 3 ≠ 0) {R' : Type*} [CommRing R'] (ψ : AddChar K R') :
    (∑ z : V, ψ ((r 0 + r 3) * Q z
        + QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u) + r 3 * Q u))
      = ψ (r 3 * Q u)
        * (ψ (-((r 0 + r 3)⁻¹ * Q (r 1 • a + r 2 • b - r 3 • u)))
            * ∑ z : V, ψ ((r 0 + r 3) * Q z)) := by
  -- pull the constant `ψ(r₃·Qu)` out of the sum
  rw [Finset.sum_congr rfl (fun z _ => by
    rw [AddChar.map_add_eq_mul])]
  rw [← Finset.sum_mul]
  -- complete the square on the remaining `∑_z ψ(ρ·Qz + polar z wᵣ)` (D1); normalize `↑(Units.mk0 …)` first
  have hD1 := sum_addChar_quadForm_linear ψ Q (Units.mk0 (r 0 + r 3) hρ) (r 1 • a + r 2 • b - r 3 • u)
  rw [Units.val_mk0] at hD1
  rw [hD1]
  ring

open scoped Classical in
/-- **Piece 1c(i), the boundary (`ρ = r₀+r₃ = 0`).** The quadratic part drops; the inner sum is the linear character sum
`ψ(r₃·Qu) · ∑_z ψ(polar z wᵣ)`, and `sum_addChar_linearMap` evaluates it: `|V|` if the functional `polar Q · wᵣ` is zero
(i.e. `wᵣ` in the radical — `wᵣ = 0` when `Q` is nondegenerate), else `0`. -/
theorem gramStrat_inner_eval_zero (Q : QuadraticForm K V) (a b u : V) (r : Fin 4 → K)
    (hρ : r 0 + r 3 = 0) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) :
    (∑ z : V, ψ ((r 0 + r 3) * Q z
        + QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u) + r 3 * Q u))
      = ψ (r 3 * Q u)
        * (if (QuadraticMap.polarBilin Q).flip (r 1 • a + r 2 • b - r 3 • u) = 0
            then (Fintype.card V : R') else 0) := by
  -- `ρ = 0`, so the `ρ·Qz` term vanishes; pull out `ψ(r₃·Qu)`
  rw [Finset.sum_congr rfl (fun z _ => by
    rw [hρ, zero_mul, zero_add, AddChar.map_add_eq_mul])]
  rw [← Finset.sum_mul]
  -- identify `∑_z ψ(polar z wᵣ)` as the linear character sum `∑_z ψ(φ z)`, `φ = polarBilin.flip wᵣ`
  have hlin : (∑ z : V, ψ (QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u)))
      = ∑ z : V, ψ ((QuadraticMap.polarBilin Q).flip (r 1 • a + r 2 • b - r 3 • u) z) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
  rw [hlin, sum_addChar_linearMap hψ]
  rw [mul_comm]

end ChainDescent.GramStrat
