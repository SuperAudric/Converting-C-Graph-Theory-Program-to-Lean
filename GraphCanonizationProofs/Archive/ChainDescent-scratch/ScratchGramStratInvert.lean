/-
# Route A, Step C — Piece 1c(ii): the `g`-profile Fourier inversion of `gramStratCount`

**What this module builds (recovery doc §9.7, Piece 1c(ii)).** The character-sum identity (Piece 1b) writes
`gramStratCount u g · |K|⁴ = ∑_r ψ(−(r₀g₀+r₁g₁+r₂g₂)) · InnerZ_u(r)`, where the count depends on `g` only through the
phase `ψ(−⟨(r₀,r₁,r₂),g⟩)`. Fourier-inverting over `g ∈ K³` (orthogonality) collapses the `(r₀,r₁,r₂)`-sum, extracting the
`r₃`-marginal of `InnerZ_u`. The payoff: **`SameGramStratCounts u u'` ⟹ `∀ s, ∑_t InnerZ_u(s,t) = ∑_t InnerZ_{u'}(s,t)`**
(the count *functions* are equal, so their `g`-transforms are equal — trivially — and this identity evaluates the
transform). That marginal is where `u`'s Gram data + the `u_⊥` distinction live (Piece 1c(iii)).

This module is **complete** (all three declarations landed, axiom-clean):

* **`gsum_orthogonality`** — the `K³` character orthogonality `∑_{g:K×K×K} ψ(⟨t,g⟩) = |K|³·𝟙[t=0]`, via
  `AddChar.sum_mulShift` on each coordinate (the heart of the inversion). Collapses the `(r₀,r₁,r₂)`-sum against the
  `g`-profile. NB coordinate factoring uses explicit `have`s, since `← Finset.mul_sum` does not fire inside `simp_rw`
  (higher-order match).
* **`innerZ`** — the surviving inner z-sum, kept an opaque `def` so `Finset.mul_sum` cannot distribute into it during the
  transform (a build steer).
* **`gramStrat_transform_eval`** — the evaluated `g`-transform: `(∑_g ψ(⟨s,g⟩)·gramStratCount u g)·|K|⁴ =
  ∑_r 𝟙[r₀₁₂=s]·|K|³·innerZ_u(r)`. From `gramStratCount_charsum_normalized` + `gsum_orthogonality` + `Finset.sum_comm`.
* **`sameGramStratCounts_transform`** — `SameGramStratCounts u u'` ⟹ equal `innerZ` fibre sums ∀`s` (trivial once the
  transform is evaluated: equal count functions ⟹ equal transforms). This is the input to **Piece 1c(iii)**
  (`ScratchGramStratOrbit`: bulk non-degeneracy → primal Gram, boundary → the `u∈span{a,b}` flag, then the carried
  refined-Witt) that discharges the open predicate `GramCountsRecoverGram`.

Reuses `GaussCount` (`AddChar.sum_mulShift`) and `ScratchGramStratCharSum` (`gramStratCount_charsum_normalized`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratCharSum

namespace ChainDescent.GramStrat

open QuadraticMap Finset ChainDescent

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **`K³` character orthogonality.** `∑_{g:K×K×K} ψ(t₀g₀+t₁g₁+t₂g₂) = |K|³` if `t = 0`, else `0`. Coordinatewise via
`AddChar.sum_mulShift`. -/
theorem gsum_orthogonality {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) (t : K × K × K) :
    (∑ g : K × K × K, ψ (t.1 * g.1 + t.2.1 * g.2.1 + t.2.2 * g.2.2))
      = if t = 0 then (Fintype.card K : R') ^ 3 else 0 := by
  -- coordinatewise geometric sum
  have hcoord : ∀ b : K, (∑ x : K, ψ (b * x)) = if b = 0 then (Fintype.card K : R') else 0 := by
    intro b
    simp_rw [mul_comm b]
    rw [AddChar.sum_mulShift b hψ]
    split_ifs <;> simp
  -- expand the triple sum into an iterated sum with the character factored coordinatewise
  have hexpand : (∑ g : K × K × K, ψ (t.1 * g.1 + t.2.1 * g.2.1 + t.2.2 * g.2.2))
      = ∑ g0 : K, ∑ g1 : K, ∑ g2 : K, ψ (t.1 * g0) * ψ (t.2.1 * g1) * ψ (t.2.2 * g2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun g0 _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun g1 _ => Finset.sum_congr rfl (fun g2 _ => ?_))
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  -- collapse each coordinate sum in turn (constants are concrete, so `rw [← mul_sum]` matches)
  have collapse : ∀ g0 g1 : K,
      (∑ g2 : K, ψ (t.1 * g0) * ψ (t.2.1 * g1) * ψ (t.2.2 * g2))
        = ψ (t.1 * g0) * ψ (t.2.1 * g1) * (if t.2.2 = 0 then (Fintype.card K : R') else 0) := by
    intro g0 g1; rw [← Finset.mul_sum, hcoord]
  have collapse2 : ∀ g0 : K,
      (∑ g1 : K, ψ (t.1 * g0) * ψ (t.2.1 * g1) * (if t.2.2 = 0 then (Fintype.card K : R') else 0))
        = ψ (t.1 * g0) * (if t.2.1 = 0 then (Fintype.card K : R') else 0)
            * (if t.2.2 = 0 then (Fintype.card K : R') else 0) := by
    intro g0; rw [← Finset.sum_mul, ← Finset.mul_sum, hcoord]
  have collapse3 :
      (∑ g0 : K, ψ (t.1 * g0) * (if t.2.1 = 0 then (Fintype.card K : R') else 0)
          * (if t.2.2 = 0 then (Fintype.card K : R') else 0))
        = (if t.1 = 0 then (Fintype.card K : R') else 0)
            * (if t.2.1 = 0 then (Fintype.card K : R') else 0)
            * (if t.2.2 = 0 then (Fintype.card K : R') else 0) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hcoord]
  rw [hexpand]
  simp_rw [collapse, collapse2]
  rw [collapse3]
  -- LHS is now the product of the three coordinate `if`s; match against `if t = 0`
  rcases eq_or_ne t.1 0 with h0 | h0
  · rcases eq_or_ne t.2.1 0 with h1 | h1
    · rcases eq_or_ne t.2.2 0 with h2 | h2
      · rw [if_pos h0, if_pos h1, if_pos h2,
          if_pos (Prod.ext_iff.mpr ⟨h0, Prod.ext_iff.mpr ⟨h1, h2⟩⟩)]; ring
      · rw [if_neg h2, if_neg (show t ≠ 0 by rintro rfl; exact h2 rfl)]; ring
    · rw [if_neg h1, if_neg (show t ≠ 0 by rintro rfl; exact h1 rfl)]; ring
  · rw [if_neg h0, if_neg (show t ≠ 0 by rintro rfl; exact h0 rfl)]; ring

/-- The surviving **inner z-sum** (`InnerZ`) of the round-3 character sum, at dual variable `r`. Kept as a `def` so the
`g`-orthogonality manipulation (and `Finset.mul_sum`) treat it opaquely. Definitionally the 1c(i) inner sum. -/
noncomputable def innerZ (Q : QuadraticForm K V) (a b u : V) {R' : Type*} [CommRing R']
    (ψ : AddChar K R') (r : Fin 4 → K) : R' :=
  ∑ z : V, ψ ((r 0 + r 3) * Q z
    + QuadraticMap.polar Q z (r 1 • a + r 2 • b - r 3 • u) + r 3 * Q u)

/-- **Piece 1c(ii), the evaluated `g`-transform.** Multiplying `gramStratCount u g · |K|⁴` (in its `charsum_normalized`
form) by `ψ(⟨s,g⟩)` and summing over `g ∈ K³`, the `g`-orthogonality collapses the `(r₀,r₁,r₂)`-sum onto the fibre
`r₀₁₂ = s`: only the inner `r₃`-sum survives, weighted by `|K|³`. `u` now lives entirely in the surviving `innerZ`.
This turns the (trivial) equality of two count profiles into an equality of `innerZ` fibre sums
(`sameGramStratCounts_transform`), the input to the 1c(iii) non-degeneracy. -/
theorem gramStrat_transform_eval (Q : QuadraticForm K V) (a b u : V) (s : K × K × K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    (∑ g : K × K × K, ψ (s.1 * g.1 + s.2.1 * g.2.1 + s.2.2 * g.2.2)
        * (gramStratCount Q a b u g : R')) * (Fintype.card K : R') ^ 4
      = ∑ r : Fin 4 → K,
          (if (s.1 - r 0, s.2.1 - r 1, s.2.2 - r 2) = (0 : K × K × K)
            then (Fintype.card K : R') ^ 3 else 0) * innerZ Q a b u ψ r := by
  have hcs : ∀ g : K × K × K, (gramStratCount Q a b u g : R') * (Fintype.card K : R') ^ 4
      = ∑ r : Fin 4 → K, ψ (-(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2)) * innerZ Q a b u ψ r :=
    fun g => gramStratCount_charsum_normalized Q a b u g hψ
  rw [Finset.sum_mul]
  simp_rw [mul_assoc, hcs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hcomb : ∀ g : K × K × K,
      ψ (s.1 * g.1 + s.2.1 * g.2.1 + s.2.2 * g.2.2)
          * (ψ (-(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2)) * innerZ Q a b u ψ r)
        = ψ ((s.1 - r 0) * g.1 + (s.2.1 - r 1) * g.2.1 + (s.2.2 - r 2) * g.2.2)
            * innerZ Q a b u ψ r := by
    intro g
    rw [← mul_assoc, ← AddChar.map_add_eq_mul,
      show s.1 * g.1 + s.2.1 * g.2.1 + s.2.2 * g.2.2 + -(r 0 * g.1 + r 1 * g.2.1 + r 2 * g.2.2)
        = (s.1 - r 0) * g.1 + (s.2.1 - r 1) * g.2.1 + (s.2.2 - r 2) * g.2.2 from by ring]
  simp_rw [hcomb]
  rw [← Finset.sum_mul, gsum_orthogonality hψ (s.1 - r 0, s.2.1 - r 1, s.2.2 - r 2)]

/-- **Piece 1c(ii), the payoff.** Equal round-3 count profiles ⟹ equal `g`-transforms (trivially, being sums of equal
terms), hence — by `gramStrat_transform_eval` — equal `innerZ` fibre sums for every `s`. This converts the
count-equality into the Gauss-sum equality that 1c(iii) inverts to `u`'s Gram data. -/
theorem sameGramStratCounts_transform (Q : QuadraticForm K V) (a b : V) {u u' : V}
    (h : SameGramStratCounts Q a b u u') (s : K × K × K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    (∑ r : Fin 4 → K,
        (if (s.1 - r 0, s.2.1 - r 1, s.2.2 - r 2) = (0 : K × K × K)
          then (Fintype.card K : R') ^ 3 else 0) * innerZ Q a b u ψ r)
      = ∑ r : Fin 4 → K,
          (if (s.1 - r 0, s.2.1 - r 1, s.2.2 - r 2) = (0 : K × K × K)
            then (Fintype.card K : R') ^ 3 else 0) * innerZ Q a b u' ψ r := by
  rw [← gramStrat_transform_eval Q a b u s hψ, ← gramStrat_transform_eval Q a b u' s hψ]
  congr 1
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [h g]

end ChainDescent.GramStrat
