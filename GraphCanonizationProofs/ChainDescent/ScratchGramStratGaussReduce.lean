/-
# Route A, Step C — Piece 1c: the reduction of `GramCountsRecoverGram` to the cone non-degeneracy

**What this module builds (recovery doc §9.7).** Using the factorization core (`ScratchGramStratGauss`), this reduces
the open Gauss predicate `GramCountsRecoverGram` (`ScratchGramStratOrbit`) to a **single classical statement about the
isotropic-cone character sum** `isoConeSum`, and **discharges the primitive-character hypothesis `hψ`** internally
(Mathlib `FiniteField.primitiveChar`). After this, the entire round-3 crux `bᵢ = 1` compiles modulo:

  * `IsoConeSumSeparatesGram` — the isolated **classical Gauss non-degeneracy** (below), and
  * `RefinedWittExtends` — the carried Witt-on-`W^⊥` input (`ScratchGramStratOrbit`).

* **`gramK_eq_iff_sameExactGram`** — `gramK u = gramK u' ↔ SameExactGram Q {a,b} u u'` (the observable's Gram triple *is*
  the exact-Gram data to the base).
* **`IsoConeSumSeparatesGram`** — the isolated crux: for any primitive `ψ`, equal factored transforms
  `ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)` (∀`t`) force `gramK u = gramK u'` and the plane flag. Stated purely via the
  classical `isoConeSum`; **no `gramStratCount` combinatorics**. This is the honest single open Gauss statement, probe-true
  at a `GoodBase` (recovery §9.7); its closed form (complete the square) is `|K|⁻¹(|V|·𝟙[y=0] + ∑_{s≠0} ψ(−s⁻¹Qy)G(s))`.
* **`gramCountsRecoverGram_of_isoConeSep`** — the reduction: `IsoConeSumSeparatesGram ⟹ GramCountsRecoverGram`, with the
  primitive additive character **constructed** (into a cyclotomic field of characteristic `0 ≠ ringChar K`), so `hψ` is
  discharged, not carried.
* **`gramCountsEq_iff_stabOrbit_of_isoConeSep`** — capstone: `bᵢ = 1` for the round-3 observable modulo exactly
  `IsoConeSumSeparatesGram` (Gauss) + `RefinedWittExtends` (Witt).

Reuses `ScratchGramStratGauss` (`countHat_factor`, `isoConeSum`), `ScratchGramStratOrbit`
(`GramCountsRecoverGram`/`GoodBase`/`RefinedWittExtends`/`gramCountsEq_iff_stabOrbit_refined`),
`ScratchGramStratCount` (`gramK`), `ScratchWallKernel` (`SameExactGram`), and Mathlib `FiniteField.primitiveChar`.
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratGauss
import ChainDescent.ScratchGramStratOrbit
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace ChainDescent.GramStrat

open QuadraticMap ChainDescent.Wall ChainDescent.OrbitBaseCase

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **The observable's Gram triple is the exact-Gram data to `{a,b}`.** `gramK u = gramK u'` iff `Q u = Q u'`,
`polar u a = polar u' a`, `polar u b = polar u' b` — i.e. `SameExactGram Q {a,b} u u'`. -/
theorem gramK_eq_iff_sameExactGram {a b u u' : V} :
    gramK Q a b u = gramK Q a b u' ↔ SameExactGram Q ({a, b} : Set V) u u' := by
  constructor
  · intro h
    simp only [gramK, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, fun s hs => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact h2
    · exact h3
  · rintro ⟨h1, h2⟩
    have ha : QuadraticMap.polar Q u a = QuadraticMap.polar Q u' a := h2 a (Set.mem_insert _ _)
    have hb : QuadraticMap.polar Q u b = QuadraticMap.polar Q u' b :=
      h2 b (Set.mem_insert_of_mem _ rfl)
    simp only [gramK, Prod.mk.injEq]
    exact ⟨h1, ha, hb⟩

/-- **★ The isolated remaining crux — a classical isotropic-cone non-degeneracy.** At a `GoodBase`, for any primitive
additive character `ψ`, equality of the factored transforms `ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)` for all `t`
forces the exact Gram (`gramK u = gramK u'`) and the plane flag. Stated purely via the classical `isoConeSum` — no
`gramStratCount`. **The honest single open Gauss statement** (`GramCountsRecoverGram`'s content); probe-true. -/
def IsoConeSumSeparatesGram (Q : QuadraticForm K V) (a b : V) : Prop :=
  GoodBase Q a b → ∀ {R' : Type} [Field R'] (ψ : AddChar K R'), ψ.IsPrimitive → ∀ u u' : V,
    (∀ t : K × K × K,
      ψ (t.1 * Q u + t.2.1 * QuadraticMap.polar Q u a + t.2.2 * QuadraticMap.polar Q u b)
          * isoConeSum Q ψ (t.1 • u + t.2.1 • a + t.2.2 • b)
        = ψ (t.1 * Q u' + t.2.1 * QuadraticMap.polar Q u' a + t.2.2 * QuadraticMap.polar Q u' b)
          * isoConeSum Q ψ (t.1 • u' + t.2.1 • a + t.2.2 • b)) →
    gramK Q a b u = gramK Q a b u'
      ∧ (u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V))

/-- **★ The reduction — the cone non-degeneracy discharges `GramCountsRecoverGram` (with `hψ` constructed).** A primitive
additive character on `K` exists (Mathlib `FiniteField.primitiveChar`, into a cyclotomic field of characteristic
`0 ≠ ringChar K`); equal counts give equal `countHat` (`countHat_eq_of_sameGramStratCounts`), which `countHat_factor`
rewrites into the factored equality; `IsoConeSumSeparatesGram` then yields `gramK u = gramK u'` (⟹ `SameExactGram`, via
`gramK_eq_iff_sameExactGram`) and the flag. **No `hψ` is carried** — it is discharged here. -/
theorem gramCountsRecoverGram_of_isoConeSep {a b : V}
    (hsep : IsoConeSumSeparatesGram Q a b) : GramCountsRecoverGram Q a b := by
  intro hbase u u' hcounts
  -- construct a primitive additive character on K (into a cyclotomic field of ℚ, characteristic 0)
  have hprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hchar : ringChar ℚ ≠ ringChar K := by
    rw [show ringChar ℚ = 0 from ringChar.eq ℚ 0]
    exact hprime.pos.ne
  let pac := AddChar.FiniteField.primitiveChar K ℚ hchar
  -- equal counts ⟹ equal countHat, then factor both sides
  have hfact : ∀ t : K × K × K,
      pac.char (t.1 * Q u + t.2.1 * QuadraticMap.polar Q u a + t.2.2 * QuadraticMap.polar Q u b)
          * isoConeSum Q pac.char (t.1 • u + t.2.1 • a + t.2.2 • b)
        = pac.char (t.1 * Q u' + t.2.1 * QuadraticMap.polar Q u' a + t.2.2 * QuadraticMap.polar Q u' b)
          * isoConeSum Q pac.char (t.1 • u' + t.2.1 • a + t.2.2 • b) := by
    intro t
    have hc := countHat_eq_of_sameGramStratCounts a b hcounts pac.char t
    rw [countHat_factor, countHat_factor] at hc
    exact hc
  obtain ⟨hg, hflag⟩ :=
    hsep hbase (R' := CyclotomicField pac.n ℚ) pac.char pac.prim u u' hfact
  exact ⟨gramK_eq_iff_sameExactGram.mp hg, hflag⟩

/-- **★ Capstone — `bᵢ = 1` for the round-3 observable, modulo the cone non-degeneracy + Witt.** Composing the reduction
with `gramCountsEq_iff_stabOrbit_refined`: at a `GoodBase`, `SameGramStratCounts u u' ↔ StabOrbit`, i.e. the round-3
cells ARE the `Stab({a,b})`-orbits, modulo exactly `IsoConeSumSeparatesGram` (the classical Gauss non-degeneracy) and
`RefinedWittExtends` (carried Witt). The primitive character is discharged. -/
theorem gramCountsEq_iff_stabOrbit_of_isoConeSep {a b : V} (hbase : GoodBase Q a b)
    (hsep : IsoConeSumSeparatesGram Q a b) (h2 : RefinedWittExtends Q a b) {u u' : V} :
    SameGramStratCounts Q a b u u' ↔ StabOrbit Q ({a, b} : Set V) u u' :=
  gramCountsEq_iff_stabOrbit_refined hbase (gramCountsRecoverGram_of_isoConeSep hsep) h2

end ChainDescent.GramStrat
