/-
# Route A, increment 2 — the `d`-cancellation, via the seal's own count-factoring (REUSE)

**The finding that shapes this module.** The "complement-factoring" route A's increment 2 was scoped to build — decompose
`V = ⟨a⟩ ⊕ ⟨a⟩ᗮ`, factor the isotropy count, cancel the `(d−2)`-dim complement's contribution — is **already built**, for
the quasipoly seal, in `IsotropicIncidenceCountK`: `reduction_to_levelsetK` does the `V = U ⊕ Uᗮ` split, and
`levelset_count_eqK` gives the level-set count in closed form
`count·|K|^{m+1} = |V| + ∑_{s≠0} ∑_ρ ψ(−sc)·(ψ(−s⁻¹·Q(∑ⱼρⱼaⱼ))·∑_x ψ(s·Q x))`. In that formula the **`d`-dependence
is confined to two config-independent factors** — `|V| = |K|^d` and the global Gauss sum `∑_x ψ(s·Q x)` — and the whole
**config-dependence collapses, via `configGaussSum_eq_detK`, to the single scalar `χ(det G_config)`** (the discriminant
character of the config Gram). This module *harvests* that: the level-set count factors through `χ(det G_config)` and the
level `c`, **uniformly in `d`**. That is exactly the increment-2 cancellation — reused, not rebuilt.

**What this lemma is (and what it teaches route A).** `levelset_count_factors_through_chiDet`: two configs `a, a'` of the
same size with the **same discriminant character** `χ(det G_a) = χ(det G_{a'})` give the **same** (scaled) level-set count
at every level `c`, for every `d`. The `d`-factors (`|V|`, the global Gauss sum) are common and cancel; the config enters
only through `χ(det)`. **Consequence for route A (the honest re-scope):** a *single* isotropy count is therefore only
`χ(det)`-valued — a **2-valued** function of the config (this is why the seal needed a *matching* of many pairs to reach
frame discreteness, `c₀ ≤ ¾` + union). So route A's *exact-Gram* recovery `(Q u, polar u a, polar u b)` at a span-dim-2
base cannot come from one count; it needs the profile over the **sub-configs** `S ⊆ {0,a,b}` (⟹ `ZProfileSeparatesK`) and
the **iterated** observable (the probe's `r* ∈ {3,4}` rounds — the `χ(det G₂)` 2-WL fixpoint), not the single round. This
module pins the single-round content (factored + `d`-cancelled); the remaining route-A content is the iteration, which the
probe says is `d`-flat.

Reuses `IsotropicIncidenceCountK` (`levelset_count_eqK`, `configFormK`, `configGaussSum_eq_detK`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.IsotropicIncidenceCountK

namespace ChainDescent.ComplementFactorK

open QuadraticMap Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
  {d : ℕ}

open scoped Classical in
/-- **★ The `d`-cancellation (increment 2, reused).** For two configs `a, a'` of the same size `m`, both with
nondegenerate config Gram, whose config-Gram **discriminant characters agree** (`χ(det G_a) = χ(det G_{a'})`), the
(scaled) homogeneous level-set counts at every level `c` are **equal — uniformly in `d`**. The `d`-dependent factors of
`levelset_count_eqK` (`|V| = |K|^d` and the global Gauss sum `∑_x ψ(s·Q x)`) are config-independent, so they cancel; the
config enters only through `χ(det)` (collapsed by `configGaussSum_eq_detK`). This is the complement-factoring's payoff:
the isotropy count factors through the *local* config invariant, with the `(d−2)`-dim complement contributing only the
common global Gauss factor. (It also shows a single count is `χ(det)`-valued — see the module header for the route-A
consequence.) -/
theorem levelset_count_factors_through_chiDet
    (Q : QuadraticForm K (Fin d → K)) (hF : ringChar K ≠ 2)
    {m : ℕ} (a a' : Fin m → (Fin d → K)) (c : K)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det)
    (hG' : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a' i) (a' j)) :
        Matrix (Fin m) (Fin m) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (hχ : ((quadraticChar K).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin m → K))
              (QuadraticMap.associated (configFormK Q a))).det)
          = ((quadraticChar K).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin m → K))
              (QuadraticMap.associated (configFormK Q a'))).det)) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1)
    = ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a' j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1) := by
  classical
  rw [levelset_count_eqK Q a c hG hψ, levelset_count_eqK Q a' c hG' hψ]
  -- the `|V|` boundary is common; match the `s ≠ 0` bulk termwise.
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
  set u : Kˣ := Units.mk0 (-s⁻¹) (neg_ne_zero.mpr (inv_ne_zero hs0)) with hu
  have huval : (u : K) = -s⁻¹ := rfl
  -- factor the (ρ-independent) `ψ(−sc)` and global Gauss sum out of the ρ-sum, then apply `configGaussSum_eq_detK`.
  have key : ∀ b : Fin m → (Fin d → K),
      IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (b i) (b j)) :
        Matrix (Fin m) (Fin m) K).det →
      (∑ ρ : Fin m → K, ψ (-(s * c)) *
          (ψ (-(s⁻¹ * Q (∑ j, ρ j • b j))) * ∑ x : Fin d → K, ψ (s * Q x)))
      = (ψ (-(s * c)) * ∑ x : Fin d → K, ψ (s * Q x)) *
          (((quadraticChar K).ringHomComp (Int.castRingHom R')) (u : K)
              ^ Module.finrank K (Fin m → K)
            * (((quadraticChar K).ringHomComp (Int.castRingHom R'))
                ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin m → K))
                  (QuadraticMap.associated (configFormK Q b))).det)
              * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
                  ^ Module.finrank K (Fin m → K))) := by
    intro b hGb
    have hsum : (∑ ρ : Fin m → K, ψ (-(s * c)) *
          (ψ (-(s⁻¹ * Q (∑ j, ρ j • b j))) * ∑ x : Fin d → K, ψ (s * Q x)))
        = (ψ (-(s * c)) * ∑ x : Fin d → K, ψ (s * Q x)) *
            ∑ ρ : Fin m → K, ψ ((u : K) * configFormK Q b ρ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      rw [configFormK_apply, huval, neg_mul, ← neg_mul, inv_mul_eq_div, ← neg_div, neg_mul]
      ring
    rw [hsum, configGaussSum_eq_detK Q hF b hGb hψ u]
  rw [key a hG, key a' hG', hχ]

end ChainDescent.ComplementFactorK
