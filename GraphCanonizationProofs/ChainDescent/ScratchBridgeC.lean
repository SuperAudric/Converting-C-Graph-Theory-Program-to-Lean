/-
# B1a wrapping (step ii-a) — the `|S| = 2` config-indexing + level-set reduction.

The bridge uses the joint count over a 2-element sub-frame `S = {t, t₀}`. This module connects the Lemma-A `fullcount`
over that `Finset` to the **homogeneous level-set count** (`reduction_to_levelset_nondeg`), by indexing the pair as the
`Fin 2` config `a = ![t̄−ū, t̄₀−ū]`:

`fullcount_{{t,t₀}}(u) = #{x : (∀ j, polar Q x (a j) = 0) ∧ Q x = −Q(∑ k, c k • a k)}`  (for a config-nondeg Gram).

Composing with `ScratchBridgeA.levelset_count_collapse` (wrap ii-b, a direct application) then gives the closed form
`fullcount · q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀ = 0] − 1)`.

NOT in build (scratch; `lake env lean`, after `lake build ChainDescent.ScratchBridgeA ChainDescent.ScratchBridgeB`).
-/
import ChainDescent.ScratchBridgeA
import ChainDescent.ScratchBridgeB

namespace ChainDescent

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **B1a wrap (ii-a) — fullcount over `{t,t₀}` = the homogeneous level-set count.** Index the pair `{t,t₀}` as the
`Fin 2` config `a = ![t̄−ū, t̄₀−ū]`; on the config-nondegenerate locus (`hG : IsUnit (config Gram det)`) the Lemma-A
fullcount equals the level-set count of `Q|_{Uᗮ}` at level `−Q w₀` for the spanning `w₀ = ∑ c k • a k`. Pure compose of
the `Finset {t,t₀}` ↔ `Fin 2` predicate conversion with the landed `reduction_to_levelset_nondeg`. -/
theorem fullcount_pair_eq_levelset (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (u t t₀ : Fin (p ^ d))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det) :
    ∃ c : Fin 2 → ZMod p,
      (Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
            Q (y - (affineE.symm s - affineE.symm u)) = 0)).card
        = (Finset.univ.filter (fun x : Fin d → ZMod p =>
          (∀ j, QuadraticMap.polar Q x
              (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j) = 0)
          ∧ Q x = - Q (∑ k, c k •
              (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k)))).card := by
  set a : Fin 2 → (Fin d → ZMod p) :=
    ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] with ha
  -- the Finset-`{t,t₀}` membership predicate equals the `Fin 2`-config predicate
  have hpred : (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
          Q (y - (affineE.symm s - affineE.symm u)) = 0))
      = (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ j, Q (y - a j) = 0)) := by
    apply Finset.filter_congr
    intro y _
    refine and_congr_right (fun _ => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.forall_fin_two, ha, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpred]
  exact reduction_to_levelset_nondeg Q a hG

open scoped Classical in
/-- **B1a wrap (ii-b) — the fullcount closed form over `{t,t₀}`.** Composing wrap (ii-a) with
`levelset_count_collapse`: for even `d` and a config-nondegenerate Gram, the Lemma-A fullcount over `{t,t₀}` satisfies
`fullcount · q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀ = 0] − 1)`, with `w₀ = ∑ c k • a k` the spanning solution and
`D = det` of the config Gram. The level bit `[c=0]` is `[−Q w₀ = 0] = [Q w₀ = 0]`. This is the fullcount side of the
bridge's per-pair closed form; the observable `jointIsoCount` then equals `fullcount − corr` (wrap (i)). -/
theorem fullcount_pair_closed (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (u t t₀ : Fin (p ^ d)) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ∃ w₀ : Fin d → ZMod p,
      ((Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
            Q (y - (affineE.symm s - affineE.symm u)) = 0)).card : R') * (p : R') ^ 3
        = (Fintype.card (Fin d → ZMod p) : R')
          + ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
              ((LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
                (QuadraticMap.associated (configForm Q
                  ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u]))).det)
            * (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) ψ ^ 2
                * ∑ x : Fin d → ZMod p, ψ (Q x))
            * ((p : R') * (if Q w₀ = 0 then 1 else 0) - 1) := by
  obtain ⟨c, hc⟩ := fullcount_pair_eq_levelset Q u t t₀ hG
  refine ⟨∑ k, c k • (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k), ?_⟩
  rw [hc, levelset_count_collapse Q hF
      ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u]
      (- Q (∑ k, c k • (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k)))
      hd hG hψ v hv hw]
  simp only [neg_eq_zero]

end ChainDescent

#print axioms ChainDescent.fullcount_pair_eq_levelset
#print axioms ChainDescent.fullcount_pair_closed
