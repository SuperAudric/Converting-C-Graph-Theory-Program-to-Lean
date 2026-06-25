/-
# B1a — the `|S| = 2`, even-`d` closed-form collapse for the observable↔count bridge.

The bridge (`ScratchBridge`) consumes the `|S|=2` closed form `Z_w · q³ = qᵈ + χ(det G₂_w)·K·(q[c=0]−1)`.
This module assembles the **analytic heart** of B1a: the collapse of `levelset_count_eq`'s `s`-sum, for the
config size `m = |S| = 2` and **even** form dimension `d`, into

    (level-set count at `c`) · q³  =  |V|  +  χ(D) · (gaussSum² · W) · (q·[c = 0] − 1),

where `D = det` of the config Gram, `W = ∑_x ψ(Q x)` the global quadratic Gauss sum (both *config/`u`-independent*
up to `D`), `q = #K`. Mechanism: in `levelset_count_eq`'s `∑_{s≠0} ∑_ρ …`,
* the config `ρ`-sum is `configGaussSum_eq_det`: `χ(−s⁻¹)²·χ(D)·gaussSum²` (config-dependence only via `χ(D)`);
* the global `x`-sum is `sum_addChar_quadForm_smul`: `χ(s)ᵈ·W`;
* `m = 2 ⟹ χ(−s⁻¹)² = 1` and **even `d` ⟹ χ(s)ᵈ = 1**, so the `s`-character powers vanish, leaving
  `∑_{s≠0} ψ(−s·c) = q·[c=0] − 1` (additive orthogonality, `AddChar.sum_mulShift`).

The `χ(D)` factor is the pair invariant `χ(det G₂)` the bridge separates on. The remaining B1a steps (off this
analytic core, all landed-tool or mechanical): the cone-count↔level-set reduction (`reduction_to_levelset_nondeg` +
the `w=0` correction `ScratchLemmaB.cone_count_zero_split`), the `D ↔ pairForm` identification, and the `R'→ℕ`
descent (`÷q³`). NOT in build (scratch; `lake env lean ChainDescent/ScratchBridgeA.lean`).
-/
import ChainDescent.ScratchLemmaA

namespace ChainDescent

open QuadraticMap Finset Module

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **B1a analytic core — the `|S|=2`, even-`d` `s`-sum collapse.** For a nondegenerate config Gram (`hG`), config
size `m = 2`, and **even** `d` with an orthogonal anisotropic basis `v` of `Q` (`hv`/`hw`), the level-set count at
level `c` satisfies
`count · q³ = |V| + χ(D) · (gaussSum² · W) · (q·[c=0] − 1)`,
`D = det` of `associated (configForm Q a)` at `finBasis`, `W = ∑_x ψ(Q x)`. The config-dependence enters **only**
through `χ(D)` (= the pair invariant `χ(det G₂)`) — the property the bridge needs. -/
theorem levelset_count_collapse (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (a : Fin 2 → (Fin d → ZMod p)) (c : ZMod p) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R') * (p : R') ^ 3
      = (Fintype.card (Fin d → ZMod p) : R')
        + ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
              (QuadraticMap.associated (configForm Q a))).det)
          * (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) ψ ^ 2
              * ∑ x : Fin d → ZMod p, ψ (Q x))
          * ((p : R') * (if c = 0 then 1 else 0) - 1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R') with hχ
  set g := gaussSum χ ψ with hg
  set W := ∑ x : Fin d → ZMod p, ψ (Q x) with hW
  set D := (LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
      (QuadraticMap.associated (configForm Q a))).det with hD
  -- the landed closed form, then collapse the `s`-sum
  rw [show ((p : R') ^ 3) = (p : R') ^ (2 + 1) from by norm_num, levelset_count_eq Q a c hG hψ]
  congr 1
  -- per-`s` evaluation of the inner `ρ`-sum
  have hsq : ∀ t : ZMod p, t ≠ 0 → χ t ^ 2 = 1 := by
    intro t ht
    have h := quadraticChar_sq_one (F := ZMod p) ht
    have : (χ t) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hterm : ∀ s ∈ Finset.univ.erase (0 : ZMod p),
      (∑ ρ : Fin 2 → ZMod p, ψ (-(s * c)) *
          (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x)))
        = ψ (-(s * c)) * (χ D * (g ^ 2 * W)) := by
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    -- factor out the `ρ`-independent pieces
    have hfac : ∀ ρ : Fin 2 → ZMod p,
        ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x))
          = (ψ (-(s * c)) * ∑ x : Fin d → ZMod p, ψ (s * Q x))
            * ψ ((-(s⁻¹)) * configForm Q a ρ) := by
      intro ρ
      rw [configForm_apply, show (-(s⁻¹)) * Q (∑ j, ρ j • a j) = -(s⁻¹ * Q (∑ j, ρ j • a j)) from by
        ring]
      ring
    rw [Finset.sum_congr rfl (fun ρ _ => hfac ρ), ← Finset.mul_sum]
    -- config `ρ`-sum via `configGaussSum_eq_det` at the unit `s' = -s⁻¹`
    have hsinv : (-(s⁻¹)) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
    have hcfg := configGaussSum_eq_det Q hF a hG hψ (Units.mk0 (-(s⁻¹)) hsinv)
    rw [Units.val_mk0] at hcfg
    rw [hcfg]
    -- global `x`-sum via `sum_addChar_quadForm_smul` at the unit `s`
    have hglob := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 s hs0)
    rw [Units.val_mk0] at hglob
    rw [hglob, ← hW]
    -- kill the `s`-character powers (`m = 2` even, `d` even) by rewriting only the power subterms
    have hp1 : χ (-(s⁻¹)) ^ (Module.finrank (ZMod p) (Fin 2 → ZMod p)) = 1 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]; exact hsq _ hsinv
    have hp2 : χ s ^ (Module.finrank (ZMod p) (Fin d → ZMod p)) = 1 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]
      obtain ⟨r, hr⟩ := hd
      rw [hr, ← two_mul, pow_mul, hsq s hs0, one_pow]
    have hp3 : g ^ (Module.finrank (ZMod p) (Fin 2 → ZMod p)) = g ^ 2 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]
    rw [hp1, hp2, hp3]
    simp only [hχ, hg, hW, hD]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  -- additive orthogonality: `∑_{s≠0} ψ(−(s·c)) = q·[c=0] − 1`
  have horth : (∑ s ∈ Finset.univ.erase (0 : ZMod p), ψ (-(s * c)))
      = (p : R') * (if c = 0 then 1 else 0) - 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod p)),
      Finset.sum_congr rfl (fun s _ => by rw [show -(s * c) = s * (-c) from by ring]),
      AddChar.sum_mulShift (-c) hψ]
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, ZMod.card, neg_eq_zero]
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · simp [hc]
  rw [horth]
  ring

end ChainDescent

#print axioms ChainDescent.levelset_count_collapse
