/-
# The observable↔count bridge at `|S| = 2` (increment 3/4/5 → `ZProfileSeparates`).

Increments 3/4/5 produce a base `T` that separates every pair `(u,v)` in the **pair-determinant
observable** `χ(det G₂(u;t,t₀))` (`ScratchC0Final.c0_le_threequarters` + the matching trick). But
`ScratchCrux.ZProfileSeparates` is stated in the **joint isotropic counts** `Z_u(S)`. The two are linked by
the `|S| = 2` case of Lemma A (`ScratchLemmaA`): on the **nondegenerate-config** locus, with `m = |S| = 2`
and **even `d`** (all the `VO^ε_{2m}(q)` families), the closed form collapses to

    Z_u({t,t₀}) · q³  =  qᵈ  +  χ(det G₂(u;t,t₀)) · K · (q · [c = 0] − 1),
    K = χ(disc Q) · gaussSum^{d+2}  (a NONZERO rational integer; `gaussSum²= χ(−1)·q`).

* the config-dependence enters **only** through `χ(det G₂)` (`ScratchLemmaA.configGaussSum_eq_det`:
  `∑_ρ ψ(s·QRρ) = χ(s)ⁿ·χ(D)·gaussSumⁿ`, `D = det` config Gram);
* `m = 2 ⟹ χ(−s⁻¹)² = 1` and even `d ⟹ χ(s)ᵈ = 1` kill the `s`-bracket, leaving
  `∑_{s≠0} ψ(−sc) = q·[c=0] − 1`.

So `Z` takes four values `qᵈ ± K`, `qᵈ ± K(q−1)` across the `(χ, [c=0]) ∈ {±1}×{0,1}` cases, which are
**distinct for `q > 2`** (`K ≠ 0`). Hence `χ(det G₂)_u ≠ χ(det G₂)_v ⟹ Z_u ≠ Z_v`: the matching's separating
pair forces the `Z`-profiles apart, discharging the contrapositive at the heart of `ZProfileSeparates`.

**This module proves B1b** — that distinctness consequence — from the abstract closed form, isolating the two
remaining open pieces:
* **B1a (assembly):** assemble the displayed closed form at `|S|=2` from `levelset_count_eq` +
  `configGaussSum_eq_det` + `sum_addChar_quadForm_smul` (the "big but mechanical" `D3a` at `m=2`, even `d`);
* **B1-deg:** the **degenerate-config** value (`det G₂ = 0`, `χ = 0`; `ScratchLemmaA` needs `IsUnit (det G)`),
  needed when a separating pair has `χ_u = 0` vs `χ_v = ±1`. This couples to the good-anchor predicate
  (`hgood`/`hnz`/`hPu` — increment 4): if the matching is restricted to config-nondegenerate separating pairs,
  the bridge only ever needs the `±1 / ±1` case proved here. (`q = 2` is out of scope: char-2, separate track.)

NOT in build (scratch; `lake env lean ChainDescent/ScratchBridge.lean`).
-/
import Mathlib.Tactic

namespace ChainDescent

/-- **B1b — the bridge distinctness (nondeg/nondeg case).** Given the `|S|=2` even-`d` closed form
`Z_w = n + χ_w · K · (q·b_w − 1)` (here `n = qᵈ`, `K = χ(disc Q)·gaussSum^{d+2}`, `b_w = [c_w = 0]`), with each
square-class `χ_w ∈ {±1}` (nondegenerate config), `b_w ∈ {0,1}`, `K ≠ 0`, and `q > 2`: if the two square-classes
differ then the two counts differ. So a pair that separates `(u,v)` in `χ(det G₂)` separates them in `Z`. -/
theorem chiSep_imp_zSep {n q K cu cv bu bv : ℤ}
    (hq : 2 < q) (hK : K ≠ 0)
    (hbu : bu = 0 ∨ bu = 1) (hbv : bv = 0 ∨ bv = 1)
    (hcu : cu = 1 ∨ cu = -1) (hcv : cv = 1 ∨ cv = -1)
    (hne : cu ≠ cv) :
    n + cu * K * (q * bu - 1) ≠ n + cv * K * (q * bv - 1) := by
  -- distinct square-classes in `{±1}` are negatives
  have hcv' : cv = -cu := by rcases hcu with h | h <;> rcases hcv with h' | h' <;> simp_all
  have hcu0 : cu ≠ 0 := by rcases hcu with h | h <;> subst h <;> norm_num
  -- the residual scalar factor is nonzero for `q > 2` and `b_u + b_v ∈ {0,1,2}`
  have hF : q * (bu + bv) - 2 ≠ 0 := by
    rcases hbu with h | h <;> rcases hbv with h' | h' <;> subst h <;> subst h' <;> omega
  rw [← sub_ne_zero]
  have hrw : (n + cu * K * (q * bu - 1)) - (n + cv * K * (q * bv - 1))
      = cu * K * (q * (bu + bv) - 2) := by subst hcv'; ring
  rw [hrw]
  exact mul_ne_zero (mul_ne_zero hcu0 hK) hF

/-- **B1b in the joint-count language — the per-pair bridge step.** Given the `|S|=2`, even-`d` closed form for the
joint isotropic count of each point (`Z_w · q³ = qᵈ + χ_w · K · (q·b_w − 1)`, the nondeg-config output of
`ScratchBridgeA.levelset_count_collapse` with `n = qᵈ`, `K = gaussSum²·∑ψ(Q)`, `χ_w = χ(det G₂_w)`, `b_w = [c_w=0]`),
two points whose pair invariants `χ(det G₂)` differ (`hne`) have **different joint counts** `Z_u ≠ Z_v` at that pair.
This is exactly what feeds `zProfileSeparates_of_zSep` (a config-nondeg χ-separating pair is a `Z`-separating
sub-frame). The hypotheses `hZu`/`hZv` are discharged by completing B1a's mechanical wrapping; everything else is
`chiSep_imp_zSep`. -/
theorem pairCount_ne_of_chiSep {Zu Zv n q K cu cv bu bv : ℤ}
    (hq : 2 < q)
    (hK : K ≠ 0)
    (hbu : bu = 0 ∨ bu = 1) (hbv : bv = 0 ∨ bv = 1)
    (hcu : cu = 1 ∨ cu = -1) (hcv : cv = 1 ∨ cv = -1)
    (hne : cu ≠ cv)
    (hZu : Zu * q ^ 3 = n + cu * K * (q * bu - 1))
    (hZv : Zv * q ^ 3 = n + cv * K * (q * bv - 1)) :
    Zu ≠ Zv := by
  intro h
  exact chiSep_imp_zSep hq hK hbu hbv hcu hcv hne (by rw [← hZu, ← hZv, h])

end ChainDescent

#print axioms ChainDescent.chiSep_imp_zSep
