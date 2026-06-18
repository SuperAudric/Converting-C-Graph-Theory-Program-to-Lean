/-
# Gauss-sum point-count infrastructure for Stage B.1c-ii (the "Gauss build")

WORK IN PROGRESS — develop here, port into `CascadeAffine.lean` (near §OrthogonalForm) once Bricks
C and D land. Everything below is PROVEN and axiom-clean `[propext, Classical.choice, Quot.sound]`
(verified via `lake env lean ChainDescent/ScratchGauss.lean`). This file imports ONLY Mathlib, so it
builds in isolation (cheap) — it does NOT pull in the heavy project modules.

Target (CORRECTED — see the ⚠⚠ block below): discharge the seal's node-4 forms-graph residue (B.1c-ii) for
`VO^ε_4(q)`. NOTE the original target `IsotropyCountsRecoverFrameQ Q` at the standard frame is FALSE/mis-shaped
(⚠⚠ below); the corrected target is **one-round count-injectivity at a symmetry-broken base** (`≈ d+2`), built
from these Gauss bricks. Mathlib has the machinery (`gaussSum_sq`, `quadraticChar_card_sqrts`,
`equivalent_weightedSumSquares`, char orthogonality) but NOT the assembled affine-quadric point-count formula —
that is what these bricks build.

DONE (this file — the full exponential-sum core + the assembled point count):
* Brick A  `count_eq_charsum`        — solution count `#{x | f x = c}` as a double character sum.
* Brick B1 `sum_addChar_sq`          — `∑_x ψ(x²) = gaussSum χ ψ`.
* Brick B2 `sum_addChar_smul_sq`     — `∑_x ψ(a·x²) = χ(a)·gaussSum χ ψ` (a a unit).
* helper   `addChar_sum`             — `ψ(∑ aᵢ) = ∏ ψ(aᵢ)`.
* Brick B3 `sum_addChar_quadForm`    — `∑_x ψ(Q x) = (∏ᵢ χ(wᵢ))·gaussSum^d` for nondegenerate `Q`
                                       (diagonalize + reindex + factor). THE multivariable core.
* Brick B3′`sum_quadForm_eval`       — basis-explicit B3 (weights `Q (v i)`; value pinned).
* scaling  `sum_addChar_quadForm_smul` — `∑_x ψ(s·Q x) = χ(s)^d · ∑_x ψ(Q x)` (change of character).
* Brick C  `card_quadForm_eq`        — THE affine-quadric point count (Mathlib-absent), character-sum
                                       form: `#{x:Q x=c}·q = #V + (∑_{t≠0} ψ(−tc)·χ(t)^d)·∑_x ψ(Q x)`.

* Brick D1 `sum_addChar_quadForm_linear` — complete-the-square: `∑_w ψ(r·Qw + polar Q w a') =
             ψ(−r⁻¹·Q a')·∑_w ψ(r·Qw)`. The engine for hyperplane-section / joint counts.
* Brick A2 `count2_eq_charsum`       — two-condition count = double char sum (generalizes Brick A).
* helpers  `quad_sub` (`Q(a−b)=Qa+Qb−polar Q a b`), `polar_sum_right` (`∑ rⱼ·polar Q z tⱼ = polar Q z (∑rⱼ•tⱼ)`).
* MULTI-POINT `sum_addChar_multiQuad` — `∑_z ψ(∑ⱼ rⱼ·Q(z−tⱼ)) = ψ(∑rⱼQtⱼ − R⁻¹·Q(∑rⱼ•tⱼ))·∑_z ψ(R·Qz)`
             (`R=∑rⱼ≠0`). The summand collapses to D1 via `quad_sub`+`polar_sum_right`. THE engine for the
             multi-point count at a symmetry-broken base — the inner sum of the k-fold count.

⚠ KEY FINDING (2026-06-18) — the naive PAIRWISE plan for Brick D FAILS; recovery needs the FULL joint
frame count. Computing the pairwise common-isotropic-neighbour count via A2 + D1 + a Gauss collapse:
    #{w : Q w = 0 ∧ Q (w − a) = 0} = #{w : Q w = 0 ∧ polar Q w a = Q a} = q² + S(1)/q   (d = 4),
S(1) = ∑_x ψ(Q x) = ±q². This is INDEPENDENT of which anisotropic shell `a` lies in (VO^-_4(3):
9 + (−9)/3 = 6 for both Q a = 1 and Q a = 2). Reason: a similitude `g` of factor `μ` preserves the cone
{Q=0} and maps shell {Q=1}→{Q=μ}, so ANY count built from the cone + a SINGLE point `a` is similitude-
invariant ⟹ shell-blind. So pairwise (one frame point + u) counts CANNOT recover `χ(Q(ū−t))`; the
earlier "hyperplane-section depends on χ(Q a)" idea is WRONG (the χ(Q a) dependence cancels — confirmed
by the Gauss collapse AND the similitude symmetry).

⚠⚠ OPEN QUESTION RESOLVED (2026-06-18, finite probe over VO^ε_4(3), /tmp/isoprobe*.py) — the standard-frame
predicates are MIS-SHAPED; fix = a symmetry-broken base. Findings:
  (1) `IsotropyCountsRecoverFrameQ` / `SimilitudeFrameSeparates` (the one-round count at the standard frame
      {0,e₀,…,e_d}) are **FALSE for VO^-_4(3)**: u=(0,0,1,2), u'=(0,0,2,1) have IDENTICAL one-round
      isotropy-counts to the frame but different Q-profiles (Q(u−e₂)=1 vs 2). Cause: Q=x₀x₁+x₂²+x₃² is
      symmetric in x₂,x₃, and the count (a coarser invariant than orbits) is blind to it at the symmetric
      frame. (VO^+_4(3) is FINE at the standard frame — issue is minus-type symmetry.)
  (2) The SCHEME genuinely discretizes: iterated 1-WL from the frame → 81 singletons in 2 rounds, separates
      u,u'. So bounded WL-dim HOLDS; only the one-round-count-at-symmetric-frame predicate is wrong.
  (3) THE PROJECT ENGINE `discrete_of_kRoundRelationSeparates` consumes exactly the ONE-ROUND count
      (CascadeAffine:1918-1924; k-independent — k only proves the count is a warmRefine invariant), so it
      CANNOT discharge VO^- at the standard frame, though the conclusion (warmRefine Discrete) is true.
  (4) FIX: the one-round count IS injective at a slightly larger, symmetry-broken base. Well-chosen (greedy)
      one-round base is small + slow-growing: VO^ε_4(3)→4, VO^±_4(5)→6 (both types). Frame-based bigger:
      VO^-_4(3)→6, VO^+_4(5)→7 — matches Probe_FormsGraphs [5,5,6,7] q=2..5 (so that probe = ONE-ROUND base).
      Net ≈ d+2, slow q-dep, bounded. B.0 (isometry O(Q)) UNAFFECTED (relation=Q-value, depth-1). First
      target q=3,d=4 = frame+1 (size 6) or greedy size-4.

CONSEQUENCE — the landed B.1 checkpoint capstones (`reachesRigidOrCameron_via{IsotropyCounts,CountsDetermineFrameQ,
SimilitudeForm}`) are axiom-clean but have UNPROVABLE hypotheses as stated (tied to the symmetric frame); they
need REFORMULATION with a symmetry-broken base. The "recover Q-profile then coords_determine" architecture is
also wrong for minus-type (front half false); the correct target is direct count-injectivity at the bigger base.

NEXT (next session) — Brick D, corrected target:
* In CascadeAffine: replace the standard-frame predicate by "∃ bounded base `T` (size ≤ d+2, e.g.
  `frameBase ∪ {p}`) on which the one-round relation-count profile separates all vertices" — then
  `discrete_of_kRoundRelationSeparates` gives `Discrete` → `SeparatesAtBoundedBase` → seal directly (no
  coords_determine / Q-profile recovery needed).
* The PROOF of count-injectivity at `T` is the genuine content. Remaining engine step: the **k-fold count**
  `#{z : Q(z−tⱼ)=cⱼ ∀j∈T} · q^|T| = ∑_{r:T→K} (∏ⱼ ψ(−rⱼcⱼ))·∑_z ψ(∑ⱼ rⱼ Q(z−tⱼ))` (generalize `count2_eq_charsum`
  to a Finset of conditions), whose inner sum is now `sum_addChar_multiQuad` (R=∑rⱼ≠0) or a linear boundary
  (R=0). That gives the closed-form multi-point Q-count; then (a) inclusion–exclusion turns isotropy counts
  into Q-counts, (b) prove the resulting `A_u` injective in `u` at the symmetry-broken base. The Gauss toolkit
  (A/A2/B/C/D1/multiQuad) is COMPLETE; remaining is the k-fold assembly + the injectivity argument.
* Brick C-even (independent, short) — `d` even ⟹ `χ(t)^d=1` ⟹ closed `q^{d-1}±(q-1)q^{d/2-1}` via
  `AddChar.sum_mulShift` + `gaussSum_sq`. Validates Brick C numerically.
* Bridge `(Q.polarBilin).Nondegenerate ⟹ (associated Q).SeparatingLeft` (`two_nsmul_associated` +
  `Invertible(2:ZMod p)`) + orthogonal basis for `VO^ε_4(3)`. Then PORT into CascadeAffine.

CAVEAT: the bricks require `[Invertible (2:K)]` / `ringChar ≠ 2` — char-2 (`q = 2,4`) is a separate
argument (§5 R2′); do `q = 3` first.
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open Finset Module

/-- **Brick A — solution count as a character sum.** -/
theorem count_eq_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] (f : V → F) (c : F) :
    (∑ x : V, ∑ t : F, ψ (t * (f x - c)))
      = ((univ.filter (fun x : V => f x = c)).card : R') * (Fintype.card F : R') := by
  have hinner : ∀ x : V, (∑ t : F, ψ (t * (f x - c)))
      = if f x = c then (Fintype.card F : R') else 0 := by
    intro x
    rw [AddChar.sum_mulShift (f x - c) hψ]
    simp [sub_eq_zero]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

/-- **Brick B1 — the 1-dimensional quadratic Gauss sum.** For a finite field `F` of odd
characteristic and a nontrivial additive character `ψ`, the quadratic exponential sum
`∑_x ψ(x²)` equals the Gauss sum of the quadratic character. (Each value `y` is hit by
`χ(y)+1` square roots; the `+1` part sums to `0`.) -/
theorem sum_addChar_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2))
      = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom R')) ψ := by
  have hfib : (∑ x : F, ψ (x ^ 2))
      = ∑ y : F, ∑ x ∈ univ.filter (fun x : F => x ^ 2 = y), ψ y := by
    rw [← Finset.sum_fiberwise (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x hx => ?_))
    rw [(Finset.mem_filter.1 hx).2]
  rw [hfib]
  have hcard : ∀ y : F, ((univ.filter (fun x : F => x ^ 2 = y)).card : R')
      = ((quadraticChar F).ringHomComp (Int.castRingHom R')) y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts hF y
    rw [Set.toFinset_setOf] at h
    have : ((univ.filter (fun x : F => x ^ 2 = y)).card : ℤ) = quadraticChar F y + 1 := h
    have hcast := congrArg (Int.cast (R := R')) this
    push_cast at hcast
    rw [hcast]
    simp [MulChar.ringHomComp]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => by rw [hcard y])]
  rw [gaussSum]
  rw [Finset.sum_congr rfl (fun y _ => by rw [add_mul, one_mul])]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]

/-- **Brick B2 — the scaled quadratic Gauss sum.** For a unit `a`, the scaled sum `∑_x ψ(a·x²)`
equals `χ(a) · gaussSum χ ψ`. (Via `gaussSum_mulShift` and `χ(a)² = 1`.) -/
theorem sum_addChar_smul_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive) (a : Fˣ) :
    (∑ x : F, ψ ((a : F) * x ^ 2))
      = ((quadraticChar F).ringHomComp (Int.castRingHom R')) (a : F)
        * gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom R')) ψ := by
  set χ := (quadraticChar F).ringHomComp (Int.castRingHom R') with hχ
  have hne : (AddChar.mulShift ψ (a : F)) ≠ 1 := hψ a.ne_zero
  have hB1 : (∑ x : F, ψ ((a : F) * x ^ 2)) = gaussSum χ (AddChar.mulShift ψ (a : F)) := by
    rw [← sum_addChar_sq hF hne]
    exact Finset.sum_congr rfl (fun x _ => by rw [AddChar.mulShift_apply])
  have hms := gaussSum_mulShift χ ψ a
  have hsq : χ (a : F) * χ (a : F) = 1 := by
    have h := quadraticChar_sq_one (F := F) a.ne_zero
    have : χ (a : F) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    rw [pow_two] at this; simpa using this
  rw [hB1]
  have := congrArg (fun z => χ (a : F) * z) hms
  simp only at this
  rw [← mul_assoc, hsq, one_mul] at this
  rw [this]

/-- An additive character turns a finite sum into a finite product. -/
theorem addChar_sum {F : Type*} [AddCommGroup F] {R' : Type*} [CommMonoid R'] (ψ : AddChar F R')
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → F) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  induction s using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

/-- **Brick B3 — the multivariable quadratic Gauss sum.** For a nondegenerate quadratic form `Q` on a
finite-dimensional space over a finite field of odd characteristic, the exponential sum `∑_x ψ(Q x)`
diagonalizes to `(∏ᵢ χ(wᵢ)) · gaussSum^d`, where the `wᵢ` are the (nonzero) diagonal weights and
`d = finrank`. (Diagonalize via `equivalent_weightedSumSquares`; reindex; the additive character
factors the diagonal sum into a product of 1-D Gauss sums, each evaluated by Brick B2.) -/
theorem sum_addChar_quadForm {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] (Q : QuadraticForm K V) (hQ : (QuadraticMap.associated (R := K) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank K V) → Kˣ,
      (∑ x : V, ψ (Q x))
        = (∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (w i : K))
          * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
              ^ Module.finrank K V := by
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ
  refine ⟨w, ?_⟩
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  have hreindex : (∑ x : V, ψ (Q x))
      = ∑ y : (Fin (Module.finrank K V) → K), ψ (QuadraticMap.weightedSumSquares K w y) := by
    rw [← Equiv.sum_comp e.toLinearEquiv.toEquiv (fun y => ψ (QuadraticMap.weightedSumSquares K w y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    exact (e.map_app' x).symm
  rw [hreindex]
  have hexp : ∀ y : (Fin (Module.finrank K V) → K),
      ψ (QuadraticMap.weightedSumSquares K w y) = ∏ i, ψ ((w i : K) * (y i) ^ 2) := by
    intro y
    rw [QuadraticMap.weightedSumSquares_apply, addChar_sum]
    exact Finset.prod_congr rfl (fun i _ => by simp only [Units.smul_def, smul_eq_mul, pow_two])
  rw [Finset.sum_congr rfl (fun y _ => hexp y),
    ← Fintype.prod_sum (fun (i : Fin (Module.finrank K V)) (t : K) => ψ ((w i : K) * t ^ 2)),
    Finset.prod_congr rfl (fun i _ => sum_addChar_smul_sq hF hψ (w i)),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Brick B3′ — basis-explicit multivariable Gauss sum.** As `sum_addChar_quadForm` but with an
explicit orthogonal basis `v` (weights `Q (v i)`), so the value is pinned (no existential). This is
the form that powers the scaling relation (Brick C). -/
theorem sum_quadForm_eval {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] (Q : QuadraticForm K V) (v : Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    (∑ x : V, ψ (Q x))
      = (∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q (v i)))
        * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ Module.finrank K V := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  let e := QuadraticForm.isometryEquivWeightedSumSquares Q v hv
  have hreindex : (∑ x : V, ψ (Q x))
      = ∑ y : (Fin (Module.finrank K V) → K),
          ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y) := by
    rw [← Equiv.sum_comp e.toLinearEquiv.toEquiv
      (fun y => ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    exact (e.map_app' x).symm
  rw [hreindex]
  have hexp : ∀ y : (Fin (Module.finrank K V) → K),
      ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y) = ∏ i, ψ (Q (v i) * (y i) ^ 2) := by
    intro y
    rw [QuadraticMap.weightedSumSquares_apply, addChar_sum]
    exact Finset.prod_congr rfl (fun i _ => by rw [pow_two, smul_eq_mul])
  have hfac : ∀ i, (∑ t : K, ψ (Q (v i) * t ^ 2)) = χ (Q (v i)) * gaussSum χ ψ := by
    intro i
    have h := sum_addChar_smul_sq hF hψ (Units.mk0 (Q (v i)) (hw i))
    rw [Units.val_mk0] at h
    rw [← hχ] at h
    exact h
  rw [Finset.sum_congr rfl (fun y _ => hexp y),
    ← Fintype.prod_sum (fun (i : Fin (Module.finrank K V)) (t : K) => ψ (Q (v i) * t ^ 2)),
    Finset.prod_congr rfl (fun i _ => hfac i),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Brick C-scale — the scaling relation.** Scaling the form by a unit `s` scales the Gauss sum by
`χ(s)^d`: `∑_x ψ(s·Q x) = χ(s)^d · ∑_x ψ(Q x)`. Proved by changing the additive character
(`ψ(s·Q x) = (mulShift ψ s)(Q x)`) and `gaussSum_mulShift`. (For `d` even, `χ(s)^d = 1`, so the
quadratic exponential sum is scale-invariant — the fact behind the affine-quadric point count.) -/
theorem sum_addChar_quadForm_smul {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Invertible (2 : K)] (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype V] (Q : QuadraticForm K V)
    (v : Module.Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) (s : Kˣ) :
    (∑ x : V, ψ ((s : K) * Q x))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) ^ Module.finrank K V
        * ∑ x : V, ψ (Q x) := by
  have hφ : (AddChar.mulShift ψ (s : K)).IsPrimitive := by
    intro a ha
    have hmm : AddChar.mulShift (AddChar.mulShift ψ (s : K)) a = AddChar.mulShift ψ ((s : K) * a) := by
      ext x; simp only [AddChar.mulShift_apply, mul_assoc]
    rw [hmm]; exact hψ (mul_ne_zero s.ne_zero ha)
  have e1 : (∑ x : V, ψ ((s : K) * Q x)) = ∑ x : V, (AddChar.mulShift ψ (s : K)) (Q x) :=
    Finset.sum_congr rfl (fun x _ => by rw [AddChar.mulShift_apply])
  have hsq : ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
      * ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) = 1 := by
    have h := quadraticChar_sq_one (F := K) s.ne_zero
    have h2 : (((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)) ^ 2 = ((1 : ℤ) : R') := by
      rw [MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    rw [pow_two] at h2; simpa using h2
  have hgss : gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R'))
        (AddChar.mulShift ψ (s : K))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
        * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ := by
    have hms := gaussSum_mulShift ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ s
    have h3 := congrArg
      (fun z => ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) * z) hms
    simp only at h3
    rw [← mul_assoc, hsq, one_mul] at h3
    exact h3
  rw [e1, sum_quadForm_eval hF hφ Q v hv hw, sum_quadForm_eval hF hψ Q v hv hw, hgss, mul_pow]
  ring

/-- **Brick C — the affine-quadric point count (character-sum form).** The number of solutions of
`Q x = c`, scaled by `#K`, equals `#V` plus `(∑_{t≠0} ψ(−tc)·χ(t)^d)·∑_x ψ(Q x)`. This is the
assembled affine-quadric point-count formula (Mathlib-absent), from Brick A + the scaling relation.
For `d` even, `χ(t)^d = 1`, so the bracket collapses to `q−1` (if `c=0`) or `−1` (if `c≠0`) by
additive orthogonality, giving the classical `q^{d-1} ± (q-1)q^{d/2-1}` count once `∑_x ψ(Q x)` is
evaluated via `gaussSum_sq`. -/
theorem card_quadForm_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (Q : QuadraticForm K V)
    (v : Module.Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) (c : K) :
    ((univ.filter (fun x : V => Q x = c)).card : R') * (Fintype.card K : R')
      = (Fintype.card V : R')
        + (∑ t ∈ univ.erase (0 : K),
            ψ (-(t * c)) * ((quadraticChar K).ringHomComp (Int.castRingHom R')) t
              ^ Module.finrank K V) * (∑ x : V, ψ (Q x)) := by
  have hcount := count_eq_charsum hψ (fun x : V => Q x) c
  have hsplit_x : ∀ t : K,
      (∑ x : V, ψ (t * (Q x - c))) = ψ (-(t * c)) * ∑ x : V, ψ (t * Q x) := by
    intro t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hzero : ψ (-((0 : K) * c)) * (∑ x : V, ψ ((0 : K) * Q x)) = (Fintype.card V : R') := by
    simp [AddChar.map_zero_eq_one, Finset.card_univ]
  have hLHS : (∑ x : V, ∑ t : K, ψ (t * (Q x - c)))
      = (Fintype.card V : R')
        + (∑ t ∈ univ.erase (0 : K),
            ψ (-(t * c)) * ((quadraticChar K).ringHomComp (Int.castRingHom R')) t
              ^ Module.finrank K V) * (∑ x : V, ψ (Q x)) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun t _ => hsplit_x t),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), hzero, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have htne : t ≠ 0 := Finset.ne_of_mem_erase ht
    have hsc := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 t htne)
    rw [Units.val_mk0] at hsc
    rw [hsc]; ring
  rw [← hcount, hLHS]

/-- **Brick D1 — the quadratic-plus-linear sum (complete the square).** For a unit `r` and any `a'`,
`∑_w ψ(r·Q w + polar Q w a') = ψ(−r⁻¹·Q a')·∑_w ψ(r·Q w)`. The linear term is absorbed by the shift
`w ↦ w + r⁻¹·a'`; the residual constant `−r⁻¹·Q a'` factors out. This is the engine of the
hyperplane-section counts that Brick D needs (the isotropy joint-count reduces to such sums). Needs no
diagonalization or primitivity — pure reindexing + additivity of `ψ`. -/
theorem sum_addChar_quadForm_linear {K : Type*} [Field K] {R' : Type*} [CommRing R']
    (ψ : AddChar K R') {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (Q : QuadraticForm K V) (r : Kˣ) (a' : V) :
    (∑ w : V, ψ ((r : K) * Q w + QuadraticMap.polar Q w a'))
      = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q w) := by
  have hr : (r : K) ≠ 0 := r.ne_zero
  have key : ∀ w : V, (r : K) * Q w + QuadraticMap.polar Q w a'
      = (r : K) * Q (w + (r : K)⁻¹ • a') + (-((r : K)⁻¹ * Q a')) := by
    intro w
    have h1 : Q (w + (r : K)⁻¹ • a')
        = QuadraticMap.polar Q w ((r : K)⁻¹ • a') + Q w + Q ((r : K)⁻¹ • a') := by
      simp only [QuadraticMap.polar]; ring
    rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]; field_simp; ring
  calc (∑ w : V, ψ ((r : K) * Q w + QuadraticMap.polar Q w a'))
      = ∑ w : V, ψ ((r : K) * Q (w + (r : K)⁻¹ • a') + (-((r : K)⁻¹ * Q a'))) :=
        Finset.sum_congr rfl (fun w _ => by rw [key w])
    _ = ∑ w : V, ψ (-((r : K)⁻¹ * Q a')) * ψ ((r : K) * Q (w + (r : K)⁻¹ • a')) :=
        Finset.sum_congr rfl (fun w _ => by rw [AddChar.map_add_eq_mul, mul_comm])
    _ = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q (w + (r : K)⁻¹ • a')) := by
        rw [Finset.mul_sum]
    _ = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q w) := by
        congr 1
        exact Equiv.sum_comp (Equiv.addRight ((r : K)⁻¹ • a')) (fun w => ψ ((r : K) * Q w))

/-- **Brick A2 — two-condition solution count as a character sum.** Generalizes Brick A: the number of
common solutions of `f x = c` and `g x = d`, scaled by `q²`, equals `∑_x (∑_r ψ(r(f x−c)))·(∑_s ψ(s(g x−d)))`.
This is the entry point for the hyperplane-section count `#{w : Q w = 0 ∧ polar Q w a = c}` (Brick D),
whose inner sum then evaluates via Brick D1. -/
theorem count2_eq_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] (f g : V → F) (c d : F) :
    (∑ x : V, (∑ r : F, ψ (r * (f x - c))) * (∑ s : F, ψ (s * (g x - d))))
      = ((univ.filter (fun x : V => f x = c ∧ g x = d)).card : R')
        * ((Fintype.card F : R') * (Fintype.card F : R')) := by
  have hinner : ∀ x : V, (∑ r : F, ψ (r * (f x - c))) * (∑ s : F, ψ (s * (g x - d)))
      = if (f x = c ∧ g x = d) then (Fintype.card F : R') * (Fintype.card F : R') else 0 := by
    intro x
    rw [AddChar.sum_mulShift (f x - c) hψ, AddChar.sum_mulShift (g x - d) hψ]
    simp only [sub_eq_zero]
    split_ifs with h1 h2 h2 <;> simp_all
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

#print axioms count_eq_charsum
#print axioms sum_quadForm_eval
#print axioms sum_addChar_quadForm_smul
#print axioms card_quadForm_eq
#print axioms sum_addChar_quadForm_linear
#print axioms count2_eq_charsum

-- ============== multi-point quadratic sum (toward the symmetry-broken-base count) ==============

/-- The quadratic "difference" identity (parallelogram form): `Q(a−b) = Q a + Q b − polar Q a b`. -/
theorem quad_sub {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a b : V) :
    Q (a - b) = Q a + Q b - QuadraticMap.polar Q a b := by
  have h1 : QuadraticMap.polar Q a (-b) = Q (a - b) - Q a - Q b := by
    simp only [QuadraticMap.polar, ← sub_eq_add_neg, QuadraticMap.map_neg]
  have h2 : QuadraticMap.polar Q a (-b) = - QuadraticMap.polar Q a b := by
    rw [← neg_one_smul K b, QuadraticMap.polar_smul_right, neg_one_smul]
  rw [h2] at h1; linear_combination -h1

/-- `polar Q z ·` is additive over a finite sum in its second argument (via `polarBilin`). -/
theorem polar_sum_right {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (z : V) {ι : Type*} (s : Finset ι) (r : ι → K) (t : ι → V) :
    (∑ j ∈ s, r j * QuadraticMap.polar Q z (t j))
      = QuadraticMap.polar Q z (∑ j ∈ s, r j • t j) := by
  have hb : ∀ y, QuadraticMap.polar Q z y = Q.polarBilin z y :=
    fun y => (QuadraticMap.polarBilin_apply_apply Q z y).symm
  rw [hb, map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [hb, map_smul, smul_eq_mul])

/-- **Multi-point quadratic Gauss sum (generalizes D1).** For weights `r` summing to `R ≠ 0`,
`∑_z ψ(∑ⱼ rⱼ·Q(z−tⱼ)) = ψ(∑ⱼ rⱼ·Q(tⱼ) − R⁻¹·Q(∑ⱼ rⱼ•tⱼ))·∑_z ψ(R·Q z)`. The summand expands to
`R·Q z − polar Q z (∑rⱼ•tⱼ) + const`, collapsing to D1. THE engine for the multi-point count at a
symmetry-broken base. -/
theorem sum_addChar_multiQuad {K : Type*} [Field K] {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V)
    {ι : Type*} (s : Finset ι) (r : ι → K) (t : ι → V) (hR : (∑ j ∈ s, r j) ≠ 0) :
    (∑ z : V, ψ (∑ j ∈ s, r j * Q (z - t j)))
      = ψ ((∑ j ∈ s, r j * Q (t j)) - (∑ j ∈ s, r j)⁻¹ * Q (∑ j ∈ s, r j • t j))
        * ∑ z : V, ψ ((∑ j ∈ s, r j) * Q z) := by
  have key : ∀ z : V, (∑ j ∈ s, r j * Q (z - t j))
      = (∑ j ∈ s, r j) * Q z + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))
        + (∑ j ∈ s, r j * Q (t j)) := by
    intro z
    have e : ∀ j ∈ s, r j * Q (z - t j)
        = r j * Q z + r j * Q (t j) - r j * QuadraticMap.polar Q z (t j) := by
      intro j _; rw [quad_sub]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        polar_sum_right,
        show QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))
            = - QuadraticMap.polar Q z (∑ j ∈ s, r j • t j) by
          rw [← neg_one_smul K (∑ j ∈ s, r j • t j), QuadraticMap.polar_smul_right, neg_one_smul]]
    ring
  rw [Finset.sum_congr rfl (fun z _ => by rw [key z])]
  have hD1 := sum_addChar_quadForm_linear ψ Q (Units.mk0 (∑ j ∈ s, r j) hR)
    (-(∑ j ∈ s, r j • t j))
  rw [Units.val_mk0] at hD1
  have hfactor : (∑ z : V, ψ ((∑ j ∈ s, r j) * Q z
        + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j)) + (∑ j ∈ s, r j * Q (t j))))
      = ψ (∑ j ∈ s, r j * Q (t j))
        * ∑ z : V, ψ ((∑ j ∈ s, r j) * Q z
            + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by rw [AddChar.map_add_eq_mul]; ring)
  rw [hfactor, hD1, QuadraticMap.map_neg, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2; ring

#print axioms quad_sub
#print axioms polar_sum_right
#print axioms sum_addChar_multiQuad
