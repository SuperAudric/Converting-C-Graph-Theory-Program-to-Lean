/-
# Route A, Step C — the counting sub-step: the per-round separator + the accumulation kernel

**What this module builds (recovery doc §9.7, Route α first sub-step).** Step C reduces (via `ScratchPlanePin`) to
"1-WL-stable refines `zSet`", which the 2-dim reframe turns into: pin the plane points of `W ≅ K²` by their
complement-factored count-profiles. This module lands the **per-round separator** — confirming the seal's landed pair
lever (`AffinePolarSeal.jointIsoCountK_ne_of_sep`) applies verbatim to plane-point pinning — and **isolates the
accumulation** as one clean predicate.

* `plane_count_sep` — two plane points `w, w'` whose `χ(pairForm)` to a base pair `{t, t₀}` differ have **different**
  joint isotropy counts (the 2-round WL count separates them). This is the seal's per-pair separation, in the plane
  context. It confirms Route α's lever fires; each base pair contributes one `χ`-bit (Insight 1).
* `ChiProfileSeparatesPlane` — **the open accumulation kernel:** the `χ(pairForm)`-profile over base pairs *separates*
  the plane (distinct plane points differ in `χ` at some base pair). This is the `d`-independent 2-dim
  count-accumulation — the sole remaining route-A obligation. Combined with `plane_count_sep` it makes the joint-count
  profile injective on `W`, and (the counts being 1-WL-computable) 1-WL refines `zSet` ⟹ `bᵢ=1`.

**Honest status.** The per-round separator is landed (the lever fires for plane points). The kernel
`ChiProfileSeparatesPlane` is OPEN — it is the accumulation the probe measures at `r*∈{3,4}` rounds, the genuine Gauss
frontier (the seal's per-anchor + union assembly, at the plane level). The remaining wiring
"count-profile-injective-on-`W` ⟹ 1-WL refines `zSet`" needs a 1-WL-computability step (Route β territory), deferred.

Reuses `AffinePolarSeal.jointIsoCountK_ne_of_sep` (the seal's per-pair lever) + `FieldGeneric.jointIsoCountK`.
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.AffinePolarSeal

namespace ChainDescent.PlaneSep

open QuadraticMap

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-- **★ Route α per-round separator (the seal's lever, in the plane-pinning context).** Two plane points `w, w'` whose
`χ(pairForm)` to a base pair `{t, t₀}` differ have **different** joint isotropy counts `jointIsoCountK · {t, t₀}` — so
the 2-round WL count separates them. This is `jointIsoCountK_ne_of_sep` at `u, v := w, w'`, confirming the seal's
per-pair separation lever fires for plane-point pinning. Each base pair contributes one `χ`-bit (hence the accumulation
below is needed to reach the `Θ(log q)` bits pinning the plane — Insight 1). -/
theorem plane_count_sep (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (w w' t t₀ : Fin d → K)
    (hIw : pairForm Q (t₀ - w) (t - w) ≠ 0) (hIw' : pairForm Q (t₀ - w') (t - w') ≠ 0)
    (hQw : Q (t₀ - w) ≠ 0) (hQw' : Q (t₀ - w') ≠ 0)
    (hchi : quadraticChar K (pairForm Q (t₀ - w) (t - w))
          ≠ quadraticChar K (pairForm Q (t₀ - w') (t - w'))) :
    jointIsoCountK Q w {t, t₀} ≠ jointIsoCountK Q w' {t, t₀} :=
  ChainDescent.jointIsoCountK_ne_of_sep Q hF hcardK hd hψ vb hv hw w w' t t₀
    hIw hIw' hQw hQw' hchi

/-- **★ The Route α accumulation kernel (the open content).** The `χ(pairForm)`-profile of a plane point over base pairs
`{t, t₀} ⊆ S₀` **separates** the plane: any two distinct plane points differ in `χ(pairForm)` at some base pair (with
that pair nondegenerate at both, so `plane_count_sep` fires). This is the `d`-independent, 2-dimensional
count-accumulation — the sole remaining route-A obligation. Given it, `plane_count_sep` makes the joint-count profile
injective on `W`, and (the counts being 1-WL-computable from the individualised base) 1-WL refines `zSet` ⟹ `bᵢ = 1`.
The probe measures this at `r*∈{3,4}` rounds; the proof is the seal's per-anchor + union assembly, at the plane level. -/
def ChiProfileSeparatesPlane (Q : QuadraticForm K (Fin d → K)) (S₀ : Finset (Fin d → K))
    (W : Set (Fin d → K)) : Prop :=
  ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
    ∃ t ∈ S₀, ∃ t₀ ∈ S₀,
      (pairForm Q (t₀ - w) (t - w) ≠ 0 ∧ pairForm Q (t₀ - w') (t - w') ≠ 0
        ∧ Q (t₀ - w) ≠ 0 ∧ Q (t₀ - w') ≠ 0)
      ∧ quadraticChar K (pairForm Q (t₀ - w) (t - w))
          ≠ quadraticChar K (pairForm Q (t₀ - w') (t - w'))

/-- **★ Route α reduction — the accumulation kernel makes the joint-count profile separate the plane.** Given
`ChiProfileSeparatesPlane` and the seal's global data (even `d`, primitive `ψ`, anisotropic basis), distinct plane
points have **different joint-count profiles**: some base pair `{t, t₀}` witnesses `jointIsoCountK · {t,t₀}` differing.
So the 2-round joint-count observable is injective on `W` — the plane is pinned (modulo the 1-WL-computability of these
counts, the deferred final wiring). Reduces route A to the single open predicate `ChiProfileSeparatesPlane`. -/
theorem count_profile_separates_of_kernel (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    {S₀ : Finset (Fin d → K)} {W : Set (Fin d → K)}
    (hker : ChiProfileSeparatesPlane Q S₀ W)
    {w w' : Fin d → K} (hwW : w ∈ W) (hw'W : w' ∈ W) (hne : w ≠ w') :
    ∃ t ∈ S₀, ∃ t₀ ∈ S₀, jointIsoCountK Q w {t, t₀} ≠ jointIsoCountK Q w' {t, t₀} := by
  obtain ⟨t, htS, t₀, ht₀S, ⟨hIw, hIw', hQw, hQw'⟩, hchi⟩ := hker w hwW w' hw'W hne
  exact ⟨t, htS, t₀, ht₀S,
    plane_count_sep Q hF hcardK hd hψ vb hv hw w w' t t₀ hIw hIw' hQw hQw' hchi⟩

end ChainDescent.PlaneSep
