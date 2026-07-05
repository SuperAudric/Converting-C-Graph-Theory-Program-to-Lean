/-
# Route C — L4: the node-4 discharge for the affine-polar family, WITHOUT the open `hFormCert`.

The abstract node-4 hook `reachesRigidOrCameron_viaAffineFormScheme` (`CascadeAffine.lean`) concludes the seal for a
schurian residue `S` from a **free group base** + the **open** certificate `hFormCert : RelCountsDetermineOrbit S T`
— the "only open content", the node-4 stall. That certificate is a `CellsAreOrbits`-style predicate, which §9.0a of
the Route-C plan establishes is **false at bounded/poly base** for the coarse forms graph (cells ⊋ orbits). Route C
does **not** discharge `hFormCert`; it supplies the **alternative** seal path that bypasses it entirely:

  pair-route separation (`exists_isotropySeparatesAtBaseK`, discharged)  →  `IsotropySeparatesAtBase` (via the
  `affineE` bridge `isotropySeparatesAtBase_of_K`)  →  `SeparatesAtBoundedBase` on the concrete `affineScheme(Q)`  →
  transport to the abstract residue `S` along the realizing iso (`separatesAtBoundedBase_transport`, L1)  →
  `reachesRigidOrCameron_viaSpielman` (the sub-exp floor).

**What this module delivers (L4).** `reachesRigidOrCameron_viaAffineFormScheme_routeC` — the affine-polar node-4
residue reaches the **same** seal disjunction as `viaAffineFormScheme`, from the *classification* (`S ≅` the standard
`VO^ε` similitude scheme via a realizing permutation) + the pair-route *scope* (`q = p` odd, `q` large, `Q`
nondegenerate) — and carries **NO `hFormCert`** and **NO carried `IsotropySeparatesAtBase`** (both discharged
internally). So for the affine-polar family the abstract hook's "only open content" is retired: the separation is
*proved*, not assumed. This is L4 of the Route-C plan §9.1 — it turns the four island seals into the affine-polar
node-4 case actually discharged (the poly-ness itself stays the project's meta-claim, §9.0a — this Lean object is the
quasipoly/sub-exp seal on the discharged classification).

NB the residual carried content is the **classification** (`SchemeRealizes f S (affineScheme(similitudeGroup Q))`, the
Skresanov/Cameron/Liebeck citation that the residue *is* this family) + the pair-route scope + `{G3}` — exactly the
carried premises of the banked `reachesRigidOrCameron_affinePolar`, now transported to the abstract residue.
-/
import ChainDescent.AffinePolarSeal
import ChainDescent.RouteCFormAdapters
import ChainDescent.RouteCSeam

namespace ChainDescent

open scoped Classical

variable {p d : ℕ} [Fact p.Prime]

open QuadraticMap in
/-- **L4 — the affine-polar node-4 discharge via Route C (no `hFormCert`).** The abstract residue `S` reaches the
seal disjunction (the conclusion of `reachesRigidOrCameron_viaAffineFormScheme`) given: it is Cameron, or it is
realized (`SchemeRealizes f S`, a relation-preserving bijection) by the standard `VO^ε` similitude scheme
`affineScheme (similitudeGroup Q)` for a `Q` in the pair-route scope (`p ≠ 2`, `Even d`, `d ≥ 2`, `Q` nondegenerate,
`q = p` large). The separation certificate is **discharged** internally by the pair route
(`exists_isotropySeparatesAtBaseK`) and transported to `S` (`separatesAtBoundedBase_transport`), then sealed via
`viaSpielman` — so **no `RelCountsDetermineOrbit`/`hFormCert` is carried**. Same conclusion type as the abstract hook;
supersedes it for this family. -/
theorem reachesRigidOrCameron_viaAffineFormScheme_routeC
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme (p ^ d))
    (hbound : 128 * (Nat.log 2 (Fintype.card (Fin d → ZMod p) ^ 2) + 1) ≤ bound)
    (hclass : IsCameronScheme (p ^ d) S ∨
      ∃ (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (f : Equiv.Perm (Fin (p ^ d))),
        p ≠ 2 ∧ Even d ∧ 2 ≤ d ∧
        (∃ ψ : AddChar (ZMod p) ℂ, ψ.IsPrimitive) ∧
        polarRad Q = ⊥ ∧ Q.polarBilin.Nondegenerate ∧
        64 * (Fintype.card (ZMod p) : ℝ) ^ 2 ≤ Fintype.card (Fin d → ZMod p) ∧
        64 * (d : ℝ) ^ 2 ≤ Fintype.card (ZMod p) ∧
        256 ≤ (Fintype.card (ZMod p) : ℝ) ∧
        32 * (2 * d + 4) ≤ Fintype.card (ZMod p) ∧
        64 < Fintype.card (Fin d → ZMod p) ∧
        SchemeRealizes f S (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))) :
    ((SchemeBlockRecovered (p ^ d) S ∨ AbelianConsumed (p ^ d) S)
        ∨ SchemeRecoveredByDepth (p ^ d) S bound)
      ∨ IsCameronScheme (p ^ d) S := by
  rcases hclass with hcam | ⟨Q, f, hp2, hd, hdge, ⟨ψ, hψ⟩, hQrad, hQnd,
      hq1, hq2, hq3, hqthr, hNthr, hreal⟩
  · exact Or.inr hcam
  · -- discharge the pair-route separation certificate for the standard VO^ε form
    have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    haveI : Invertible (2 : ZMod p) := invertibleOfNonzero (Ring.two_ne_zero hF)
    obtain ⟨T₀, hT₀card, hK⟩ :=
      exists_isotropySeparatesAtBaseK Q hF hd hdge hψ hQrad hQnd hq1 hq2 hq3 hqthr hNthr
    -- relabel the V-indexed base through `affineE` to the `Fin (p^d)`-indexed one
    have himg : (T₀.image affineE).image affineE.symm = T₀ := by
      rw [Finset.image_image,
        show (affineE.symm ∘ affineE) = id from funext (fun x => affineE.symm_apply_apply x),
        Finset.image_id]
    have hTcard : (T₀.image affineE).card ≤ bound :=
      le_trans (le_trans Finset.card_image_le hT₀card) hbound
    have hIso : IsotropySeparatesAtBase Q (T₀.image affineE) :=
      isotropySeparatesAtBase_of_K Q (by rw [himg]; exact hK)
    -- transport the (light) separation to `S` and seal — no `hFormCert`
    exact reachesRigidOrCameron_viaSchurianRank3Affine_proved S
      (Or.inr ⟨Q, T₀.image affineE, f, hTcard, hIso, hreal⟩)

/-! ## Track B — the multi-form meta poly-support (finer→coarser, adapter-driven)

For families with a discharged **coarse** separation (only affine-polar, via the pair route) L4 produces a genuine
coarse `SealDisj` on the abstract residue (`reachesRigidOrCameron_viaAffineFormScheme_routeC` above). The multi-form
families (alternating / half-spin / Suzuki) lack that coarse discretization (it would be a multi-quadric pair-route,
deferred). What they *can* deliver now is the **§9.0a meta-composition** — the honest Route-C support object that
canonizes the coarse graph without a coarse `SealDisj`: the recovered-form (fine) harvest + the group-pinning of the
coarse Aut + the fine⟶coarse refinement. This is the multi-form sibling of `routeC_polySupport`, and it is now
*self-contained* (the fine harvest is **extracted** from the adapter, not carried as a hypothesis — the improvement
`schemeRecoveredByDepth_of_separatesAtBoundedBase` on the adapter's own `SeparatesAtBoundedBase` witness affords).
-/

open RouteC in
/-- **Track B engine — Route-C poly-support from any `FormAdapter` + a coarse over-group.** Given an adapter `A`
(the recovered fine structure `G₀`, discretizing at a bounded base) and any coarse group `Gc ≥ A.G₀` (`∋ −1`) —
for the forms graphs `Gc = jointConeStab`/`similitudeGroup`, the *graph-intrinsic* group — modulo the named
Skresanov 2-closure citation `AffineSchemeTwoClosed hnegc`, the honest poly-support triple holds:
  (i)  `SchemeAutGroup(affineScheme Gc) = affineG Gc` — the coarse graph's Aut group is the known classical affine group;
  (ii) `SchemeRecoveredByDepth (affineScheme A.G₀) bound` — the recovered fine scheme's genuine bounded-depth harvest,
       **extracted from the adapter** (no carried hypothesis, unlike `routeC_polySupport`);
  (iii)`SchemeAutGroup(affineScheme A.G₀) ≤ SchemeAutGroup(affineScheme Gc)` — the recovered form only refines.
Together with brick-1 + F4 this is the full structural support for the **meta** poly-canonization of the coarse graph
(§9.0a). One engine, all families (affine-polar / alternating / half-spin / Suzuki) via their adapter + coarse group. -/
theorem routeC_polySupport_of_adapter {bound : ℕ} (A : FormAdapter (p := p) (d := d) bound)
    (Gc : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hle : A.G₀ ≤ Gc) (hnegc : LinearEquiv.neg (ZMod p) ∈ Gc)
    (h2c : AffineSchemeTwoClosed hnegc) :
    (affineScheme Gc hnegc).toAssociationScheme.SchemeAutGroup = affineG Gc
      ∧ SchemeRecoveredByDepth (p ^ d) (affineScheme A.G₀ A.neg_mem) bound
      ∧ (affineScheme A.G₀ A.neg_mem).toAssociationScheme.SchemeAutGroup
          ≤ (affineScheme Gc hnegc).toAssociationScheme.SchemeAutGroup :=
  ⟨schemeAutGroup_affineScheme_eq_affineG hnegc h2c,
   schemeRecoveredByDepth_of_separatesAtBoundedBase _
     ⟨A.base, A.base_card_le, discrete_affineScheme_of_jointSeparates A.G₀ A.neg_mem A.separates⟩,
   schemeAutGroup_affineScheme_mono hle A.neg_mem hnegc⟩

open RouteC in
/-- **Track B — alternating `Alt(5,q)`.** The `routeC_polySupport` triple for the Plücker family: coarse Aut =
`affineG(jointConeStab pluckerForms)` (mod Skresanov), fine harvest extracted from `alternatingAdapter`, fine ≤ coarse.
Retires the island status of `reachesRigidOrCameron_alternating` at the §9.0a meta level. -/
theorem routeC_polySupport_alternating {p : ℕ} [Fact p.Prime]
    (h2c : AffineSchemeTwoClosed (neg_mem_jointConeStab (Plucker.pluckerForms (p := p)))) :
    (affineScheme (jointConeStab (Plucker.pluckerForms (p := p)))
          (neg_mem_jointConeStab (Plucker.pluckerForms (p := p)))).toAssociationScheme.SchemeAutGroup
        = affineG (jointConeStab (Plucker.pluckerForms (p := p)))
      ∧ SchemeRecoveredByDepth (p ^ 10)
          (affineScheme (Plucker.alternatingAdapter (p := p)).G₀
            (Plucker.alternatingAdapter (p := p)).neg_mem) (10 + 1)
      ∧ (affineScheme (Plucker.alternatingAdapter (p := p)).G₀
            (Plucker.alternatingAdapter (p := p)).neg_mem).toAssociationScheme.SchemeAutGroup
          ≤ (affineScheme (jointConeStab (Plucker.pluckerForms (p := p)))
              (neg_mem_jointConeStab (Plucker.pluckerForms (p := p)))).toAssociationScheme.SchemeAutGroup :=
  routeC_polySupport_of_adapter (Plucker.alternatingAdapter (p := p))
    (jointConeStab (Plucker.pluckerForms (p := p)))
    (iInf_isometryGroup_le_jointConeStab (Plucker.pluckerForms (p := p)))
    (neg_mem_jointConeStab (Plucker.pluckerForms (p := p))) h2c

open RouteC in
/-- **Track B — half-spin.** The `routeC_polySupport` triple for the D₅ spinor family: coarse Aut =
`affineG(jointConeStab spinorForms)` (mod Skresanov), fine harvest extracted from `spinAdapter`, fine ≤ coarse. -/
theorem routeC_polySupport_halfSpin {p : ℕ} [Fact p.Prime]
    (h2c : AffineSchemeTwoClosed (neg_mem_jointConeStab (HalfSpin.spinorForms (p := p)))) :
    (affineScheme (jointConeStab (HalfSpin.spinorForms (p := p)))
          (neg_mem_jointConeStab (HalfSpin.spinorForms (p := p)))).toAssociationScheme.SchemeAutGroup
        = affineG (jointConeStab (HalfSpin.spinorForms (p := p)))
      ∧ SchemeRecoveredByDepth (p ^ 16)
          (affineScheme (HalfSpin.spinAdapter (p := p)).G₀
            (HalfSpin.spinAdapter (p := p)).neg_mem) (16 + 1)
      ∧ (affineScheme (HalfSpin.spinAdapter (p := p)).G₀
            (HalfSpin.spinAdapter (p := p)).neg_mem).toAssociationScheme.SchemeAutGroup
          ≤ (affineScheme (jointConeStab (HalfSpin.spinorForms (p := p)))
              (neg_mem_jointConeStab (HalfSpin.spinorForms (p := p)))).toAssociationScheme.SchemeAutGroup :=
  routeC_polySupport_of_adapter (HalfSpin.spinAdapter (p := p))
    (jointConeStab (HalfSpin.spinorForms (p := p)))
    (iInf_isometryGroup_le_jointConeStab (HalfSpin.spinorForms (p := p)))
    (neg_mem_jointConeStab (HalfSpin.spinorForms (p := p))) h2c

/-! ### Suzuki — the `formConeStab` generalization (the ovoid cone is CUBIC, not quadric-cut)

The Suzuki family's connection set is the joint zero of the 5 **σ-twisted cubic** forms `SFbar` — not quadratic, so
`jointConeStab` (typed for `QuadraticForm` families) does not apply. `formConeStab` is the same graph-intrinsic
construction for an *arbitrary* form family `Fs : V → ι → K'`: the setwise stabilizer of the joint zero cone. The
generic Track-B engine `routeC_polySupport_of_adapter` accepts it as the coarse group `Gc` unchanged. -/

/-- **The cone stabilizer of an arbitrary (not necessarily quadratic) form family.** The setwise stabilizer of the
joint zero locus `{v | ∀ k, Fs v k = 0}` — the graph-intrinsic coarse group for any forms graph, quadratic or not.
`jointConeStab` is the `QuadraticForm` special case; `formConeStab (SFbar)` is the Suzuki (cubic) case. -/
def formConeStab {D : ℕ} {ι : Type*} {K' : Type*} [Zero K']
    (Fs : (Fin D → ZMod 2) → ι → K') :
    Subgroup ((Fin D → ZMod 2) ≃ₗ[ZMod 2] (Fin D → ZMod 2)) where
  carrier := {g | ∀ v, (∀ k, Fs (g v) k = 0) ↔ (∀ k, Fs v k = 0)}
  one_mem' := by intro v; rfl
  mul_mem' := by intro a b ha hb v; rw [LinearEquiv.mul_apply, ha (b v), hb v]
  inv_mem' := by
    intro a ha v
    have hav : a (a⁻¹ v) = v := by
      have h := LinearEquiv.mul_apply a a⁻¹ v
      rw [mul_inv_cancel] at h; simpa using h.symm
    have := ha (a⁻¹ v)
    rw [hav] at this
    exact this.symm

section Suzuki
variable {K : Type*} [CommRing K] [CharP K 2] (σ : K →+* K)
  {D : ℕ} (Ψ : (Fin D → ZMod 2) ≃+ (Fin 4 → K))

omit [CharP K 2] in
/-- **The Suzuki fine ⟶ coarse bridge.** A `g` preserving every σ-twisted form value (`g ∈ suzukiG₀`) certainly
preserves the ovoid cone setwise, so `suzukiG₀ ≤ formConeStab (SFbar)` — the cubic analog of
`iInf_isometryGroup_le_jointConeStab`. -/
theorem suzukiG₀_le_formConeStab :
    RouteC.Suzuki.suzukiG₀ σ Ψ ≤ formConeStab (RouteC.Suzuki.SFbar σ Ψ) := by
  intro g hg v
  constructor
  · intro h k; rw [← hg v k]; exact h k
  · intro h k; rw [hg v k]; exact h k

open RouteC in
/-- **Track B — Suzuki–Tits.** The `routeC_polySupport` triple for the σ-twisted ovoid family, via the cubic
`formConeStab (SFbar)` as the coarse group (mod Skresanov). Completes the multi-form set: fine harvest extracted
from `suzukiAdapter`, coarse Aut pinned, fine ≤ coarse. -/
theorem routeC_polySupport_suzuki
    (h2c : AffineSchemeTwoClosed
      (suzukiG₀_le_formConeStab σ Ψ (RouteC.Suzuki.neg_mem_suzukiG₀ σ Ψ))) :
    (affineScheme (formConeStab (RouteC.Suzuki.SFbar σ Ψ))
          (suzukiG₀_le_formConeStab σ Ψ
            (RouteC.Suzuki.neg_mem_suzukiG₀ σ Ψ))).toAssociationScheme.SchemeAutGroup
        = affineG (formConeStab (RouteC.Suzuki.SFbar σ Ψ))
      ∧ SchemeRecoveredByDepth (2 ^ D)
          (affineScheme (RouteC.Suzuki.suzukiAdapter σ Ψ).G₀
            (RouteC.Suzuki.suzukiAdapter σ Ψ).neg_mem) 8
      ∧ (affineScheme (RouteC.Suzuki.suzukiAdapter σ Ψ).G₀
            (RouteC.Suzuki.suzukiAdapter σ Ψ).neg_mem).toAssociationScheme.SchemeAutGroup
          ≤ (affineScheme (formConeStab (RouteC.Suzuki.SFbar σ Ψ))
              (suzukiG₀_le_formConeStab σ Ψ
                (RouteC.Suzuki.neg_mem_suzukiG₀ σ Ψ))).toAssociationScheme.SchemeAutGroup :=
  routeC_polySupport_of_adapter (RouteC.Suzuki.suzukiAdapter σ Ψ)
    (formConeStab (RouteC.Suzuki.SFbar σ Ψ))
    (suzukiG₀_le_formConeStab σ Ψ)
    (suzukiG₀_le_formConeStab σ Ψ (RouteC.Suzuki.neg_mem_suzukiG₀ σ Ψ)) h2c

end Suzuki

end ChainDescent
