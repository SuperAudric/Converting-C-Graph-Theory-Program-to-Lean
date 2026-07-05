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

end ChainDescent
