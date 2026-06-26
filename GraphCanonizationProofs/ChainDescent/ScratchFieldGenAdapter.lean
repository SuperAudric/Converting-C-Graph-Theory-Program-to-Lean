/-
# Concern #4 — the q = p adapter: the abstract-K analytic chain reaches the in-build capstone

`ScratchFieldGen.lean` lifts the analytic count chain to an abstract finite field `K` with `V = Fin d → K` indexed
directly (no `affineE`). This module closes the loop for the **prime-field** case `q = p` (`K = ZMod p`): it shows the
V-indexed `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` implies the build's `Fin (p^d)`-indexed
`IsotropySeparatesAtBase Q T` (a pure `affineE` relabel — the digit encoding is the *only* difference), and hence the
abstract predicate feeds the existing seal capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree`.

So `affineE` is confirmed to be exactly "a single endpoint conversion at the scheme seam": the analytic content lives
over abstract `K`/`V`, and only this thin relabel connects it to the `Fin (p^d)` scheme machinery. (The `q = pᵉ`
adapter — `efield : GaloisField p e ≃ₗ F_p^{de}` — is the separate Layer-D seam.)

Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build (PORT is a follow-up).
-/
import ChainDescent.ScratchFieldGen
import ChainDescent.CascadeAffine

namespace ChainDescent

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

/-- The V-indexed `isoClassK` (abstract `K`, here `K = ZMod p`) agrees with the build's `Fin (p^d)`-flavoured
`isoClass` on the vector space — both are `if w = 0 then 0 else if Q w = 0 then 1 else 2`. -/
theorem isoClassK_eq_isoClass (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (w : Fin d → ZMod p) :
    isoClassK Q w = isoClass Q w := by
  rcases eq_or_ne w 0 with h1 | h1
  · rw [(isoClassK_eq_zero_iff Q w).2 h1, (isoClass_eq_zero_iff Q w).2 h1]
  · rcases eq_or_ne (Q w) 0 with h2 | h2
    · rw [(isoClassK_eq_one_iff Q w).2 ⟨h1, h2⟩, (isoClass_eq_one_iff Q w).2 ⟨h1, h2⟩]
    · rw [(isoClassK_eq_two_iff Q w).2 h2, (isoClass_eq_two_iff Q w).2 h2]

open scoped Classical in
/-- **The relabel.** For a single pivot `w : Fin (p^d)`, the V-indexed isotropy-profile count (at base
`T.image affineE.symm`, profile `σV`, pivot class `c`) equals the build's `Fin (p^d)`-indexed count (at base `T`,
profile `σV ∘ affineE.symm`, pivot class `c`), via the bijection `affineE`. -/
theorem isoCount_transport
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (σV : (Fin d → ZMod p) → Fin 3) (c : Fin 3) (w : Fin (p ^ d)) :
    (Finset.univ.filter (fun y : Fin d → ZMod p => y ≠ affineE.symm w ∧
      (∀ t ∈ T.image affineE.symm, isoClassK Q (y - t) = σV t) ∧
      isoClassK Q (y - affineE.symm w) = c)).card
    = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
      (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σV (affineE.symm t)) ∧
      isoClass Q (affineE.symm z - affineE.symm w) = c)).card := by
  refine Finset.card_nbij' (fun y => affineE y) (fun z => affineE.symm z) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, hne, hprof, hc⟩ := hy
    refine ⟨Finset.mem_univ _, fun h => hne (by rw [← h, Equiv.symm_apply_apply]), fun t ht => ?_, ?_⟩
    · rw [Equiv.symm_apply_apply, ← isoClassK_eq_isoClass]
      exact hprof (affineE.symm t) (Finset.mem_image_of_mem _ ht)
    · rw [Equiv.symm_apply_apply, ← isoClassK_eq_isoClass]; exact hc
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, hne, hprof, hc⟩ := hz
    refine ⟨Finset.mem_univ _, fun h => hne (affineE.symm.injective h), fun tv htv => ?_, ?_⟩
    · rw [Finset.mem_image] at htv
      obtain ⟨t, ht, rfl⟩ := htv
      rw [isoClassK_eq_isoClass]; exact hprof t ht
    · rw [isoClassK_eq_isoClass]; exact hc
  · intro y _; exact affineE.symm_apply_apply y
  · intro z _; exact affineE.apply_symm_apply z

/-- **The q = p adapter.** `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` (the abstract-K, V-indexed predicate
of `ScratchFieldGen`) ⟹ `IsotropySeparatesAtBase Q T` (the build's `Fin (p^d)`-indexed predicate). Pure relabel:
descend to `V` via `affineE.symm.injective`, transport the count agreement with `isoCount_transport`, and feed the
profile `σ = σV ∘ affineE.symm`. -/
theorem isotropySeparatesAtBase_of_K
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (hK : IsotropySeparatesAtBaseK Q (T.image affineE.symm)) :
    IsotropySeparatesAtBase Q T := by
  intro u u' hcounts
  apply affineE.symm.injective
  apply hK (affineE.symm u) (affineE.symm u')
  intro σV c
  rw [isoCount_transport Q σV c u, isoCount_transport Q σV c u']
  exact hcounts (fun x => σV (affineE.symm x)) c

/-- **The abstract-K predicate reaches the capstone (q = p).** Composing the adapter with the build's Witt-free seal
capstone: `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` at a bounded base seals the `VO^ε` residue modulo
`{G3}` — no Witt, no `hSmallAutThin`. Confirms the abstract analytic chain subsumes the prime-field result. -/
theorem reachesRigidOrCameron_viaIsotropySeparatesK_wittFree
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (hcard : T.card ≤ bound)
    (hK : IsotropySeparatesAtBaseK Q (T.image affineE.symm)) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))
        ∨ AbelianConsumed (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)))
        ∨ SchemeRecoveredByDepth (p ^ d)
            (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) :=
  reachesRigidOrCameron_viaIsotropySeparates_wittFree Q T hcard (isotropySeparatesAtBase_of_K Q hK)

end ChainDescent

#print axioms ChainDescent.isoClassK_eq_isoClass
#print axioms ChainDescent.isoCount_transport
#print axioms ChainDescent.isotropySeparatesAtBase_of_K
#print axioms ChainDescent.reachesRigidOrCameron_viaIsotropySeparatesK_wittFree
