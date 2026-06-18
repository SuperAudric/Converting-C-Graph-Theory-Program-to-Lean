/-
# Forms-graph node-4 discharge (consumer module)

The `FormsGraph`-side consumer that discharges `IsotropySeparatesAtBase Q T` (CascadeAffine §OrthogonalForm) for the
rank-3 SRG `VO^ε` residue, by combining:
* the **Gauss-sum point-count toolkit** (`ChainDescent.GaussCount`) — the closed-form multi-point `Q`-count
  (`countk_eq_sum_charsum` + `multiQuad`/`multiQuad_zero`/`linearMap`) and the value-set inclusion–exclusion
  (`count_pi_setValued`);
* the **affine forms-graph substrate** (`ChainDescent.CascadeAffine`) — `affineScheme`, `affineE`, `isoClass` and
  the isotropy dictionary `isoClass_eq_*`, and the seal capstone `reachesRigidOrCameron_viaIsotropySeparates`.

Build order (the planned increments): (1) transport counts `Fin (p^d) ↔ V` along `affineE` — **landed below**;
(2) the isotropy-count → `Q`-value-set-count conversion (`count_pi_setValued` + the dictionary, with the single-point
origin correction); (3) the injectivity argument at a symmetry-broken base, proving `IsotropySeparatesAtBase Q T`
for `VO^ε_4(3)`, then feeding the capstone. All decls axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.CascadeAffine
import ChainDescent.GaussCount

namespace ChainDescent

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

/-- **Count transport `Fin (p^d) ↔ V` along `affineE`.** A vertex count over the affine point set `Fin (p^d)`,
with a predicate that factors through `affineE.symm` (the coordinate vector), equals the corresponding count over
the vector space `V = Fin d → ZMod p`. This moves the `IsotropySeparatesAtBase` counts — whose predicate is a
function of `affineE.symm z` (the difference relations `isoClass Q (affineE.symm z − affineE.symm t)`, and
`z ≠ u ↔ affineE.symm z ≠ affineE.symm u`) — into the vector space where the Gauss toolkit's point counts live.
Proved by the `affineE` bijection (`Finset.card_image_of_injective`). -/
theorem count_transport (P : (Fin d → ZMod p) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun z : Fin (p ^ d) => P (affineE.symm z))).card
      = (Finset.univ.filter (fun x : Fin d → ZMod p => P x)).card := by
  classical
  rw [← Finset.card_image_of_injective (Finset.univ.filter (fun x : Fin d → ZMod p => P x))
      affineE.injective]
  congr 1
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨affineE.symm z, hz, Equiv.apply_symm_apply _ _⟩
  · rintro ⟨x, hx, rfl⟩; rwa [Equiv.symm_apply_apply]

end ChainDescent
