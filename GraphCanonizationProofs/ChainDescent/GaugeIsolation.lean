import ChainDescent.GaugeComplex
import Mathlib.GroupTheory.Perm.Basic

/-!
# W2 Tier B — C3 `Recover`, piece R-a: gauge isolation in the rigid regime

Planning doc: `docs/chain-descent-w2-solvability-route.md` §5a (C3 `Recover` scope), §5 (Tier B).

R-a is the **isolation** step of `Recover`: identify the gauge cells, excluding the base symmetry
(the `mp7 → Z₂³`, not `|Aut| = 1344`, test). Closer analysis **refines** the scope: the hard
"gauge vs. base classifier on the full graph" is **not** what force needs. Force sees the residue
*after* the interleaving's **consume** half has peeled off the visible base symmetry — i.e. a
**rigid** residue. In the rigid regime the isolation is automatic:

* `sameOrbit_iff_eq_of_rigid` — with `Aut = 1`, `SameOrbit` collapses to equality;
* `holonomyNontrivial_iff_flat_ne_of_rigid` — so nontrivial holonomy is exactly a locally-flat pair
  of **distinct** vertices, and the **gauge cells are the non-singleton flatness classes**, with no
  base to separate out (`carriesGauge_iff_exists_holonomy_of_rigid`).

⟹ the `mp7 → Z₂³` gauge/base split is achieved by the **two-seals interleaving** (consume takes the
non-solvable base `PGL(3,2)`; force sees the rigid `Z₂³` residue), **not** by a Recover-internal
classifier. This is the clean, provable form of R-a, and it explains why the deferred extraction-free
C2 fibre-isolation is unnecessary for force: rigidity does the isolating.
-/

namespace ChainDescent
namespace GaugeComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The identity permutation is a colour-automorphism. -/
theorem isColAut_one (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) :
    IsColAut adj P χ 1 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **The rigid regime**: the only colour-automorphism is the identity (`Aut = 1`). This is the
state of the residue FORCE sees — after the interleaving's consume half has peeled off the visible
base symmetry. -/
def IsRigid (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) : Prop :=
  ∀ σ : Equiv.Perm V, IsColAut adj P χ σ → σ = 1

variable {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}

/-- In the rigid regime `SameOrbit` collapses to equality: no nontrivial automorphism moves a
vertex, so two vertices share an orbit iff they are equal. -/
theorem sameOrbit_iff_eq_of_rigid (hrig : IsRigid adj P χ) (u v : V) :
    SameOrbit adj P χ u v ↔ u = v := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [hrig σ hσ, Equiv.Perm.one_apply]
  · rintro rfl
    exact ⟨1, isColAut_one adj P χ, Equiv.Perm.one_apply u⟩

/-- **Isolation in the rigid regime (R-a).** After consume peels the base (leaving a rigid residue),
nontrivial holonomy is exactly a locally-flat pair of DISTINCT vertices. So the gauge cells are the
non-singleton flatness classes, with no base symmetry to separate out — the gauge/base split
(`mp7 → Z₂³`, not 1344) is done by the two-seals interleaving, not by a Recover-internal classifier. -/
theorem holonomyNontrivial_iff_flat_ne_of_rigid (hrig : IsRigid adj P χ) (u v : V) :
    HolonomyNontrivial adj P χ u v ↔ (LocallyFlat adj P χ u v ∧ u ≠ v) := by
  unfold HolonomyNontrivial
  rw [sameOrbit_iff_eq_of_rigid hrig]

/-- A vertex **carries gauge freedom** if its flatness class is non-singleton — it has a distinct
locally-flat partner. -/
def CarriesGauge (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (v : V) : Prop :=
  ∃ w : V, w ≠ v ∧ LocallyFlat adj P χ v w

/-- **The gauge cells ARE the holonomy support, in the rigid regime.** A vertex carries gauge
freedom iff it has a holonomy-nontrivial partner — the clean R-a statement that isolation is
automatic once rigid. -/
theorem carriesGauge_iff_exists_holonomy_of_rigid (hrig : IsRigid adj P χ) (v : V) :
    CarriesGauge adj P χ v ↔ ∃ w, HolonomyNontrivial adj P χ v w := by
  unfold CarriesGauge
  constructor
  · rintro ⟨w, hw, hflat⟩
    exact ⟨w, (holonomyNontrivial_iff_flat_ne_of_rigid hrig v w).mpr ⟨hflat, fun h => hw h.symm⟩⟩
  · rintro ⟨w, hhol⟩
    obtain ⟨hflat, hne⟩ := (holonomyNontrivial_iff_flat_ne_of_rigid hrig v w).mp hhol
    exact ⟨w, fun h => hne h.symm, hflat⟩

--#print axioms sameOrbit_iff_eq_of_rigid
--#print axioms holonomyNontrivial_iff_flat_ne_of_rigid
--#print axioms carriesGauge_iff_exists_holonomy_of_rigid

end GaugeComplex
end ChainDescent
