import ChainDescent.GaugeComplex
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# W2 Tier B, step 1 — the bridge lemma

Planning doc: `docs/chain-descent-w2-solvability-route.md` §5 (Tier B) + §4a (Γ = C3).

Connects Tier A's completeness-clean holonomy (`GaugeComplex.HolonomyNontrivial`) to the
group-carrying **recovered gauge Γ** (C3). The concrete Γ (the structural `Recover` object) is
not yet built, so — following the rigid-seal idiom (state the reduction, carry the extraction) —
we:

1. state the abstract **`GaugeContract`** that `Recover` will satisfy: a group `carrier ≤ Sym V`
   whose ORBITS are exactly the local-flatness classes (`faithful` = the isolation-faithfulness
   the structural `Recover` discharges);
2. prove the **bridge** `holonomy_iff_gauge`: `HolonomyNontrivial u v ⟺ Γ-orbit u v ∧ ¬SameOrbit`;
3. exhibit a **consistency witness** `gaugeContractMax` proving the contract is inhabited (guards
   against a vacuous interface — the recurring failure mode).

⚠ **`faithful` pins the orbit PARTITION, not the group up to isomorphism.** The *solvability*-
relevant `carrier` is the structure-preserving **recovered** gauge (`Recover` pins it — a further
carried property). Do **not** read `IsSolvable carrier` off an arbitrary faithful witness:
`gaugeMax` below is faithful yet generally non-solvable (it is the full `∏ Sym(fiber)`). It
certifies the interface is satisfiable, nothing more (this matches `mp7`: the operative Γ is the
recovered `Z₂³`, not the max partition-stabilizer).
-/

namespace ChainDescent
namespace GaugeComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The abstract recovered-gauge contract (C3, §4a).** `carrier ≤ Sym V` is the gauge group;
`faithful` says its orbits are exactly the local-flatness classes — the isolation-faithfulness the
structural `Recover` discharges. Tier B is stated against this contract and carries it. -/
structure GaugeContract (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) where
  /-- The recovered gauge group, as a subgroup of the symmetric group. -/
  carrier : Subgroup (Equiv.Perm V)
  /-- Isolation faithfulness: the gauge orbits are exactly the local-flatness classes. -/
  faithful : ∀ u v, LocallyFlat adj P χ u v ↔ ∃ σ ∈ carrier, σ u = v

/-- Gauge-equivalence induced by a contract: `u, v` lie in the same Γ-orbit. -/
def GaugeContract.Equiv {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    (G : GaugeContract adj P χ) (u v : V) : Prop :=
  ∃ σ ∈ G.carrier, σ u = v

/-- **The bridge lemma (Tier B, step 1).** Given the recovered gauge Γ, holonomy-nontrivial =
gauge-linked but not globally sectioned: `HolonomyNontrivial u v ⟺ Γ-orbit u v ∧ ¬ SameOrbit u v`.
This is what makes Γ the right handle for solvability — the holonomy is exactly the gauge orbit
modulo the global-automorphism orbit. -/
theorem holonomy_iff_gauge {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    (G : GaugeContract adj P χ) (u v : V) :
    HolonomyNontrivial adj P χ u v ↔ (G.Equiv u v ∧ ¬ SameOrbit adj P χ u v) := by
  unfold HolonomyNontrivial GaugeContract.Equiv
  rw [G.faithful u v]

/-- Soundness half of the bridge: a gauge link is a locally-flat pair (the gauge never
manufactures structure). -/
theorem locallyFlat_of_gauge {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    (G : GaugeContract adj P χ) {u v : V} (h : G.Equiv u v) : LocallyFlat adj P χ u v :=
  (G.faithful u v).mpr h

/-! ## Consistency — the contract is inhabited (non-vacuity of the interface) -/

/-- The **maximal partition-stabilizer**: permutations preserving every vertex's refined colour.
Its orbits are exactly the flatness classes. ⚠ This is the CONSISTENCY witness only — it is the
full `∏ Sym(fiber)`, generally non-solvable; it is **not** the recovered gauge Γ. -/
def gaugeMax (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) :
    Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ x, WLGeneric.refineStep adj P χ (σ x) = WLGeneric.refineStep adj P χ x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [Equiv.Perm.mul_apply, hσ (τ x), hτ x]
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_gaugeMax {adj : WLGeneric.GAdj V} {P : WLGeneric.GPOE V} {χ : V → Nat}
    {σ : Equiv.Perm V} :
    σ ∈ gaugeMax adj P χ ↔
      ∀ x, WLGeneric.refineStep adj P χ (σ x) = WLGeneric.refineStep adj P χ x :=
  Iff.rfl

/-- **The contract is inhabited.** `gaugeMax` realizes the flatness classes as its orbits, so the
`GaugeContract` interface is not vacuous. (Not the recovered gauge — see the module note.) -/
def gaugeContractMax (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) :
    GaugeContract adj P χ where
  carrier := gaugeMax adj P χ
  faithful := by
    intro u v
    constructor
    · intro h
      refine ⟨Equiv.swap u v, ?_, Equiv.swap_apply_left u v⟩
      rw [mem_gaugeMax]
      intro x
      rcases eq_or_ne x u with rfl | hxu
      · rw [Equiv.swap_apply_left]; exact h.symm
      rcases eq_or_ne x v with rfl | hxv
      · rw [Equiv.swap_apply_right]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
    · rintro ⟨σ, hσ, rfl⟩
      rw [mem_gaugeMax] at hσ
      exact (hσ u).symm

--#print axioms holonomy_iff_gauge
--#print axioms gaugeContractMax

end GaugeComplex
end ChainDescent
