import ChainDescent.GaugeSolvable
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# W2 Tier B — C3 `Recover`, piece R-c (non-abelian): the recovered gauge group construction

Planning doc: `docs/chain-descent-w2-solvability-route.md` §5a (R-c table), §3a (the Luks sharpening),
§3b (the "is the corner empty?" argument plan — this module builds the **A3** skeleton).

`R-c` builds the gauge `carrier` from the recovered system `M`. The **abelian** case is `GaugeAbelian.kerF2`
(the F₂ gauge as an additive subgroup, canonized by Gaussian elimination). This module is the **non-abelian**
case, and it is pinned by the §3a/§3b structural fact:

> the recovered gauge is a **subgroup of a product** `Γ ≤ (ι → G₀)` of the FIXED local gadget group `G₀`
> over the gadget index `ι` (for CFI this is `Z₂^β ≤ Z₂^{|E|}`; for the group-CFI it is `G₀^m`).

From that one fact the whole **A3** lead (§3b) is formal, and it needs NO composition-factor degree bound
(so it sidesteps the Luks-`Γ_d` hedge entirely — §3a):

* **`isSolvable_pi`** — `ι → G₀` is solvable whenever `G₀` is (any index type; one uniform derived length,
  since `G₀` is fixed). Hence any recovered gauge `Γ ≤ (ι → G₀)` is solvable (`isSolvable_recoveredGauge`),
  and its image in `Sym V` — a `GaugeContract`-shaped `carrier` — is solvable (`isSolvable_gaugeCarrier`).
* **`recoveredGauge_reduces_to_abelian`** — wiring the above into the **built** `of_solvable_tower`
  (`GaugeSolvable`): a canonization capability holding on **abelian** gauge layers and preserved across each
  derived-series step holds on the **whole non-abelian** recovered gauge. This is the formal content of §3b's
  A3: *the non-abelian solvable gauge reduces to a tower of abelian (linear) solves.*
* **`map_eval_derivedSeries`** — the *layering evidence* (§3b "linearity of each layer"): the `n`-th derived
  layer of the product gauge is, coordinatewise, the `n`-th derived layer of `G₀`. This is the module/product
  structure that (conjecturally, once `Recover` is shown to preserve it) makes each tower step a linear solve
  rather than an opaque coset search — the one honest gap flagged in §3b, isolated here, not closed.

⚠ **What is NOT here** (matching §3b's honest boundary): the proof that `Recover` delivers each derived layer
*with its module structure intact* (so the step is a linear solve) — that is the extraction property, carried
with `ForcingModel.bridge`. This module supplies the **group-theoretic skeleton** the extraction plugs into.

Non-vacuity is discharged with a genuinely **non-abelian** solvable local group, `S₃ = Equiv.Perm (Fin 3)`.
-/

namespace ChainDescent
namespace GaugeComplex

open Equiv

/-! ## Part 1 — the recovered gauge as a subgroup of a product of the fixed local group -/

/-- **The product of copies of a fixed solvable group is solvable.** The recovered gauge lives in `ι → G₀`
(the fixed local gadget group `G₀` over the gadget index `ι`); this is degree-independent (no `Γ_d` bound):
one uniform derived length `N` (from `G₀`) kills the whole product, because commutators are coordinatewise
(`map_derivedSeries_eq` at each projection `x ↦ x i`). -/
instance isSolvable_pi {ι : Type*} {G₀ : Type*} [Group G₀] [IsSolvable G₀] :
    IsSolvable (ι → G₀) := by
  obtain ⟨N, hN⟩ := (‹IsSolvable G₀›).solvable
  refine ⟨⟨N, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  simp only [Pi.one_apply]
  have hmap : (derivedSeries (ι → G₀) N).map (Pi.evalMonoidHom (fun _ : ι => G₀) i)
      = derivedSeries G₀ N :=
    map_derivedSeries_eq (f := Pi.evalMonoidHom (fun _ : ι => G₀) i) (fun g => ⟨fun _ => g, rfl⟩) N
  have hmem := Subgroup.mem_map_of_mem (Pi.evalMonoidHom (fun _ : ι => G₀) i) hx
  rw [hmap, hN, Subgroup.mem_bot] at hmem
  exact hmem

/-- **The recovered non-abelian gauge is solvable.** Any subgroup `Γ ≤ (ι → G₀)` (which subgroup is the
carried `Recover` extraction) is solvable when the local group is — the §3b A3 premise. -/
theorem isSolvable_recoveredGauge {ι : Type*} {G₀ : Type*} [Group G₀] [IsSolvable G₀]
    (Γ : Subgroup (ι → G₀)) : IsSolvable Γ :=
  inferInstance

/-- **Layering evidence (§3b "linearity of each layer").** The `n`-th derived layer of the product gauge is,
at each coordinate `i`, exactly the `n`-th derived layer of `G₀` — the product/module structure of the layer.
That each layer is a product of copies of an *abelian* group `G₀⁽ⁿ⁾/G₀⁽ⁿ⁺¹⁾` is what makes the tower step a
linear solve; whether `Recover` preserves this is the carried extraction gap (module header). -/
theorem map_eval_derivedSeries {ι : Type*} {G₀ : Type*} [Group G₀] (i : ι) (n : ℕ) :
    (derivedSeries (ι → G₀) n).map (Pi.evalMonoidHom (fun _ : ι => G₀) i) = derivedSeries G₀ n :=
  map_derivedSeries_eq (f := Pi.evalMonoidHom (fun _ : ι => G₀) i) (fun g => ⟨fun _ => g, rfl⟩) n

/-! ## Part 2 — the extension / metabelian core (§3b A3: a tower of solvable-by-solvable steps) -/

/-- **An extension of solvable-by-solvable is solvable.** Gauge-language re-export of Mathlib's
`solvable_of_ker_le_range`: given a normal-subgroup inclusion `ν : N →* E` and a quotient map `ρ : E →* Q`
with `ker ρ ≤ range ν`, if both `N` and `Q` are solvable then `E` is. This is the abstract "two abelian
layers" fact behind §3b A3/A4 — e.g. `D_p = Z_p ⋊ Z₂` (ring-solve `Z_p`, `kerF2` the `Z₂`-quotient). -/
theorem isSolvable_extension {N E Q : Type*} [Group N] [Group E] [Group Q]
    (ν : N →* E) (ρ : E →* Q) (h : ρ.ker ≤ ν.range) [IsSolvable N] [IsSolvable Q] :
    IsSolvable E :=
  solvable_of_ker_le_range ν ρ h

/-! ## Part 3 — reduction of the recovered non-abelian gauge to the abelian branch (the deliverable) -/

/-- **The recovered non-abelian gauge reduces to the abelian branch (§3b A3, formal).** A canonization
capability `P` that holds on every **abelian** subgroup of the recovered gauge `Γ` (`habelian` = the abelian
branch, `GaugeAbelian`) and is preserved across each derived-series step (`hstep` = the carried Luks/linear
lift) holds on the **whole** non-abelian gauge (`P ⊤`). Via the built `of_solvable_tower` + `Γ` solvable.
This is the sense in which "solvable ⟹ tower of abelian (linear) solves" — the corner's poly route. -/
theorem recoveredGauge_reduces_to_abelian {ι : Type*} {G₀ : Type*} [Group G₀] [IsSolvable G₀]
    (Γ : Subgroup (ι → G₀)) (P : Subgroup Γ → Prop)
    (habelian : ∀ H : Subgroup Γ, (∀ a b : H, a * b = b * a) → P H)
    (hstep : ∀ H : Subgroup Γ, P ⁅H, H⁆ → P H) : P ⊤ :=
  of_solvable_abelian_base P habelian hstep (isSolvable_recoveredGauge Γ)

/-- **The `carrier` form (feeds `GaugeContract`).** The image in `Sym V` of the recovered gauge — a
`GaugeContract.carrier`-shaped subgroup of `Equiv.Perm V` — is solvable: the gauge acts on `V` through a
homomorphism `φ : (ι → G₀) →* Perm V`, and the image of a solvable group is solvable. So the abstract
non-abelian gauge and the concrete permutation `carrier` are both solvable, degree-independently. -/
theorem isSolvable_gaugeCarrier {ι : Type*} {G₀ : Type*} {V : Type*} [Group G₀] [IsSolvable G₀]
    (φ : (ι → G₀) →* Equiv.Perm V) : IsSolvable φ.range :=
  solvable_of_surjective φ.rangeRestrict_surjective

/-! ## Part 4 — non-vacuity: a genuinely NON-ABELIAN solvable local group (`S₃ = Perm (Fin 3)`) -/

/-- `A₃ = alternatingGroup (Fin 3)` has prime order 3, hence is cyclic, hence commutative, hence solvable. -/
instance isSolvable_alt3 : IsSolvable (alternatingGroup (Fin 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
  haveI hcyc : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
  exact isSolvable_of_comm
    (fun a b => (IsCyclic.commGroup (α := alternatingGroup (Fin 3))).mul_comm a b)

/-- **`S₃ = Perm (Fin 3)` is solvable** (extension of the abelian `A₃` by the abelian `ℤˣ` via `sign`) — the
canonical non-abelian solvable local group; the R-c reduction genuinely applies to it, not just to abelian
gauges. -/
instance isSolvable_perm3 : IsSolvable (Equiv.Perm (Fin 3)) := by
  apply isSolvable_extension (alternatingGroup (Fin 3)).subtype (Equiv.Perm.sign)
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- `S₃` is genuinely non-abelian — so the R-c reduction is not secretly about abelian gauges. -/
theorem perm3_not_comm : ¬ ∀ a b : Equiv.Perm (Fin 3), a * b = b * a := by decide

/-- Non-vacuity of `isSolvable_pi` at a non-abelian local group. -/
example : IsSolvable (Fin 5 → Equiv.Perm (Fin 3)) := inferInstance

/-- Non-vacuity of the reduction (Part 3) at a non-abelian local group. -/
example (Γ : Subgroup (Fin 4 → Equiv.Perm (Fin 3))) (P : Subgroup Γ → Prop)
    (habelian : ∀ H : Subgroup Γ, (∀ a b : H, a * b = b * a) → P H)
    (hstep : ∀ H : Subgroup Γ, P ⁅H, H⁆ → P H) : P ⊤ :=
  recoveredGauge_reduces_to_abelian Γ P habelian hstep

--#print axioms isSolvable_pi
--#print axioms recoveredGauge_reduces_to_abelian
--#print axioms isSolvable_gaugeCarrier
--#print axioms isSolvable_perm3

end GaugeComplex
end ChainDescent
