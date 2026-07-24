import ChainDescent.GaugeNonabelian
import Mathlib.GroupTheory.Commutator.Finite

/-!
# W2 Tier B — C3 `Recover`, R-c extraction: the derived layers are module actions (L1)

Planning doc: `docs/chain-descent-w2-solvability-route.md` §3b (the "is the corner empty?" plan — this is the
**extraction / linearity-of-each-layer** piece, the one open gap A3 reduces to), §5a (R-c).

§3b's A3 empties the §3a corner **iff each derived layer of the recovered gauge acts *linearly* (as a module),
so each tower step of `of_solvable_tower` (`GaugeSolvable`) is a linear solve — not an opaque coset search.**
This module builds the **structural core** of that property.

**The core fact (L1).** The recovered gauge is a subgroup of a product `Γ ≤ (ι → G₀)` (§3a; the gadget index `ι`
is finite). Its derived tower **decomposes coordinatewise**:

> `derivedSeries (ι → G₀) k = ∏ᵢ derivedSeries G₀ k`  (`derivedSeries_pi_const`)
> equivalently `x ∈ derivedSeries (ι → G₀) k ↔ ∀ i, x i ∈ derivedSeries G₀ k`  (`mem_derivedSeries_pi`)

via Mathlib's `commutator_pi_pi_of_finite` (the derived subgroup of a finite product is the product of the
derived subgroups). This is "**each layer is a free module of rank `|ι|`**" in its exact provable form: the
solvable tower is *per gadget*, so each step decomposes over the gadgets — a linear (per-coordinate) problem,
never an entangled coset search over `|G₀|^{|ι|}` cosets. It is the structural reason the abelian branch
(`kerF2`, one Gaussian pass over `ι → ZMod 2`) generalizes up the whole tower.

**Scope boundary (the remaining bricks, §3b).** L2: the local layer `A_k = G₀⁽ᵏ⁾/G₀⁽ᵏ⁺¹⁾` is abelian, so the
product layer is literally `ι → A_k`, an `A_k`-module. L3: the per-layer solve is Smith/Gaussian over `A_k`,
with `kerF2` the `k=0`/`ZMod 2` instance. **L4 stays CARRIED** (shared with `ForcingModel.bridge`): that
`Recover` produces these layers *as explicit linear systems from the graph*. L1 (here) is the group-theoretic
structure those bricks stand on; it does not itself close L4.
-/

namespace ChainDescent
namespace GaugeComplex

open Subgroup

/-- The product of `⊤`s is `⊤` (base of the coordinatewise decomposition). -/
private theorem pi_univ_top {ι : Type*} {G₀ : Type*} [Group G₀] :
    Subgroup.pi Set.univ (fun _ : ι => (⊤ : Subgroup G₀)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_pi]
  exact fun i _ => Subgroup.mem_top _

/-- **L1 — the derived tower of the product gauge decomposes coordinatewise.** For a finite gadget index `ι`,
the `k`-th derived subgroup of `ι → G₀` is the product of the `k`-th derived subgroups of `G₀`. This is the
"each layer is a free module of rank `|ι|`" structure: the solvable tower is *per gadget*, so each step is a
linear (per-coordinate) problem. Proof: induction on `k` via `commutator_pi_pi_of_finite`. -/
theorem derivedSeries_pi_const {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) :
    derivedSeries (ι → G₀) k = Subgroup.pi Set.univ (fun _ : ι => derivedSeries G₀ k) := by
  induction k with
  | zero => simp only [derivedSeries_zero]; exact pi_univ_top.symm
  | succ k ih =>
    rw [derivedSeries_succ, ih, Subgroup.commutator_pi_pi_of_finite]
    rfl

/-- **L1, membership form.** An element of `ι → G₀` lies in the `k`-th layer iff **each gadget coordinate**
does — the per-gadget characterization the layer solve consumes. -/
theorem mem_derivedSeries_pi {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) (x : ι → G₀) :
    x ∈ derivedSeries (ι → G₀) k ↔ ∀ i, x i ∈ derivedSeries G₀ k := by
  rw [derivedSeries_pi_const, Subgroup.mem_pi]
  simp

/-- **L1, coefficient-of-layer consequence.** The projection at gadget `i` carries the `k`-th product-gauge
layer *onto* the `k`-th local layer `derivedSeries G₀ k` (surjectively). Together with `mem_derivedSeries_pi`
this says the product layer is exactly `∏ᵢ (local layer)` — the free-module shape (L2 attaches the abelian
`A_k = G₀⁽ᵏ⁾/G₀⁽ᵏ⁺¹⁾` as the coefficient group). Restates `map_eval_derivedSeries` for the layer narrative. -/
theorem map_eval_layer {ι : Type*} {G₀ : Type*} [Group G₀] (i : ι) (k : ℕ) :
    (derivedSeries (ι → G₀) k).map (Pi.evalMonoidHom (fun _ : ι => G₀) i) = derivedSeries G₀ k :=
  map_eval_derivedSeries i k

--#print axioms derivedSeries_pi_const
--#print axioms mem_derivedSeries_pi

end GaugeComplex
end ChainDescent
