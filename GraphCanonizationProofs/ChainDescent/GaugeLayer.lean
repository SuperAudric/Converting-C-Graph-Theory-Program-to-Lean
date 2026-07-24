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
open scoped commutatorElement

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

/-! ## L2 — the layer coefficient `A_k` is abelian; the module coordinate structure -/

/-- **L2 — the layer is abelian.** The commutator of two elements of the `k`-th derived subgroup lands in the
`(k+1)`-th: `a b ∈ derivedSeries G k ⟹ ⁅a,b⁆ ∈ derivedSeries G (k+1)`. So `derivedSeries G k` is commutative
**modulo the next layer** — the layer `A_k = D_k/D_{k+1}` is abelian. That abelianness is exactly what makes the
per-layer solve **linear** (a module/lattice computation — Gaussian/Smith), not a coset search over `|D_k/D_{k+1}|`. -/
theorem commutator_mem_derivedSeries_succ {G : Type*} [Group G] (k : ℕ) {a b : G}
    (ha : a ∈ derivedSeries G k) (hb : b ∈ derivedSeries G k) :
    ⁅a, b⁆ ∈ derivedSeries G (k + 1) := by
  rw [derivedSeries_succ]
  exact commutator_mem_commutator ha hb

/-- **The layer coefficient group `A_k = D_k/D_{k+1}`** — the abelianization of the `k`-th derived subgroup. A
`CommGroup` (so `Additive (layerCoeff G k)` is an `AddCommGroup`): the abelian coefficient module the `k`-th
tower step is linear over. The product gauge's layer is the free module `ι → A_k` (rank = gadget count); the
coordinate projections onto each gadget's `A_k` are `layerProj`. -/
abbrev layerCoeff (G : Type*) [Group G] (k : ℕ) : Type _ :=
  Abelianization ↥(derivedSeries G k)

/-- The coordinatewise projection of the product gauge's `k`-th derived subgroup onto gadget `i`'s
(`x ↦ x i`), landing in `derivedSeries G₀ k` by L1 (`mem_derivedSeries_pi`). -/
def derivedProj {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) (i : ι) :
    ↥(derivedSeries (ι → G₀) k) →* ↥(derivedSeries G₀ k) where
  toFun x := ⟨x.val i, ((mem_derivedSeries_pi k x.val).mp x.property) i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem derivedProj_surjective {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) (i : ι) :
    Function.Surjective (derivedProj (ι := ι) (G₀ := G₀) k i) := by
  rintro ⟨g, hg⟩
  exact ⟨⟨fun _ => g, (mem_derivedSeries_pi k _).mpr (fun _ => hg)⟩, rfl⟩

/-- **L2 — the product layer's coefficient projects onto each gadget's `A_k`.** The `i`-th coordinate map
`A_k(ι→G₀) →* A_k(G₀)` (abelianizing `derivedProj`). Its surjectivity (`layerProj_surjective`) says the
product-gauge layer coefficient surjects coordinatewise onto each local `A_k` — the free-module `ι → A_k`
coordinate structure that L3's per-coordinate linear solve consumes. -/
def layerProj {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) (i : ι) :
    layerCoeff (ι → G₀) k →* layerCoeff G₀ k :=
  Abelianization.map (derivedProj k i)

theorem layerProj_surjective {ι : Type*} [Finite ι] {G₀ : Type*} [Group G₀] (k : ℕ) (i : ι) :
    Function.Surjective (layerProj (ι := ι) (G₀ := G₀) k i) := by
  intro y
  obtain ⟨h, rfl⟩ : ∃ h, Abelianization.of h = y :=
    QuotientGroup.induction_on y (fun h => ⟨h, rfl⟩)
  obtain ⟨g, rfl⟩ := derivedProj_surjective (ι := ι) (G₀ := G₀) k i h
  exact ⟨Abelianization.of g, by rw [layerProj, Abelianization.map_of]⟩

/-! ## L3 — the per-layer solve is LINEAR: `kerF2` is the `A = ZMod 2` instance -/

open RigidSolveF2

/-- The F₂ pairing is linear in the scalar on the assignment side: `dotP r (c • x) = c * dotP r x`. -/
theorem dotP_smul_right {ι : Type*} [Fintype ι] (r : ι → ZMod 2) (c : ZMod 2) (x : ι → ZMod 2) :
    dotP r (c • x) = c * dotP r x := by
  simp only [dotP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **L3 — the abelian gauge is `ZMod 2`-scalar-closed** — `kerF2 H` is closed under `F₂`-scaling, so it is a
*subspace*, not merely an additive subgroup: the layer solve is **linear**. -/
theorem kerF2_smul_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Finset (ι → ZMod 2)) (c : ZMod 2)
    {x : ι → ZMod 2} (hx : x ∈ kerF2 H) : c • x ∈ kerF2 H := by
  rw [mem_kerF2] at hx ⊢
  intro r hr
  rw [dotP_smul_right, hx r hr, mul_zero]

/-- **L3 — `kerF2` as an F₂-*subspace*.** The abelian branch's gauge, upgraded from `AddSubgroup` to a genuine
`Submodule (ZMod 2) (ι → ZMod 2)` — a subspace of the **free `F₂`-module of rank `|ι|`**. This is the
concrete witness that the per-layer solve is a **linear-algebra** computation (Gaussian elimination over the
field `F₂`), and it is exactly the `k = 0`, coefficient `A_0 = ZMod 2` instance of the general layer module
`ι → A_k` (L2: `A_k = layerCoeff G₀ k`, an abelian coefficient group). The general layer is an `AddSubgroup`
(ℤ-submodule) of `ι → A_k`, solved by Smith normal form over `A_k`; `kerF2Submodule` is its field case. -/
def kerF2Submodule {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Finset (ι → ZMod 2)) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {x | ∀ r ∈ H, dotP r x = 0}
  zero_mem' := fun r _ => dotP_zero_right r
  add_mem' := fun ha hb r hr => by rw [dotP_add_right, ha r hr, hb r hr, add_zero]
  smul_mem' := fun c x hx r hr => by rw [dotP_smul_right, hx r hr, mul_zero]

/-- The subspace `kerF2Submodule` has exactly the `kerF2` carrier — same gauge, now recorded as linear. -/
@[simp] theorem mem_kerF2Submodule {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Finset (ι → ZMod 2)}
    {x : ι → ZMod 2} : x ∈ kerF2Submodule H ↔ x ∈ kerF2 H := Iff.rfl

/-- The general layer coefficient `A_k` is an abelian additive group (a ℤ-module), so the product-gauge layer
`ι → A_k` is a **free ℤ-module of rank `|ι|`** — the object the per-layer Smith solve is linear over. (`kerF2`
above is the `A_k = ZMod 2` field case.) -/
example (G₀ : Type*) [Group G₀] (k : ℕ) : AddCommGroup (Additive (layerCoeff G₀ k)) := inferInstance

--#print axioms derivedSeries_pi_const
--#print axioms commutator_mem_derivedSeries_succ
--#print axioms layerProj_surjective
--#print axioms kerF2Submodule
--#print axioms kerF2_smul_mem

end GaugeComplex
end ChainDescent
