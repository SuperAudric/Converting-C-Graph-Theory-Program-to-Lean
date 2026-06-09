import ChainDescent
import ChainDescent.CascadeOracle
import ChainDescent.Group
import ChainDescent.Saturation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# B1 — cascade composition (Theorem 3a), Phases A + C

The Lean discharge of **Theorem 3a (cascade composition)**: the cascade depths of
layered cascade-class subgroups **add**. Build plan in
`docs/chain-descent-tier3a-b1-build-plan.md`; paper in
`docs/chain-descent-tier3a-cascade-composition.md`.

**The formalization decision (build-plan §1).** We do *not* recurse on the quotient
graph as a re-typed `AdjMatrix mᵢ`. The conclusion only needs that warm refinement at
the *final* cumulative individualization set `T_k = S₁ ∪ … ∪ S_k` is `Discrete`, so we
stay on `Fin n` and **telescope cumulative sets**:

* **Phase A** — the cascade-class interface: `RecoverableByDepth` (already in
  `CascadeOracle.lean`, with Tier-1/Tier-2 instances) is the cascade-class predicate;
  here we add `IsBase` (the chain bottoms out at `{1}`) and `LayerStep` (the per-layer
  transfer obligation, discharged in Phase D).
* **Phase C** — the composition theorem:
  - **(C1)** `discrete_of_cellsAreOrbits_base` — `CellsAreOrbits` at a base ⟹ `Discrete`.
  - **(C2)** `cellsAreOrbits_compose` — the induction chaining per-layer `LayerStep`s
    from layer 1's unconditional recoverability up to `CellsAreOrbits` at `T_k`.
  - `cumulative_card_le` — `|⋃ Sᵢ| ≤ Σ fᵢ` (the "depths add" cardinality).
  - `cascadeComposition` — the headline, = (C2) then (C1). **Conditional on the
    per-layer steps** (the `hstep` hypotheses = the transfer, Phase D); §4.3 of the
    paper confirms 4.2.5 is the *only* genuinely new content, so this conditional form
    is the paper's actual structure.

Phase D (discharging `LayerStep` from Tier-1/Tier-2 via the quotient — the §4.2.5
transfer lemma) is the hard residual and deliberately **not** here; the headline does
not depend on it.
-/

namespace ChainDescent

open scoped BigOperators

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}

/-! ## Phase A — the cascade-class interface

`RecoverableByDepth adj P bound` (in `CascadeOracle.lean`) is the cascade-class
membership predicate — "∃ a set of size ≤ bound at which cells = orbits" — with
Tier-1 (`recoverableByDepth_cfi`) and Tier-2 (`recoverableByDepth_scheme`) instances
already proved. Phase A adds the two pieces composition needs on top of it. -/

/-- **Base set.** `T` is a *base* of the (`P`-preserving) automorphism group when its
pointwise stabilizer is trivial — i.e. the `Aut_T`-orbit relation is equality. This is
the chain's bottom `H_k = {1}`: once `T` is a base, the orbit partition is the discrete
partition. (`OrbitPartition adj P T v w → v = w`.) -/
def IsBase (adj : AdjMatrix n) (P : PMatrix n) (T : Finset (Fin n)) : Prop :=
  ∀ v w, OrbitPartition adj P T v w → v = w

/-- **A layer step (the per-layer transfer obligation).** Given that cells already
coincide with `Aut_T`-orbits (the quotient `G_T` is exposed), individualizing the
increment `S` brings cells down to `Aut_{T ∪ S}`-orbits. This is exactly the paper's
§4.2.5 transferred to `G`; discharging it from the Tier-1/Tier-2 layer theorems is
**Phase D**. Here it is the interface the composition induction consumes. -/
def LayerStep (adj : AdjMatrix n) (P : PMatrix n) (T S : Finset (Fin n)) : Prop :=
  CellsAreOrbits adj P T → CellsAreOrbits adj P (T ∪ S)

/-! ## Phase C — the composition theorem -/

/-- **(C1) Finish.** If cells coincide with `Aut_T`-orbits (`CellsAreOrbits`) and `T`
is a base (`Aut_T` trivial), then warm refinement at `T` is `Discrete`: same-cell ⟹
same-orbit (`CellsAreOrbits`) ⟹ equality (`IsBase`). This is the cascade reaching the
discrete partition — full canonization at `T`. -/
theorem discrete_of_cellsAreOrbits_base {T : Finset (Fin n)}
    (hco : CellsAreOrbits adj P T) (hbase : IsBase adj P T) :
    Discrete (warmRefine adj P (individualizedColouring n T)) :=
  fun v w hcell => hbase v w (hco v w hcell)

/-- **(C2) Construction — the composition induction.** Cumulative individualization
sets `T 0 ⊆ T 1 ⊆ …` (with `T 0` = the first layer's set), where layer 1 gives
`CellsAreOrbits` at `T 0` unconditionally (`hbase`) and each subsequent layer is a
`LayerStep` (`hstep i : CellsAreOrbits (T i) → CellsAreOrbits (T (i+1))`). Then
`CellsAreOrbits` holds at the final cumulative set `T k`. The depths *add* because each
step only widens the set by its layer's bounded increment (cardinality below). -/
theorem cellsAreOrbits_compose {k : Nat} (T : Nat → Finset (Fin n))
    (hbase : CellsAreOrbits adj P (T 0))
    (hstep : ∀ i, i < k → CellsAreOrbits adj P (T i) → CellsAreOrbits adj P (T (i + 1))) :
    CellsAreOrbits adj P (T k) := by
  induction k with
  | zero => exact hbase
  | succ m ih =>
    exact hstep m (Nat.lt_succ_self m) (ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)))

/-- **Cardinality — depths add.** The cumulative individualization set
`⋃_{i ≤ k} S i` has size at most `Σ_{i ≤ k} f i` whenever each layer set `S i` is
bounded by its depth `f i`. This is the `|S| ≤ Σ fᵢ` half of Theorem 3a. -/
theorem cumulative_card_le {k : Nat} (S : Nat → Finset (Fin n)) (f : Nat → Nat)
    (hf : ∀ i, (S i).card ≤ f i) :
    ((Finset.range (k + 1)).biUnion S).card ≤ ∑ i ∈ Finset.range (k + 1), f i :=
  le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum (fun i _ => hf i))

/-- **Theorem 3a (cascade composition) — the headline, conditional form.** Given
cumulative sets `T` with layer 1's recoverability (`hbase`), per-layer transfer steps
(`hstep` — the Phase-D obligation), and the final set a base (`hbaseSet`, the chain
ends at `{1}`), warm refinement on `(G, T k)` reaches the **discrete** partition. The
companion `cumulative_card_le` bounds `|T k| ≤ Σ fᵢ`, so the cascade depth is `≤ Σ fᵢ`
— the depths add. Conditional on `hstep` (= §4.2.5 transferred per layer), which §4.3
identifies as the sole new content; discharging it is Phase D. -/
theorem cascadeComposition {k : Nat} (T : Nat → Finset (Fin n))
    (hbase : CellsAreOrbits adj P (T 0))
    (hstep : ∀ i, i < k → CellsAreOrbits adj P (T i) → CellsAreOrbits adj P (T (i + 1)))
    (hbaseSet : IsBase adj P (T k)) :
    Discrete (warmRefine adj P (individualizedColouring n (T k))) :=
  discrete_of_cellsAreOrbits_base (cellsAreOrbits_compose T hbase hstep) hbaseSet

/-! ### Single-layer sanity check (k = 0)

The `k = 0` case of `cascadeComposition` is exactly the existing Tier-1/Tier-2 result:
one cascade-class layer, recoverable at one bounded set, which (being a base) reaches
discreteness. This recovers the orbit-recovery theorems as the base of the composition,
confirming the abstraction sits on top of them. -/
theorem cascadeComposition_single {T₀ : Finset (Fin n)}
    (hco : CellsAreOrbits adj P T₀) (hbaseSet : IsBase adj P T₀) :
    Discrete (warmRefine adj P (individualizedColouring n T₀)) :=
  cascadeComposition (fun _ => T₀) hco (fun i h => absurd h (Nat.not_lt_zero i)) hbaseSet

/-! ## Phase D — discharging `LayerStep` (the §4.2.5 transfer), intrinsic route

Approach B (build-plan §3): stay on `Fin n`, reduce `LayerStep` to a *witness-upgrade*
via **set-monotonicity** of warm refinement, reusing the `refineStep_iff` API. We do
*not* materialize the quotient graph (Approach A, rejected — `refineStep` is axiomatic
and does not transfer across a change of vertex set). -/

/-! ### Set-monotonicity of warm refinement

The load-bearing prerequisite: warm refinement is monotone in the partition order of its
initial colouring. (The docs mis-cite `warmRefine_refines` for this; that lemma relates
`warmRefine` to its *initial* colouring, a different statement.) -/

/-- `χ₁` refines `χ₂` — the partition of `χ₁` is finer (more classes). -/
def Refines (χ₁ χ₂ : Colouring n) : Prop := ∀ a b, χ₁ a = χ₁ b → χ₂ a = χ₂ b

/-- **Signatures respect refinement.** If `χ₁` refines `χ₂`, then any signature
*separation* under `χ₁` carries to `χ₂`: `signature χ₂` is the image of `signature χ₁`
under the coarsening map on colours, so equal `χ₁`-signatures give equal `χ₂`-signatures.
The crux of warm-refinement monotonicity. -/
theorem signature_refines {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂)
    {v w : Fin n} (h : signature adj P χ₁ v = signature adj P χ₁ w) :
    signature adj P χ₂ v = signature adj P χ₂ w := by
  classical
  -- coarsening map `g` with `g (χ₁ u) = χ₂ u` (well-defined since `χ₁` refines `χ₂`).
  set g : Nat → Nat := fun c => if h : ∃ u, χ₁ u = c then χ₂ h.choose else 0 with hg_def
  have hg : ∀ u, g (χ₁ u) = χ₂ u := by
    intro u
    have hex : ∃ u', χ₁ u' = χ₁ u := ⟨u, rfl⟩
    simp only [hg_def, dif_pos hex]
    exact href _ _ hex.choose_spec
  have key : ∀ x : Fin n, signature adj P χ₂ x
      = (signature adj P χ₁ x).map (fun t => (g t.1, t.2.1, t.2.2)) := by
    intro x
    simp only [signature, Multiset.map_map]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    simp only [Function.comp_apply, hg u]
  rw [key v, key w, h]

/-- One refinement round preserves refinement: `Refines χ₁ χ₂ → Refines (refineStep χ₁)
(refineStep χ₂)`. From `refineStep_iff` (same colour ∧ same signature) + `signature_refines`. -/
private theorem refineStep_mono {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂) :
    Refines (refineStep adj P χ₁) (refineStep adj P χ₂) := by
  intro a b hab
  rw [refineStep_iff] at hab ⊢
  exact ⟨href _ _ hab.1, signature_refines href hab.2⟩

/-- Iterating refinement preserves refinement. -/
theorem iterate_refineStep_refines {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂) :
    ∀ k, Refines ((refineStep adj P)^[k] χ₁) ((refineStep adj P)^[k] χ₂) := by
  intro k
  induction k with
  | zero => exact href
  | succ m ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact refineStep_mono ih

/-- **Warm refinement is monotone in the initial colouring.** A finer initial colouring
yields a finer warm-refined partition. -/
theorem warmRefine_refines_initial {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂) :
    Refines (warmRefine adj P χ₁) (warmRefine adj P χ₂) :=
  iterate_refineStep_refines href n

/-- Individualizing a *superset* gives a finer initial colouring: `T ⊆ T'` ⟹
`individualizedColouring n T'` refines `individualizedColouring n T`. -/
theorem individualizedColouring_refines {T T' : Finset (Fin n)} (hsub : T ⊆ T') :
    Refines (individualizedColouring n T') (individualizedColouring n T) := by
  intro a b hab
  simp only [individualizedColouring] at hab ⊢
  by_cases ha' : a ∈ T' <;> by_cases hb' : b ∈ T'
  · rw [if_pos ha', if_pos hb'] at hab
    have hab' : a = b := Fin.ext (by omega)
    rw [hab']
  · rw [if_pos ha', if_neg hb'] at hab; exact absurd hab (Nat.succ_ne_zero _)
  · rw [if_neg ha', if_pos hb'] at hab; exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [if_neg (fun h => ha' (hsub h)), if_neg (fun h => hb' (hsub h))]

/-- **Set-monotonicity (the payoff).** Two vertices in the same `(T ∪ S)`-cell are in the
same `T`-cell: warm refinement at a larger individualization set refines warm refinement
at a smaller one. This is "1-WL monotone in the individualization set". -/
theorem warmRefine_indiv_mono {T S : Finset (Fin n)} {v w : Fin n}
    (h : warmRefine adj P (individualizedColouring n (T ∪ S)) v
       = warmRefine adj P (individualizedColouring n (T ∪ S)) w) :
    warmRefine adj P (individualizedColouring n T) v
      = warmRefine adj P (individualizedColouring n T) w :=
  warmRefine_refines_initial (individualizedColouring_refines Finset.subset_union_left) v w h

/-! ### The reduction: `LayerStep` from a witness-upgrade -/

/-- **The witness-upgrade (the genuine §4.2.5 content).** For vertices `v, w` already in
the same `Aut_T`-orbit and the same `(T ∪ S)`-cell, the orbit relation *upgrades* to
`Aut_{T∪S}`: there is a `(T∪S)`-fixing automorphism relating them. Discharging this from
the Tier-1/Tier-2 layer theorems is the remaining Phase-D work (build-plan §3 step 5). -/
def WitnessUpgrade (adj : AdjMatrix n) (P : PMatrix n) (T S : Finset (Fin n)) : Prop :=
  ∀ v w, OrbitPartition adj P T v w →
    warmRefine adj P (individualizedColouring n (T ∪ S)) v
      = warmRefine adj P (individualizedColouring n (T ∪ S)) w →
    OrbitPartition adj P (T ∪ S) v w

/-- **The reduction.** A witness-upgrade discharges a layer step. Uses set-monotonicity
(`warmRefine_indiv_mono`) to pull a `(T∪S)`-cell back to a `T`-cell, then `CellsAreOrbits T`
to get the `Aut_T`-orbit, then the upgrade. This is where the Phase-C composition meets
the per-layer content. -/
theorem layerStep_of_witnessUpgrade {T S : Finset (Fin n)}
    (hwu : WitnessUpgrade adj P T S) : LayerStep adj P T S := by
  intro hco v w hcell
  exact hwu v w (hco v w (warmRefine_indiv_mono hcell)) hcell

/-! ### Trivial layer-step instances (real corollaries) -/

/-- The empty layer is a no-op: `LayerStep adj P T ∅`. -/
theorem layerStep_empty {T : Finset (Fin n)} : LayerStep adj P T ∅ := by
  intro h; rwa [Finset.union_empty]

/-- A layer adding nothing new (`S ⊆ T`) is a no-op. -/
theorem layerStep_subset {T S : Finset (Fin n)} (hS : S ⊆ T) : LayerStep adj P T S := by
  intro h; rwa [Finset.union_eq_left.mpr hS]

/-- If the widened set is independently orbit-recoverable, the step holds (its hypothesis
is irrelevant). The hook for a layer theorem that applies to `G` directly. -/
theorem layerStep_of_cellsAreOrbits {T S : Finset (Fin n)}
    (h : CellsAreOrbits adj P (T ∪ S)) : LayerStep adj P T S := fun _ => h

/-- **The recursion bottom.** If the widened set discretizes warm refinement, the step
holds unconditionally (`cellsAreOrbits_of_discrete`). The final layer reaching `{1}`. -/
theorem layerStep_of_discrete {T S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n (T ∪ S)))) :
    LayerStep adj P T S := fun _ => cellsAreOrbits_of_discrete hd

/-! ### Support-backbone sufficient condition (bridge to harvested generators) -/

/-- **Witness-upgrade from path-fixing automorphisms.** If every same-orbit, same-cell
pair `v, w` admits a `P`-preserving automorphism whose support avoids the committed set
`T ∪ S` (so it fixes the whole individualized path) and sends `v ↦ w`, the upgrade holds
(via `orbitPartition_of_support_disjoint`). This is exactly what the cascade/linear
oracles harvest — a verified generator fixing the committed path — so it is the bridge
from Theorem 3a's per-layer obligation to the algorithm's actual output. -/
theorem witnessUpgrade_of_pathFixing {T S : Finset (Fin n)}
    (h : ∀ v w, OrbitPartition adj P T v w →
      warmRefine adj P (individualizedColouring n (T ∪ S)) v
        = warmRefine adj P (individualizedColouring n (T ∪ S)) w →
      ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u)
        ∧ Disjoint (T ∪ S) π.support ∧ π v = w) :
    WitnessUpgrade adj P T S := by
  intro v w horb hcell
  obtain ⟨π, hπ, hP, hdisj, hvw⟩ := h v w horb hcell
  exact orbitPartition_of_support_disjoint hπ hP hdisj hvw

/-! ### Step 5 — the synthesis: Theorem 3a reduced to harvested path-fixing generators

The end-to-end composition. Chaining `cascadeComposition` (Phase C) through
`layerStep_of_witnessUpgrade` + `witnessUpgrade_of_pathFixing` (Phase D) reduces the
**whole** of Theorem 3a to a single hypothesis: *at every layer, the residual orbit
symmetry is realized by automorphisms that fix the committed path* (support disjoint
from the cumulative individualization set). That hypothesis is exactly the
**harvested-generator** picture of [`chain-descent-calculator.md`](../../docs/chain-descent-calculator.md)
§2 — every cascade-oracle orbit certification and every linear-oracle twist is a
verified automorphism fixing the path. So this theorem is the precise bridge from the
combinatorial composition to the algorithm's actual output.

What it does **not** yet contain: the *existence* of those path-fixing witnesses for a
concrete layer class (CFI gadget twists, scheme automorphisms). That is the remaining
deep work — it needs the gadget/scheme machinery to construct the witnesses — and is
correctly isolated here as the sole hypothesis. -/

/-- **Theorem 3a, reduced to harvested path-fixing generators.** Cumulative
individualization sets `T` built by increments `S` (`T (i+1) = T i ∪ S i`), with layer 1
recoverable (`hbase`), every layer's residual symmetry realized by **path-fixing**
automorphisms (`hwit` — support disjoint from the committed set, i.e. harvested
generators), and the final set a base (`hbaseSet`). Then warm refinement on `(G, T k)`
reaches the **discrete** partition. With `cumulative_card_le`, depth `≤ Σ fᵢ` — the
depths add, *unconditionally modulo the existence of the per-layer path-fixing
witnesses*. -/
theorem cascadeComposition_pathFixing {k : Nat}
    (T : Nat → Finset (Fin n)) (S : Nat → Finset (Fin n))
    (hT : ∀ i, i < k → T (i + 1) = T i ∪ S i)
    (hbase : CellsAreOrbits adj P (T 0))
    (hwit : ∀ i, i < k → ∀ v w, OrbitPartition adj P (T i) v w →
      warmRefine adj P (individualizedColouring n (T i ∪ S i)) v
        = warmRefine adj P (individualizedColouring n (T i ∪ S i)) w →
      ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u)
        ∧ Disjoint (T i ∪ S i) π.support ∧ π v = w)
    (hbaseSet : IsBase adj P (T k)) :
    Discrete (warmRefine adj P (individualizedColouring n (T k))) := by
  refine cascadeComposition T hbase (fun i hi => ?_) hbaseSet
  rw [hT i hi]
  exact layerStep_of_witnessUpgrade (witnessUpgrade_of_pathFixing (hwit i hi))

/-- **Two-layer corollary** — the smallest genuine composition. An outer layer
recoverable at `T₀` (a cascade-class set, e.g. Tier 1/2 on `G`), an inner layer with
increment `S` whose residual symmetry is path-fixing, and the union a base. The
`CFI(scheme)` / `Scheme(CFI)` shape (build-plan §5.b) once the inner witnesses are
constructed. -/
theorem cascadeComposition_twoLayer {T₀ S : Finset (Fin n)}
    (hbase : CellsAreOrbits adj P T₀)
    (hwit : ∀ v w, OrbitPartition adj P T₀ v w →
      warmRefine adj P (individualizedColouring n (T₀ ∪ S)) v
        = warmRefine adj P (individualizedColouring n (T₀ ∪ S)) w →
      ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u)
        ∧ Disjoint (T₀ ∪ S) π.support ∧ π v = w)
    (hbaseSet : IsBase adj P (T₀ ∪ S)) :
    Discrete (warmRefine adj P (individualizedColouring n (T₀ ∪ S))) :=
  discrete_of_cellsAreOrbits_base
    (layerStep_of_witnessUpgrade (witnessUpgrade_of_pathFixing hwit) hbase) hbaseSet

/-! ## Phase 6b — CFI gadget flips discharge the Tier-3a `hwit`

The Stage-3 gadget flip (`CFI.lean §15`) packaged its three controlled properties into the exact
path-fixing existential `cascadeComposition_pathFixing`'s `hwit` requires
(`IsCFI'.cfiFlipAut_pathFixing_witness`). This section is the drop-in: it discharges `hwit` for a CFI
layering from the per-layer existence of committed-set-avoiding gadget flips, and gives Theorem 3a for
CFI layers conditional only on that existence (the same cascade-1b content as the linear oracle's
`CFIGadgetFlippableLocal`). -/

/-- **Per-layer CFI gadget-flip existence.** For each layer `i` and same-orbit, same-cell pair
`(v, w)`, an even-symmetric cycle `F` whose gadget flip maps `v ↦ w`, with the committed set
`T i ∪ S i` confined to `F`-free gadgets. The `hwit` analog of the linear oracle's
`CFIGadgetFlippableLocal`. -/
def CFILayerGadgetFlippable (h : IsCFI' adj) (k : Nat) (T S : Nat → Finset (Fin n)) : Prop :=
  ∀ i, i < k → ∀ v w, OrbitPartition adj P (T i) v w →
    warmRefine adj P (individualizedColouring n (T i ∪ S i)) v
      = warmRefine adj P (individualizedColouring n (T i ∪ S i)) w →
    ∃ (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ x, (h.H.flipSet F x).card % 2 = 0),
      (∀ a b, F a b = F b a) ∧
      (∀ x ∈ T i ∪ S i, h.H.flipSet F (h.H.gadget (h.e x)) = ∅) ∧
      h.cfiFlipAut F hEven v = w

/-- **CFI gadget flips discharge the path-fixing witness** (Phase 6b). Given per-layer
committed-set-avoiding gadget flips realising each residual orbit map (`CFILayerGadgetFlippable`) and
an automorphism-invariant `P`, the Tier-3a `hwit` hypothesis holds — directly via
`cfiFlipAut_pathFixing_witness`. The connector from the Stage-3 construction to Theorem 3a. -/
theorem cfiLayer_pathFixing_hwit (h : IsCFI' adj) {k : Nat}
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {T S : Nat → Finset (Fin n)} (hflip : CFILayerGadgetFlippable (P := P) h k T S) :
    ∀ i, i < k → ∀ v w, OrbitPartition adj P (T i) v w →
      warmRefine adj P (individualizedColouring n (T i ∪ S i)) v
        = warmRefine adj P (individualizedColouring n (T i ∪ S i)) w →
      ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u)
        ∧ Disjoint (T i ∪ S i) π.support ∧ π v = w := by
  intro i hi v w horb hcell
  obtain ⟨F, hEven, hFsymm, hTfree, hvw⟩ := hflip i hi v w horb hcell
  exact h.cfiFlipAut_pathFixing_witness F hEven hFsymm hP hTfree hvw

/-- **Theorem 3a for CFI layers** (Phase 6b capstone). If a graph decomposes into CFI layers whose
residual orbit maps are realised by committed-set-avoiding gadget flips, the descent reaches the
discrete partition. The CFI instance of `cascadeComposition_pathFixing`, with `hwit` discharged by the
Stage-3 gadget flips — conditional only on the (cascade-1b) existence of the per-layer cycles. -/
theorem cascadeComposition_cfi (h : IsCFI' adj) {k : Nat}
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (T : Nat → Finset (Fin n)) (S : Nat → Finset (Fin n))
    (hT : ∀ i, i < k → T (i + 1) = T i ∪ S i)
    (hbase : CellsAreOrbits adj P (T 0))
    (hflip : CFILayerGadgetFlippable (P := P) h k T S)
    (hbaseSet : IsBase adj P (T k)) :
    Discrete (warmRefine adj P (individualizedColouring n (T k))) :=
  cascadeComposition_pathFixing T S hT hbase (cfiLayer_pathFixing_hwit h hP hflip) hbaseSet

/-! ## Harvest-window connector — Theorem 3a's `Discrete` output as a `RecoverableByDepth` certificate

The harvest-window lemma ([`docs/chain-descent-harvest-window.md`](../../../docs/chain-descent-harvest-window.md))
states its conclusion as `RecoverableByDepth adj P (b g)`, with `b g` the recoverability depth (§6.3
there). Theorem 3a (`cascadeComposition_pathFixing`) outputs `Discrete (warmRefine … (T k))`. These
connect: a discrete warm refinement at the cumulative set `T k` **is** a `RecoverableByDepth` certificate
at depth `|T k|` (via `cellsAreOrbits_of_discrete`). So the harvest-window's `recoverableByDepth_of_findable`
is exactly `cascadeComposition_pathFixing` re-housed in the `RecoverableByDepth` conclusion, with
`b g = |T k|` the cumulative individualization size (`≤ Σ |S i|` by `cumulative_card_le` — the depths add).

What this connector does **not** contain — and what the harvest-window *screen* `D1∨D2` would supply — is
the per-layer `hwit` (the path-fixing witnesses). That bridge, **screen `D1∨D2` ⟹ `hwit`**, is the
class-agnostic generalization of cascade-1b (the `CFILayerGadgetFlippable` existence above), reached via
the support trichotomy rather than the (false-in-general) σ-coherence route. Defining `D1`/`D2` as Lean
predicates and proving that bridge is the remaining content; here it is correctly isolated as `hwit`. -/

/-- **Harvest-window conclusion from path-fixing layers.** Theorem 3a's discrete output, re-expressed as
the harvest-window's `RecoverableByDepth adj P b` for any `b ≥ |T k|`. Witness set = the cumulative `T k`;
`cellsAreOrbits_of_discrete` turns discreteness into `CellsAreOrbits`. This lands the harvest-window's
*stated conclusion* on the existing composition machinery, isolating `hwit` (= the screen-supplies-
witnesses bridge) as the sole residual. -/
theorem recoverableByDepth_of_pathFixing_layers {k : Nat}
    (T : Nat → Finset (Fin n)) (S : Nat → Finset (Fin n)) {b : Nat}
    (hT : ∀ i, i < k → T (i + 1) = T i ∪ S i)
    (hbase : CellsAreOrbits adj P (T 0))
    (hwit : ∀ i, i < k → ∀ v w, OrbitPartition adj P (T i) v w →
      warmRefine adj P (individualizedColouring n (T i ∪ S i)) v
        = warmRefine adj P (individualizedColouring n (T i ∪ S i)) w →
      ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u)
        ∧ Disjoint (T i ∪ S i) π.support ∧ π v = w)
    (hbaseSet : IsBase adj P (T k))
    (hb : (T k).card ≤ b) :
    RecoverableByDepth adj P b :=
  ⟨T k, hb, cellsAreOrbits_of_discrete
    (cascadeComposition_pathFixing T S hT hbase hwit hbaseSet)⟩

/-- **CFI corollary.** The harvest-window conclusion for CFI layers: `RecoverableByDepth adj P b` for any
`b ≥ |T k|`, given per-layer committed-set-avoiding gadget flips (`CFILayerGadgetFlippable`). The CFI
instance of `recoverableByDepth_of_pathFixing_layers`, conditional only on the (cascade-1b) per-layer
cycle existence. -/
theorem recoverableByDepth_of_cascadeComposition_cfi (h : IsCFI' adj) {k : Nat} {b : Nat}
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (T : Nat → Finset (Fin n)) (S : Nat → Finset (Fin n))
    (hT : ∀ i, i < k → T (i + 1) = T i ∪ S i)
    (hbase : CellsAreOrbits adj P (T 0))
    (hflip : CFILayerGadgetFlippable (P := P) h k T S)
    (hbaseSet : IsBase adj P (T k))
    (hb : (T k).card ≤ b) :
    RecoverableByDepth adj P b :=
  ⟨T k, hb, cellsAreOrbits_of_discrete (cascadeComposition_cfi h hP T S hT hbase hflip hbaseSet)⟩

/-! ## Screen predicate D2 — abelian residual (the harvest-window screen, leg B)

The harvest-window screen ([`docs/chain-descent-harvest-window.md`](../../../docs/chain-descent-harvest-window.md)
§3) is the seal's negation-complete `D1 ∨ D2`. This section defines **D2**, the *unique-candidate /
abelian* leg: the residual symmetry (the `P`-preserving automorphisms fixing the committed set `S`
pointwise) forms an **abelian** group. By the calculator's §6 boundary, abelian ⟺ each apparent
decision exposes a *unique* candidate twist — exactly the regime the linear oracle reads. Its negation
(non-abelian residual) is the Johnson / `Aₖ` fingerprint that leg C consumes.

Stated **relative to `S`** deliberately: CFI's *full* `Aut = Z₂^β ⋊ Aut(H)` is non-abelian, but once `S`
fixes the `Aut(H)` part the residual `Z₂^β` is abelian — so D2 holds at the committed sets the descent
actually reaches, not at the root. (D1 — the visible/cascade leg — is the companion, to follow.) -/

/-- **Residual automorphism.** A `P`-preserving automorphism of `adj` fixing `S` pointwise — the
elements of the residual group `Aut_S^P`. `OrbitPartition adj P S v w` is exactly
`∃ π, ResidualAut adj P S π ∧ π v = w` (`orbitPartition_iff_residualAut`). The reusable building block
for the screen predicates. -/
def ResidualAut (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u) ∧ FixesPointwise π S

/-- **D2 — abelian residual.** The residual group `Aut_S^P` is abelian: any two residual automorphisms
commute. The harvest-window screen's *unique-candidate / linear* leg (⟺ abelian, calculator §6); its
negation is the leg-C Johnson fingerprint. Relative to `S` (see section note). -/
def ResidualAbelian (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) : Prop :=
  ∀ π₁ π₂ : Equiv.Perm (Fin n),
    ResidualAut adj P S π₁ → ResidualAut adj P S π₂ → π₁ * π₂ = π₂ * π₁

/-- `OrbitPartition` unfolds to a `ResidualAut` carrying `v ↦ w`. -/
theorem orbitPartition_iff_residualAut {S : Finset (Fin n)} {v w : Fin n} :
    OrbitPartition adj P S v w ↔ ∃ π, ResidualAut adj P S π ∧ π v = w := by
  unfold OrbitPartition ResidualAut
  constructor
  · rintro ⟨π, h1, h2, h3, h4⟩; exact ⟨π, ⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨π, ⟨h1, h2, h3⟩, h4⟩; exact ⟨π, h1, h2, h3, h4⟩

/-! ## Leg B (de-classing) — the involutive (D2) swap certificate

The linear oracle (Leg B, hidden-abelian) was designed early, before the recovery framework, so
its completeness routed per-class through CFI gadget involutions (`cfiFlipAut_swaps_endpointVertex`,
`CFIParityDecisionFlippable`) and left the abstract D2 predicate `ResidualAbelian` orphaned. The
class-agnostic content the per-class route hard-codes is: **the orbit automorphism witnessing a
decision pair is automatically a *swap* `g a = b ∧ g b = a` when the residual is exponent-2** (every
element an involution — precisely CFI's `Z₂^β` gauge group). `ResidualAbelian` (commuting) is *not*
enough for that; the precise predicate is `ResidualInvolutive` below, and it implies `ResidualAbelian`.

This produces the **swap** the config-swap constructors (`configSwap_of_aut`/`_of_swap`,
`LinearOracle.lean`) consume as their first input, class-agnostically and via the recovery machinery
(`CellsAreOrbits`) — *no* gadget cycle, *no* `tw(H)`, *no* σ-coherence. (Connecting this swap to the
order-model `ConfigSwap`'s remaining coherence — `fixesχι` + off-pair σ-preservation — is the separate
§0.4 model-gap step, not closed here.) -/

/-- **The residual group is closed under composition.** Composition of `P`-preserving
automorphisms fixing `S` pointwise is again one. -/
theorem ResidualAut.mul {S : Finset (Fin n)} {π₁ π₂ : Equiv.Perm (Fin n)}
    (h₁ : ResidualAut adj P S π₁) (h₂ : ResidualAut adj P S π₂) :
    ResidualAut adj P S (π₁ * π₂) := by
  obtain ⟨hA₁, hP₁, hF₁⟩ := h₁
  obtain ⟨hA₂, hP₂, hF₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · intro v w; simp only [Equiv.Perm.mul_apply]; rw [hA₁, hA₂]
  · intro x u; simp only [Equiv.Perm.mul_apply]; rw [hP₁, hP₂]
  · intro v hv; rw [Equiv.Perm.mul_apply, hF₂ v hv, hF₁ v hv]

/-- **D2, the precise (exponent-2) form.** Every residual automorphism is an involution — the
residual group has exponent ≤ 2, i.e. is an elementary-abelian `Z₂^d` (CFI's gauge group). This is
the form of D2 the swap content needs: `ResidualAbelian` (commuting) does *not* give involutions.
See `residualAbelian_of_involutive` (it *implies* the abelian predicate) and
`orbitPartition_swap_of_involutive` (it turns an orbit *map* into a *swap*). -/
def ResidualInvolutive (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) : Prop :=
  ∀ π : Equiv.Perm (Fin n), ResidualAut adj P S π → π * π = 1

/-- **Exponent-2 ⟹ abelian** (the classic group fact), wiring the orphaned `ResidualAbelian`
predicate to the precise `ResidualInvolutive`: a residual group of involutions commutes. -/
theorem residualAbelian_of_involutive {S : Finset (Fin n)}
    (hinv : ResidualInvolutive adj P S) : ResidualAbelian adj P S := by
  intro π₁ π₂ h₁ h₂
  have e1 : π₁⁻¹ = π₁ := inv_eq_of_mul_eq_one_right (hinv _ h₁)
  have e2 : π₂⁻¹ = π₂ := inv_eq_of_mul_eq_one_right (hinv _ h₂)
  have e12 : (π₁ * π₂)⁻¹ = π₁ * π₂ := inv_eq_of_mul_eq_one_right (hinv _ (h₁.mul h₂))
  rw [mul_inv_rev, e1, e2] at e12
  exact e12.symm

/-- **An involutive orbit witness is a swap.** Closing the map-vs-swap gap class-agnostically: if the
residual is exponent-2 (`ResidualInvolutive`) and `a, b` are an orbit pair, the witnessing residual
automorphism `g` satisfies `g a = b` **and** `g b = a` (from `g (g a) = a`). This is what the CFI
route obtains from gadget involutions — here from the abstract `Z₂^d` structure. -/
theorem orbitPartition_swap_of_involutive {S : Finset (Fin n)} {a b : Fin n}
    (hinv : ResidualInvolutive adj P S) (h : OrbitPartition adj P S a b) :
    ∃ g, ResidualAut adj P S g ∧ g a = b ∧ g b = a := by
  rw [orbitPartition_iff_residualAut] at h
  obtain ⟨g, hg, hgab⟩ := h
  refine ⟨g, hg, hgab, ?_⟩
  have h2 : (g * g) a = (1 : Equiv.Perm (Fin n)) a := by rw [hinv g hg]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h2
  rw [hgab] at h2
  exact h2

/-- **The class-agnostic swap certificate at a recoverable node.** Where orbit recovery holds
(`CellsAreOrbits`) and the residual is exponent-2 (`ResidualInvolutive`), every same-cell decision
pair `{a, b}` carries a **swapping** orbit automorphism (`g a = b ∧ g b = a`). This is the firing
certificate's symmetry half — the linear oracle's "a swap exists" input — produced from recovery + D2,
replacing the per-class `CFIGadgetFlippable`/`cfiGadgetFlippableLocal_of_parity` derivation. -/
theorem swap_of_cellsAreOrbits_involutive {S : Finset (Fin n)} {a b : Fin n}
    (hco : CellsAreOrbits adj P S) (hinv : ResidualInvolutive adj P S)
    (hcell : warmRefine adj P (individualizedColouring n S) a
           = warmRefine adj P (individualizedColouring n S) b) :
    ∃ g, ResidualAut adj P S g ∧ g a = b ∧ g b = a :=
  orbitPartition_swap_of_involutive hinv (hco a b hcell)

/-- **Under a base, every residual automorphism is the identity.** `IsBase adj P S` says the
`Aut_S`-orbit relation is equality, so a residual auto cannot move any point: it fixes everything,
hence is `1`. -/
theorem residualAut_eq_one_of_isBase {S : Finset (Fin n)} {π : Equiv.Perm (Fin n)}
    (hbase : IsBase adj P S) (hπ : ResidualAut adj P S π) : π = 1 := by
  refine Equiv.ext (fun v => ?_)
  show π v = v
  exact (hbase v (π v) ⟨π, hπ.1, hπ.2.1, hπ.2.2, rfl⟩).symm

/-- **Base case of the trichotomy: a trivial residual is abelian.** When `S` is a base, the residual
group is `{1}`, vacuously abelian. This is the recursion bottom — `D2` holds for free at discreteness. -/
theorem residualAbelian_of_isBase {S : Finset (Fin n)} (hbase : IsBase adj P S) :
    ResidualAbelian adj P S := by
  intro π₁ π₂ h₁ h₂
  rw [residualAut_eq_one_of_isBase hbase h₁, residualAut_eq_one_of_isBase hbase h₂]

/-- **D2 is inherited as the committed set grows.** Fixing *more* points (`S ⊆ S'`) shrinks the
residual group to a subgroup, and a subgroup of an abelian group is abelian. So `ResidualAbelian` passes
*down* the descent chain — once abelian at a node, abelian at every deeper node. -/
theorem residualAbelian_mono {S S' : Finset (Fin n)} (h : ResidualAbelian adj P S)
    (hSS' : S ⊆ S') : ResidualAbelian adj P S' := by
  intro π₁ π₂ h₁ h₂
  exact h π₁ π₂ ⟨h₁.1, h₁.2.1, fun v hv => h₁.2.2 v (hSS' hv)⟩
    ⟨h₂.1, h₂.2.1, fun v hv => h₂.2.2 v (hSS' hv)⟩

/-! ## Part A (Stage A1) — the residual group `Aut_S^P` as a `Subgroup`

The path-fixing residual `ResidualAut adj P S` is the carrier of an honest Mathlib `Subgroup`,
`StabilizerAt adj P S`. This packages the scattered predicate-level residual reasoning as a group
object — the bottom layer of the stabilizer-chain / Schreier–Sims buildout
([`docs/chain-descent-schreier-sims.md`](../../../docs/chain-descent-schreier-sims.md), Stage A1). It
consolidates `ResidualAut.mul` (closure), `residualAut_eq_one_of_isBase` (base ⟺ trivial), and the
`FixesPointwise`-monotonicity into subgroup form, and exposes `MulAction.orbit` per node (generalizing
`Group.lean`'s root bridge `mem_orbit_autGroup_iff_orbitPartition` off `S = ∅`). -/

/-- **The residual group `Aut_S^P` as a `Subgroup`.** Carrier: the `P`-preserving automorphisms fixing
`S` pointwise (`ResidualAut adj P S`). Closure is `ResidualAut.mul`; identity and inverses are direct.
The group object underlying the stabilizer chain; `StabilizerAt adj P ∅` is the ambient `P`-preserving
automorphism group (`mem_stabilizerAt_empty`). -/
def StabilizerAt (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | ResidualAut adj P S π}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := fun ha hb => ResidualAut.mul ha hb
  inv_mem' := by
    intro a ha
    obtain ⟨hA, hP, hF⟩ := ha
    have hax : ∀ y, a (a⁻¹ y) = y := fun y => by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    refine ⟨IsAut.symm hA, ?_, ?_⟩
    · intro x u
      have h := hP (a⁻¹ x) (a⁻¹ u)
      rw [hax, hax] at h
      exact h.symm
    · intro v hv
      have hav := hF v hv
      calc a⁻¹ v = a⁻¹ (a v) := by rw [hav]
        _ = (a⁻¹ * a) v := (Equiv.Perm.mul_apply a⁻¹ a v).symm
        _ = v := by rw [inv_mul_cancel, Equiv.Perm.one_apply]

@[simp] theorem mem_stabilizerAt {S : Finset (Fin n)} {π : Equiv.Perm (Fin n)} :
    π ∈ StabilizerAt adj P S ↔ ResidualAut adj P S π := Iff.rfl

/-- The subgroup action's `smul` is application of the underlying permutation (as for `AutGroup`). -/
@[simp] theorem stabilizerAt_smul {S : Finset (Fin n)} (g : StabilizerAt adj P S) (v : Fin n) :
    g • v = (g : Equiv.Perm (Fin n)) v := rfl

/-- **Root = the ambient `P`-preserving automorphism group.** `FixesPointwise π ∅` is vacuous, so
`StabilizerAt adj P ∅` is exactly the `P`-preserving automorphisms of `adj`. -/
theorem mem_stabilizerAt_empty {π : Equiv.Perm (Fin n)} :
    π ∈ StabilizerAt adj P ∅ ↔ IsAut π adj ∧ ∀ x u, P (π x) (π u) = P x u := by
  rw [mem_stabilizerAt]
  exact ⟨fun ⟨hA, hP, _⟩ => ⟨hA, hP⟩,
    fun ⟨hA, hP⟩ => ⟨hA, hP, fun v hv => absurd hv (Finset.notMem_empty v)⟩⟩

/-- **Monotonicity (stabilizer containment).** Fixing *more* points gives a *smaller* group:
`S ⊆ S' → StabilizerAt adj P S' ≤ StabilizerAt adj P S`. The subgroup form of `OrbitPartition.mono`. -/
theorem stabilizerAt_mono {S S' : Finset (Fin n)} (h : S ⊆ S') :
    StabilizerAt adj P S' ≤ StabilizerAt adj P S := by
  intro π hπ
  obtain ⟨hA, hP, hF⟩ := hπ
  exact ⟨hA, hP, fun v hv => hF v (h hv)⟩

/-- **`StabilizerAt = ⊥ ⟺ base.** The chain's bottom: the residual group is trivial exactly when `S`
is a base (`IsBase`). Forward via `Subgroup.mem_bot`; backward via `residualAut_eq_one_of_isBase`. -/
theorem stabilizerAt_eq_bot_iff_isBase {S : Finset (Fin n)} :
    StabilizerAt adj P S = ⊥ ↔ IsBase adj P S := by
  constructor
  · intro h v w hvw
    obtain ⟨π, hres, hπvw⟩ := orbitPartition_iff_residualAut.mp hvw
    have hmem : π ∈ StabilizerAt adj P S := hres
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem] at hπvw
    simpa using hπvw
  · intro hbase
    rw [Subgroup.eq_bot_iff_forall]
    intro π hπ
    exact residualAut_eq_one_of_isBase hbase hπ

/-- **Per-node orbit bridge.** `v`'s orbit under `StabilizerAt adj P S` is exactly the `OrbitPartition`
relation at `S` — generalizing `Group.lean`'s root bridge `mem_orbit_autGroup_iff_orbitPartition` off
`S = ∅`. So `MulAction.orbit (StabilizerAt …)` *is* the working orbit relation, with the group element
available. -/
theorem mem_orbit_stabilizerAt_iff {S : Finset (Fin n)} {v w : Fin n} :
    w ∈ MulAction.orbit (StabilizerAt adj P S) v ↔ OrbitPartition adj P S v w := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hA, hP, hF⟩ := g.2
    exact ⟨(g : Equiv.Perm (Fin n)), hA, hP, hF, by simpa using hg⟩
  · rintro ⟨π, hA, hP, hF, hvw⟩
    exact ⟨⟨π, hA, hP, hF⟩, by simpa using hvw⟩

/-! ## Part A (Stage A2) — the cross-branch harvest seam (soundness)

The descent harvests automorphisms **cross-branch**: when two branches reach the same leaf, the
relabelling between them is an automorphism (verified edge-by-edge), folded into the residual group
(`AddGenerator`); a folded generator that fixes the committed path then **prunes** sibling branches
(`CoveredByPathFixingAut`). The Lean side of that seam, on top of `StabilizerAt` (Stage A1):

* **Fold-in is sound** — a verified path-fixing automorphism is a member of `StabilizerAt S`
  (`residualAut_mem_stabilizerAt`), and the whole harvested chain `Subgroup.closure gens` stays **inside**
  the true residual `Aut_S^P` (`closure_le_stabilizerAt`): the chain only ever records genuine
  path-fixing automorphisms.
* **Consumption is sound** — a candidate `v` lying in the orbit of an explored `w` under any subgroup
  `≤ StabilizerAt S` is genuinely `Aut_S^P`-orbit-equivalent to `w` (`orbit_pathFixing_sound`), so
  pruning `v`'s branch as isomorphic to `w`'s is sound (`covered_sound`).

This is the mechanism the discretizing-oracle limit (`CascadeOracle.lean §C.8`,
`lockstep_disc_imp_stab_trivial`) showed is *required* for multi-step hidden symmetry: it is harvested
here, cross-branch, not by the within-cell colour-match.
([`docs/chain-descent-schreier-sims.md`](../../../docs/chain-descent-schreier-sims.md), Stage A2.) -/

/-- **Fold-in entry.** A verified `P`-preserving automorphism fixing `S` pointwise is a member of the
residual group `StabilizerAt adj P S` — the harness's `AddGenerator` precondition, abstractly. -/
theorem residualAut_mem_stabilizerAt {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (h : ResidualAut adj P S g) : g ∈ StabilizerAt adj P S := h

/-- **The harvested chain stays inside the true residual (soundness).** If every harvested generator is
a verified path-fixing automorphism (`ResidualAut adj P S`), the subgroup they generate is contained in
`StabilizerAt adj P S`. So the accumulated group never contains a non-automorphism or a non-path-fixing
element — the "over-split sound, under-merge not" contract, group side. -/
theorem closure_le_stabilizerAt {S : Finset (Fin n)} {gens : Set (Equiv.Perm (Fin n))}
    (hgens : ∀ g ∈ gens, ResidualAut adj P S g) :
    Subgroup.closure gens ≤ StabilizerAt adj P S :=
  (Subgroup.closure_le _).mpr (fun g hg => hgens g hg)

/-- **Consumption soundness (the orbit prune).** For any subgroup `H ≤ StabilizerAt adj P S`, if `v` is
in the `H`-orbit of `w` then `v` and `w` are genuinely `Aut_S^P`-orbit-equivalent (`OrbitPartition`). So
a folded-in chain (which is `≤ StabilizerAt` by `closure_le_stabilizerAt`) only ever prunes branches that
are truly isomorphic — the soundness of `CoveredByPathFixingAut`. -/
theorem orbit_pathFixing_sound {H : Subgroup (Equiv.Perm (Fin n))} {S : Finset (Fin n)}
    (hHle : H ≤ StabilizerAt adj P S) {v w : Fin n}
    (hv : v ∈ MulAction.orbit H w) : OrbitPartition adj P S w v := by
  rw [← mem_orbit_stabilizerAt_iff]
  obtain ⟨g, hg⟩ := hv
  exact ⟨⟨(g : Equiv.Perm (Fin n)), hHle g.2⟩, by simpa using hg⟩

/-- **Covered ⟹ sound prune (capstone).** A candidate `v` in the orbit of an explored `w` under the
subgroup generated by verified path-fixing harvested automorphisms is genuinely `Aut_S^P`-equivalent to
`w`, so dropping `v`'s subtree as isomorphic to `w`'s is sound. The `CoveredByPathFixingAut` soundness,
assembled from `closure_le_stabilizerAt` + `orbit_pathFixing_sound`. -/
theorem covered_sound {S : Finset (Fin n)} {gens : Set (Equiv.Perm (Fin n))}
    (hgens : ∀ g ∈ gens, ResidualAut adj P S g) {v w : Fin n}
    (hv : v ∈ MulAction.orbit (Subgroup.closure gens) w) :
    OrbitPartition adj P S w v :=
  orbit_pathFixing_sound (closure_le_stabilizerAt hgens) hv

/-! ## Part A (Stage A3) — order and the rigid/Cameron verdict

With `Aut_S^P` a `Subgroup` (Stage A1) its **order** `Nat.card (StabilizerAt adj P S)` is a finite,
meaningful quantity. Two payoffs:

* **The rigid verdict** (`card_stabilizerAt_eq_one_iff_isBase`): the residual is trivial (order 1)
  **iff** `S` is a base — i.e. the descent has reached a rigid node. Its negation (`≠ 1`) is the
  non-rigid / Tier-2-like side (a non-trivial residual; classifying it as a Cameron section is
  Cameron-hard, out of scope — but "residual non-trivial" is now a precise predicate). This is the Lean
  form of the flag diagnostic (`CanonGraphOrdererChainDescent.cs`: `Tier2Like` vs `IrBlindSpot`).
* **The order recursion** (`card_stabilizerAt_eq_orbit_mul`): `|Aut_S^P| = |orbit of b| · |Aut_{S∪{b}}^P|`
  — the inductive step of `order = ∏ basic-orbit sizes`, via Mathlib's orbit–stabilizer
  (`Subgroup.card_mul_index` + `index_stabilizer`) plus the carrier match `stabilizer(Aut_S^P, b) =
  Aut_{insert b S}^P` (`subgroupOf_insert_eq_stabilizer`). Assembling the full product over a base
  sequence is the thin Stage-A4 layer.
([`docs/chain-descent-schreier-sims.md`](../../../docs/chain-descent-schreier-sims.md), Stage A3.) -/

/-- The residual group is finite (a subgroup of `Equiv.Perm (Fin n)`), so its order is positive. -/
theorem card_stabilizerAt_pos {S : Finset (Fin n)} : 0 < Nat.card (StabilizerAt adj P S) :=
  Nat.card_pos

/-- **The rigid verdict.** The residual group is trivial (order 1) **iff** `S` is a base. So
`Nat.card (StabilizerAt adj P S) = 1` is exactly "the descent is rigid at `S`"; `≠ 1` is the non-rigid
(Tier-2-like) residual. Composes `Subgroup.eq_bot_iff_card` with `stabilizerAt_eq_bot_iff_isBase`. -/
theorem card_stabilizerAt_eq_one_iff_isBase {S : Finset (Fin n)} :
    Nat.card (StabilizerAt adj P S) = 1 ↔ IsBase adj P S := by
  rw [← Subgroup.eq_bot_iff_card, stabilizerAt_eq_bot_iff_isBase]

/-- **The chain carrier match.** Inside the residual group `Aut_S^P`, the stabilizer of a point `b` is
exactly `Aut_{insert b S}^P` (adding `b` to the base): a residual fixing `S` and `b` fixes `insert b S`.
The bridge for the order recursion. -/
theorem subgroupOf_insert_eq_stabilizer (b : Fin n) {S : Finset (Fin n)} :
    (StabilizerAt adj P (insert b S)).subgroupOf (StabilizerAt adj P S)
      = MulAction.stabilizer (StabilizerAt adj P S) b := by
  ext x
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, mem_stabilizerAt, stabilizerAt_smul]
  constructor
  · intro hres
    exact hres.2.2 b (Finset.mem_insert_self b S)
  · intro hxb
    obtain ⟨hA, hP, hF⟩ := x.2
    exact ⟨hA, hP, fun v hv => (Finset.mem_insert.mp hv).elim (fun h => h.symm ▸ hxb) (fun h => hF v h)⟩

/-- The point-stabilizer inside `Aut_S^P` has the same order as `Aut_{insert b S}^P`
(`subgroupOf_insert_eq_stabilizer` + `subgroupOfEquivOfLe`). -/
theorem card_stabilizer_eq (b : Fin n) {S : Finset (Fin n)} :
    Nat.card (MulAction.stabilizer (StabilizerAt adj P S) b)
      = Nat.card (StabilizerAt adj P (insert b S)) := by
  rw [← subgroupOf_insert_eq_stabilizer]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (stabilizerAt_mono (Finset.subset_insert b S))).toEquiv

/-- **The order recursion (one chain level).** `|Aut_S^P| = |orbit of b under Aut_S^P| · |Aut_{insert b
S}^P|` — the inductive step of `order = ∏ basic-orbit sizes`, from Mathlib's orbit–stabilizer
(`Subgroup.card_mul_index` + `index_stabilizer`) and the carrier match `card_stabilizer_eq`. -/
theorem card_stabilizerAt_eq_orbit_mul (b : Fin n) {S : Finset (Fin n)} :
    Nat.card (StabilizerAt adj P S)
      = (MulAction.orbit (StabilizerAt adj P S) b).ncard
        * Nat.card (StabilizerAt adj P (insert b S)) := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (StabilizerAt adj P S) b)
  rw [MulAction.index_stabilizer, card_stabilizer_eq] at h1
  rw [← h1]; ring

/-! ### Part A (Stage A3.5) — the full order product over a base sequence

`card_stabilizerAt_eq_orbit_mul` is one chain level. Telescoping it over an ordered **base sequence**
gives `order = ∏ basic-orbit sizes` — the abstract counterpart of `PermutationGroup.cs`'s
`Order = ∏ level.OrbitSize`. This needs **no** computable BSGS (it is pure induction on the per-level
recursion), so it is separated out of Stage A4: the order story / `Aut(G)`-as-a-byproduct lands at the
abstract layer, and the concrete `Level`/transversal structure is needed only for *computing* the
product, not for the identity. -/

/-- **The basic-orbit-size product along a base sequence.** Consuming `bs` from the individualized set
`S`: each `b` contributes the size of its orbit under the *current* residual `Aut_S^P`, then the residual
descends to `Aut_{insert b S}^P` for the tail. The right-hand side of `order = ∏ basic-orbit sizes`. -/
noncomputable def orbitSizeProd (adj : AdjMatrix n) (P : PMatrix n) :
    List (Fin n) → Finset (Fin n) → Nat
  | [], _ => 1
  | b :: bs, S => (MulAction.orbit (StabilizerAt adj P S) b).ncard * orbitSizeProd adj P bs (insert b S)

/-- **`order = ∏ basic-orbit sizes` — the telescoping identity.** For *any* sequence `bs`,
`|Aut_S^P|` equals the product of basic-orbit sizes along `bs` times the residual order at the
fully-accumulated set. Induction on `bs` via `card_stabilizerAt_eq_orbit_mul`; no computable BSGS. -/
theorem card_stabilizerAt_eq_prod (bs : List (Fin n)) (S : Finset (Fin n)) :
    Nat.card (StabilizerAt adj P S)
      = orbitSizeProd adj P bs S
        * Nat.card (StabilizerAt adj P (bs.foldl (fun s b => insert b s) S)) := by
  induction bs generalizing S with
  | nil => simp [orbitSizeProd]
  | cons b bs ih =>
    simp only [orbitSizeProd, List.foldl_cons]
    rw [card_stabilizerAt_eq_orbit_mul b (S := S), ih (insert b S)]
    ring

/-- **`order = ∏ basic-orbit sizes` at a base.** When the accumulated set `bs.foldl … S` is a base, the
trailing residual is trivial (order 1, `card_stabilizerAt_eq_one_iff_isBase`), so `|Aut_S^P|` is exactly
the product of basic-orbit sizes — the abstract `Order = ∏ OrbitSize` of `PermutationGroup.cs`, with no
computable BSGS. -/
theorem card_stabilizerAt_eq_prod_of_base (bs : List (Fin n)) (S : Finset (Fin n))
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Nat.card (StabilizerAt adj P S) = orbitSizeProd adj P bs S := by
  rw [card_stabilizerAt_eq_prod bs S, card_stabilizerAt_eq_one_iff_isBase.mpr hbase, mul_one]

/-- **`Aut(G)^P` as a byproduct: its order is `∏ basic-orbit sizes`.** The `S = ∅` headline of
`card_stabilizerAt_eq_prod_of_base`: `StabilizerAt adj P ∅` is the whole `P`-preserving automorphism
group (`mem_stabilizerAt_empty`), so a base sequence `bs` from `∅` reads off `|Aut(G)^P|` as the orbit-size
product — computing the canonical form yields the group order for free (strategy §6, the chain). -/
theorem card_autP_eq_prod_of_base (bs : List (Fin n))
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) ∅)) :
    Nat.card (StabilizerAt adj P ∅) = orbitSizeProd adj P bs ∅ :=
  card_stabilizerAt_eq_prod_of_base bs ∅ hbase

/-! ### Part A (Stage A2-complete) — the cross-branch harvest *completeness* seam

Stage A2 proved harvest **soundness** (`closure_le_stabilizerAt`: the folded chain stays `⊆ StabilizerAt`).
This is the **dual** — that the harvested generators *generate* the residual — the property the multi-step
conservation finding (`lockstep_disc_imp_stab_trivial`) redirected the project to.

**Why the realizers must be path-fixing (the genuine reduction).** A naive "every orbit element is realized
by *some* element of `closure gens`" is *circular*: since the residual shrinks down the base
(`StabilizerAt S ≤ StabilizerAt ∅`), `closure gens = StabilizerAt ∅` already realizes every deeper orbit, so
that condition is equivalent to the conclusion. The honest content is the classical **strong generating set**
condition: at level `S` the realizer must come from the *path-fixing* generators `gensAt adj P gens S`
(the subset of `gens` lying in `StabilizerAt adj P S`), whose closure can be a *proper* subgroup of
`StabilizerAt S` even when `gens` generate the top group — exactly what sifting/Schreier generators exist to
establish, and exactly what the per-level path-fixing harvest (`CoveredByPathFixingAut`) supplies.

Iterated down a base sequence, this **coverage witness** (`CoversOrbits`) gives
`closure (gensAt … S) = StabilizerAt S`, hence `closure gens = StabilizerAt ∅` at the root; with Stage A3.5
the harvested chain reproduces both the residual **group** and its **order** `= ∏ basic-orbit sizes`.
([`docs/chain-descent-schreier-sims.md`](../../../docs/chain-descent-schreier-sims.md), Stage A2-complete.) -/

/-- **Path-fixing generators at `S`.** The subset of `gens` lying in `StabilizerAt adj P S` (i.e. fixing the
committed path `S` pointwise). The strong-generating-set machinery realizes each level's orbit from *these*,
not from the full `closure gens` — see the section note on why that distinction is the genuine content. -/
def gensAt (adj : AdjMatrix n) (P : PMatrix n) (gens : Set (Equiv.Perm (Fin n)))
    (S : Finset (Fin n)) : Set (Equiv.Perm (Fin n)) :=
  {g | g ∈ gens ∧ g ∈ StabilizerAt adj P S}

/-- The path-fixing generators shrink as the path grows: `S ⊆ S' → gensAt … S' ⊆ gensAt … S`
(fixing more points is a stronger condition), via `stabilizerAt_mono`. -/
theorem gensAt_anti {gens : Set (Equiv.Perm (Fin n))} {S S' : Finset (Fin n)} (h : S ⊆ S') :
    gensAt adj P gens S' ⊆ gensAt adj P gens S :=
  fun _ hg => ⟨hg.1, stabilizerAt_mono h hg.2⟩

/-- The closure of the path-fixing generators is inside the residual (soundness, intrinsic to `gensAt`). -/
theorem closure_gensAt_le_stabilizerAt {gens : Set (Equiv.Perm (Fin n))} {S : Finset (Fin n)} :
    Subgroup.closure (gensAt adj P gens S) ≤ StabilizerAt adj P S :=
  (Subgroup.closure_le _).mpr (fun _ hg => hg.2)

/-- Monotonicity of the path-fixing closure: `S ⊆ S' → closure (gensAt … S') ≤ closure (gensAt … S)`.
The step that makes the completeness induction descend the base. -/
theorem closure_gensAt_anti {gens : Set (Equiv.Perm (Fin n))} {S S' : Finset (Fin n)} (h : S ⊆ S') :
    Subgroup.closure (gensAt adj P gens S') ≤ Subgroup.closure (gensAt adj P gens S) :=
  Subgroup.closure_mono (gensAt_anti h)

/-- At the empty path the path-fixing condition is vacuous, so `gensAt … ∅ = gens` once every generator is
a `P`-preserving automorphism (the Stage-A2 soundness hypothesis, here as `∈ StabilizerAt ∅`). -/
theorem gensAt_empty_eq {gens : Set (Equiv.Perm (Fin n))}
    (hsound : ∀ g ∈ gens, g ∈ StabilizerAt adj P ∅) : gensAt adj P gens ∅ = gens := by
  ext g; exact ⟨fun h => h.1, fun h => ⟨h, hsound g h⟩⟩

/-- **The one-level completeness core (strong-generation step).** If the *path-fixing* closure at the next
level contains `StabilizerAt adj P (insert b S)`, and the path-fixing closure at `S` **realizes the full
`Aut_S^P`-orbit of `b`**, then it already contains the whole residual `StabilizerAt adj P S`. The dual of
`closure_le_stabilizerAt`. Proof: for `g ∈ StabilizerAt S`, pick `h ∈ closure (gensAt … S)` with `h b = g b`;
then `h⁻¹ * g` fixes `b`, lies in `StabilizerAt (insert b S) ≤ closure (gensAt … (insert b S)) ≤
closure (gensAt … S)`, so `g = h * (h⁻¹ * g) ∈ closure (gensAt … S)`. The `≤ closure (gensAt … S)` step is
`closure_gensAt_anti` — where the path-fixing form (not the full `closure gens`) is essential. -/
theorem stabilizerAt_le_closure_gensAt_step {gens : Set (Equiv.Perm (Fin n))} {S : Finset (Fin n)}
    (b : Fin n)
    (hstab : StabilizerAt adj P (insert b S) ≤ Subgroup.closure (gensAt adj P gens (insert b S)))
    (hreal : ∀ w, OrbitPartition adj P S b w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h b = w) :
    StabilizerAt adj P S ≤ Subgroup.closure (gensAt adj P gens S) := by
  intro g hg
  have hgr : ResidualAut adj P S g := mem_stabilizerAt.mp hg
  obtain ⟨h, hhcl, hhb⟩ := hreal (g b) (orbitPartition_iff_residualAut.mpr ⟨g, hgr, rfl⟩)
  have hhS : h ∈ StabilizerAt adj P S := closure_gensAt_le_stabilizerAt hhcl
  have hfixb : (h⁻¹ * g) b = b := by
    rw [Equiv.Perm.mul_apply, ← hhb, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  have hmemS : h⁻¹ * g ∈ StabilizerAt adj P S := mul_mem (inv_mem hhS) hg
  obtain ⟨hA, hP, hF⟩ := mem_stabilizerAt.mp hmemS
  have hins : h⁻¹ * g ∈ StabilizerAt adj P (insert b S) :=
    mem_stabilizerAt.mpr ⟨hA, hP, by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvS
      · exact hfixb
      · exact hF v hvS⟩
  have hdeep : h⁻¹ * g ∈ Subgroup.closure (gensAt adj P gens S) :=
    closure_gensAt_anti (Finset.subset_insert b S) (hstab hins)
  have hmul : h * (h⁻¹ * g) ∈ Subgroup.closure (gensAt adj P gens S) := mul_mem hhcl hdeep
  rwa [mul_inv_cancel_left] at hmul

/-- **Orbit-coverage along a base sequence (the harvest's strong-generating-set witness).** Consuming `bs`
from `S`: at the head `b`, the **path-fixing** generators' closure `closure (gensAt … S)` realizes the full
`Aut_S^P`-orbit of `b`, then the same recursively at `insert b S`; the empty tail requires `S` a base. The
honest analog of the within-cell depth witness — the per-level path-fixing harvest (`CoveredByPathFixingAut`,
strategy §4 step 6) supplies it; class-conditional, not unconditional (multi-step CFI bounded-`tw` is the
witness). Genuinely *stronger* than "`gens` generate the top group" — see the section note. -/
def CoversOrbits (adj : AdjMatrix n) (P : PMatrix n) (gens : Set (Equiv.Perm (Fin n))) :
    List (Fin n) → Finset (Fin n) → Prop
  | [], S => IsBase adj P S
  | b :: bs, S =>
      (∀ w, OrbitPartition adj P S b w →
          ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h b = w)
        ∧ CoversOrbits adj P gens bs (insert b S)

/-- **Coverage step from path-fixing realizers (the harvest interface).** If the path-fixing *generators*
themselves (`gensAt … S`, not merely their closure) realize `b`'s full orbit, the coverage clause holds —
the realizers land in `closure (gensAt … S)` via `Subgroup.subset_closure`. This is the hook concrete
gauge-generator work (CFI / schemes) plugs into: exhibit, among the path-fixing harvested generators at `S`,
one mapping `b` to each orbit-mate. (`swap_of_cellsAreOrbits_involutive` produces such automorphisms for the
involutive/`Z₂^β` case; whether they are *in* `gens` is the harvest-collection content.) -/
theorem coversOrbits_realize_of_mem {gens : Set (Equiv.Perm (Fin n))} {S : Finset (Fin n)} {b : Fin n}
    (hreal : ∀ w, OrbitPartition adj P S b w → ∃ h ∈ gensAt adj P gens S, h b = w) :
    ∀ w, OrbitPartition adj P S b w → ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h b = w :=
  fun w hw => let ⟨h, hmem, hb⟩ := hreal w hw; ⟨h, Subgroup.subset_closure hmem, hb⟩

/-- The terminal accumulated set of a coverage witness is a base (matches A3.5's `foldl`). -/
theorem coversOrbits_isBase_foldl {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n))
    {S : Finset (Fin n)} (hcov : CoversOrbits adj P gens bs S) :
    IsBase adj P (bs.foldl (fun s b => insert b s) S) := by
  induction bs generalizing S with
  | nil => exact hcov
  | cons b bs ih => simpa using ih hcov.2

/-- **Harvest completeness (`≤`).** A coverage witness makes the path-fixing closure contain the residual:
`StabilizerAt adj P S ≤ Subgroup.closure (gensAt adj P gens S)`. Iterates `stabilizerAt_le_closure_gensAt_step`
down the base; the dual of `closure_le_stabilizerAt`. -/
theorem stabilizerAt_le_closure_gensAt_of_coversOrbits {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)} (hcov : CoversOrbits adj P gens bs S) :
    StabilizerAt adj P S ≤ Subgroup.closure (gensAt adj P gens S) := by
  induction bs generalizing S with
  | nil => rw [stabilizerAt_eq_bot_iff_isBase.mpr hcov]; exact bot_le
  | cons b bs ih => exact stabilizerAt_le_closure_gensAt_step b (ih hcov.2) hcov.1

/-- **Harvest completeness (equality) — the path-fixing closure *is* the residual.** Soundness (`≤`,
`closure_gensAt_le_stabilizerAt`, intrinsic to `gensAt`) and the coverage witness (`≥`) give
`Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S`. No separate soundness hypothesis needed. -/
theorem stabilizerAt_eq_closure_gensAt_of_coversOrbits {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)} (hcov : CoversOrbits adj P gens bs S) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  le_antisymm closure_gensAt_le_stabilizerAt (stabilizerAt_le_closure_gensAt_of_coversOrbits bs hcov)

/-- **Partial coverage along a base-sequence segment (no terminal base).** The per-head orbit-coverage clauses
of `CoversOrbits` for the segment `bs` from `S`, *without* requiring the accumulated set to be a base. This is
the piece that lets a base sequence be split into phases: `coversOrbits_append` glues a partial segment to a
full `CoversOrbits` tail. The structural tool for ordering the descent — e.g. **block representatives first,
then within-block points** — that the imprimitive decomposition (Route B) needs: the quotient phase is partial
coverage, the fiber phase the full tail. -/
def CoversOrbitsAlong (adj : AdjMatrix n) (P : PMatrix n) (gens : Set (Equiv.Perm (Fin n))) :
    List (Fin n) → Finset (Fin n) → Prop
  | [], _ => True
  | b :: bs, S =>
      (∀ w, OrbitPartition adj P S b w →
          ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h b = w)
        ∧ CoversOrbitsAlong adj P gens bs (insert b S)

/-- A full `CoversOrbits` witness yields partial coverage along its sequence (forget the terminal base). -/
theorem coversOrbitsAlong_of_coversOrbits {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n))
    {S : Finset (Fin n)} (hcov : CoversOrbits adj P gens bs S) :
    CoversOrbitsAlong adj P gens bs S := by
  induction bs generalizing S with
  | nil => trivial
  | cons b bs ih => exact ⟨hcov.1, ih hcov.2⟩

/-- **Base-sequence phase split.** Partial coverage along `bs₁` from `S`, followed by a full `CoversOrbits`
witness for `bs₂` from the accumulated set `bs₁.foldl insert S`, glue to `CoversOrbits (bs₁ ++ bs₂) S`. This is
the freedom to choose the descent order — resolve one phase (e.g. the quotient / block representatives) before
another (the fibers / within-block points) — that the imprimitive decomposition exploits: each phase's coverage
is supplied by a different (smaller/coarser) constituent's recovery. -/
theorem coversOrbits_append {gens : Set (Equiv.Perm (Fin n))} (bs₁ bs₂ : List (Fin n))
    {S : Finset (Fin n)}
    (h1 : CoversOrbitsAlong adj P gens bs₁ S)
    (h2 : CoversOrbits adj P gens bs₂ (bs₁.foldl (fun s b => insert b s) S)) :
    CoversOrbits adj P gens (bs₁ ++ bs₂) S := by
  induction bs₁ generalizing S with
  | nil => simpa using h2
  | cons b bs ih => exact ⟨h1.1, ih h1.2 h2⟩

/-- **Harvest completeness at the root — the harvested chain *is* `Aut(G)^P`.** At `S = ∅` the path-fixing
condition is vacuous (`gensAt_empty_eq`), so a coverage witness plus the Stage-A2 soundness hypothesis give
`Subgroup.closure gens = StabilizerAt adj P ∅` — the folded generators generate exactly the `P`-preserving
automorphism group. Closes the cross-branch harvest the way Stage A2 closed its soundness half. -/
theorem closure_eq_stabilizerAt_empty_of_coversOrbits {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) (hsound : ∀ g ∈ gens, g ∈ StabilizerAt adj P ∅)
    (hcov : CoversOrbits adj P gens bs ∅) :
    Subgroup.closure gens = StabilizerAt adj P ∅ := by
  rw [← gensAt_empty_eq hsound]
  exact stabilizerAt_eq_closure_gensAt_of_coversOrbits bs hcov

/-- **Capstone — the harvested chain reproduces the residual *order*.** With Stage A3.5, a coverage witness
gives `Nat.card (Subgroup.closure (gensAt adj P gens S)) = orbitSizeProd adj P bs S` (= `∏ basic-orbit
sizes`): the cross-branch harvest recovers not just the residual group but its order — the
`Order = ∏ OrbitSize` of `PermutationGroup.cs`, computed from the *folded* path-fixing generators. -/
theorem card_closure_gensAt_eq_prod_of_coversOrbits {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)} (hcov : CoversOrbits adj P gens bs S) :
    Nat.card (Subgroup.closure (gensAt adj P gens S)) = orbitSizeProd adj P bs S := by
  rw [stabilizerAt_eq_closure_gensAt_of_coversOrbits bs hcov]
  exact card_stabilizerAt_eq_prod_of_base bs S (coversOrbits_isBase_foldl bs hcov)

/-! ### Part A (Stage A2-complete) — de-classed `CoversOrbits` for the involutive (`Z₂^d`) residual

A2-complete reduces the cross-branch harvest's *completeness* to a coverage witness `CoversOrbits`, and the
per-class plan was to discharge it for CFI via the `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` structure theorem. This block
**de-classes** that discharge: a single abstract hypothesis — the residual group is **exponent-2**
(`ResidualInvolutive`, an elementary-abelian `Z₂^d`) — yields `CoversOrbits` for the *generating set of all
involutive residual automorphisms*, for **every** class with that residual structure (CFI's gauge regime, the
twin/module regime, …). It is the cross-branch analogue of how `theorem_2_HOR_of_pPolynomial` de-classed the
metric/DRG family: one structural predicate, no per-class grind.

The mechanism is exactly the existing swap brick. At an involutive node, `orbitPartition_swap_of_involutive`
turns *each* orbit pair `(b, w)` into an involutive residual automorphism `g` with `g b = w` — a single
generator realizing that orbit-mate. If `gens` contains every involutive root residual automorphism (which is
what the leaf-collision harvest, folding in *verified* involutions, supplies), `g ∈ gensAt`, so
`coversOrbits_realize_of_mem` discharges the level. No structure theorem, no `Φ(σ)` base-aut lift: the
identification of the residual with the *literal* gauge flips is sidestepped — the harvested involutions
generate the residual whatever their internal description.

The remaining class-specific obligation is then a single focused predicate — `ResidualInvolutive adj P S`
at the relevant committed set (for CFI: a gauge-regime `S` where the `Aut(H)` factor is killed, so the
residual is the exponent-2 gauge group) — not the full semidirect-product structure theorem. -/

/-- **`ResidualInvolutive` is inherited as the committed set grows** (the exponent-2 analogue of
`residualAbelian_mono`): fixing more points (`S ⊆ S'`) shrinks the residual to a subgroup, and a subgroup of
an exponent-2 group has exponent ≤ 2. So once the residual is involutive at a node, it is involutive at every
deeper node — which lets `coversOrbits_of_residualInvolutive` carry the hypothesis down the base sequence. -/
theorem residualInvolutive_mono {S S' : Finset (Fin n)} (h : ResidualInvolutive adj P S)
    (hSS' : S ⊆ S') : ResidualInvolutive adj P S' :=
  fun π hπ => h π ⟨hπ.1, hπ.2.1, fun v hv => hπ.2.2 v (hSS' hv)⟩

/-- **De-classed coverage, general (non-abelian) form — `CoversOrbits` from per-level path-fixing realizers.**
The honest "covers everything, no class ladder" core of the cross-branch harvest: if at every level `T ⊇ S`
the harvested generating set `gens` contains a **path-fixing realizer** for each orbit-mate of each base point
(a residual automorphism `g ∈ gens` at `T` with `g b = w`), and the base sequence `bs` terminates at a base,
then `CoversOrbits adj P gens bs S` holds. No assumption on the residual's group structure — abelian *or*
non-abelian (schemes, Cameron sections) — so it is the cross-branch analogue of `theorem_2_HOR_of_pPolynomial`
generalized past the exponent-2 case. The realizer is supplied directly to `gensAt` (path-fixing generators),
not to `closure gens`, so this is genuinely the strong-generating-set condition, not the circular one (see the
A2-complete section note). `coversOrbits_of_residualInvolutive` is the special case where the realizers are the
swap involutions; the metric/scheme family is the case where they come from recovery (`CellsAreOrbits`). -/
theorem coversOrbits_of_realizers {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hreal : ∀ T : Finset (Fin n), S ⊆ T → ∀ b w : Fin n,
        OrbitPartition adj P T b w → ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    CoversOrbits adj P gens bs S := by
  induction bs generalizing S with
  | nil => exact hbase
  | cons b bs ih =>
      refine ⟨coversOrbits_realize_of_mem (fun w hw => ?_), ?_⟩
      · obtain ⟨g, hgmem, hgres, hgbw⟩ := hreal S (Finset.Subset.refl S) b w hw
        exact ⟨g, ⟨hgmem, mem_stabilizerAt.mpr hgres⟩, hgbw⟩
      · refine ih (S := insert b S)
          (fun T hT b' w' hw' =>
            hreal T (Finset.Subset.trans (Finset.subset_insert b S) hT) b' w' hw')
          (by simpa using hbase)

/-- **Harvest-facing form — realizers keyed on the refinement-visible cell relation.** The same general
coverage, but the realizer hypothesis ranges over *same-`warmRefine`-cell* pairs (polynomially computable)
rather than over `OrbitPartition` pairs: since orbits refine cells (`OrbitPartition.subset_warmRefine`), a
realizer for every visible cell-mate covers every orbit-mate a fortiori. This is the shape the structural
(scheme/recovery) harvest actually supplies — at a recoverable node cells *are* orbits, so the visible
cell-mates are exactly the orbit-mates, and the leaf-collision harvest collects a path-fixing realizer for
each. (At a non-recoverable node the hypothesis demands realizers for cell-mates that are not orbit-mates, so
it is only satisfiable in the recoverable regime — which is correct.) -/
theorem coversOrbits_of_visibleRealizers {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hreal : ∀ T : Finset (Fin n), S ⊆ T → ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    CoversOrbits adj P gens bs S :=
  coversOrbits_of_realizers bs
    (fun T hT b w hw => hreal T hT b w (OrbitPartition.subset_warmRefine hw)) hbase

/-- **General harvest completeness — the path-fixing closure *is* the residual, from realizers.** Composing
`coversOrbits_of_realizers` with the A2-complete equality `stabilizerAt_eq_closure_gensAt_of_coversOrbits`:
given per-level path-fixing realizers (abelian *or* non-abelian), `Subgroup.closure (gensAt adj P gens S) =
StabilizerAt adj P S`. The general (non-exponent-2) analogue of `closure_eq_stabilizerAt_of_residualInvolutive`
— the cross-branch harvest reproduces the residual group for the whole recoverable class, no group-structure
hypothesis. With Stage A3.5 the order `= ∏ basic-orbit sizes` follows (`card_closure_gensAt_eq_prod_of_coversOrbits`). -/
theorem closure_eq_stabilizerAt_of_realizers {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hreal : ∀ T : Finset (Fin n), S ⊆ T → ∀ b w : Fin n,
        OrbitPartition adj P T b w → ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  stabilizerAt_eq_closure_gensAt_of_coversOrbits bs (coversOrbits_of_realizers bs hreal hbase)

/-- **The localisation core — recovery makes the harvest refinement-decidable.** At a node `T` where orbits
are recovered (`CellsAreOrbits`), the refinement-**visible** realizer hypothesis (over same-`warmRefine`-cell
pairs — polynomially computable) is *equivalent* to the orbit realizer hypothesis (over `OrbitPartition`
pairs). The `→` direction is free (orbits refine cells, `OrbitPartition.subset_warmRefine`); the `←` direction
is exactly where recovery is used (a visible cell-mate is a genuine orbit-mate). This pins what localisation
buys the cross-branch harvest: coverage **correctness** holds from orbit realizers unconditionally
(`coversOrbits_of_realizers`), and recovery is what makes the *equivalent* harvest target
**refinement-computable** — the polynomiality layer, not a correctness gap. Per-level recovery down the base
sequence is therefore the substrate-conditional content (the cascade property iterated; `RecoverableByDepth`
witnesses), distinct from and downstream of the now-unconditional coverage core. -/
theorem orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits {gens : Set (Equiv.Perm (Fin n))}
    {T : Finset (Fin n)} (hrec : CellsAreOrbits adj P T) :
    (∀ b w : Fin n, OrbitPartition adj P T b w → ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
      ↔ (∀ b w : Fin n, warmRefine adj P (individualizedColouring n T) b
            = warmRefine adj P (individualizedColouring n T) w →
          ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w) := by
  constructor
  · intro horb b w hcell; exact horb b w (hrec b w hcell)
  · intro hvis b w ho; exact hvis b w (OrbitPartition.subset_warmRefine ho)

/-- **General polynomiality capstone (group side, refinement-computable).** `closure_eq_stabilizerAt_of_realizers`
keys on `OrbitPartition` realizers (the orbits being *computed*); the honest harvest interface is `warmRefine`
*cells* (refinement-computable). Composing `coversOrbits_of_visibleRealizers` with the A2-complete equality:
per-level path-fixing realizers for every same-`warmRefine`-cell pair give `Subgroup.closure (gensAt adj P gens
S) = StabilizerAt adj P S`. The visible-realizer hypothesis is satisfiable exactly on the recoverable class
(`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`), so this is the cross-branch harvest reproducing the
residual *group* through the interface it actually computes on — the polynomiality layer made explicit. -/
theorem closure_eq_stabilizerAt_of_visibleRealizers {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hreal : ∀ T : Finset (Fin n), S ⊆ T → ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  stabilizerAt_eq_closure_gensAt_of_coversOrbits bs (coversOrbits_of_visibleRealizers bs hreal hbase)

/-- **General polynomiality capstone — the cross-branch harvest reproduces the residual group AND order from
the refinement-computable harvest.** The polynomiality-layer analogue of `exhaustiveObstruction_scheme`: from
per-level path-fixing *visible* (cell) realizers — what the leaf-collision harvest supplies, satisfiable on the
recoverable class — and a terminal base, BOTH `Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S`
and its order `Nat.card … = orbitSizeProd adj P bs S` (= `∏ basic-orbit sizes`). The single substrate-conditional
input is **recovery** (which makes the visible-realizer hypothesis satisfiable, via
`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`); the coverage → group → order chain is unconditional and
axiom-clean. The witnesses populating recovery are `recoverableByDepth_pPolynomial` (metric/DRG) and
`recoverableByDepth_cfi` (CFI). -/
theorem crossBranchHarvest_reproduces_residual {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hreal : ∀ T : Finset (Fin n), S ⊆ T → ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S
      ∧ Nat.card (Subgroup.closure (gensAt adj P gens S)) = orbitSizeProd adj P bs S := by
  have hcov := coversOrbits_of_visibleRealizers bs hreal hbase
  exact ⟨stabilizerAt_eq_closure_gensAt_of_coversOrbits bs hcov,
    card_closure_gensAt_eq_prod_of_coversOrbits bs hcov⟩

/-- **Root headline — the descent reproduces `Aut(G)^P` and `|Aut(G)^P|` from the refinement-computable harvest.**
The `S = ∅` case of `crossBranchHarvest_reproduces_residual` (via `gensAt_empty_eq`): on the recoverable class,
the folded harvested generators generate **exactly** the `P`-preserving automorphism group, and its order is the
basic-orbit-size product — `Order = ∏ OrbitSize` of `PermutationGroup.cs`, computed end-to-end from the visible
(cell) harvest with no group-structure hypothesis (abelian or non-abelian). -/
theorem autP_reproduced_of_visibleRealizers {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n))
    (hsound : ∀ g ∈ gens, g ∈ StabilizerAt adj P ∅)
    (hreal : ∀ T : Finset (Fin n), (∅ : Finset (Fin n)) ⊆ T → ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) ∅)) :
    Subgroup.closure gens = StabilizerAt adj P ∅
      ∧ Nat.card (Subgroup.closure gens) = orbitSizeProd adj P bs ∅ := by
  have hcov := coversOrbits_of_visibleRealizers bs hreal hbase
  refine ⟨closure_eq_stabilizerAt_empty_of_coversOrbits bs hsound hcov, ?_⟩
  rw [← gensAt_empty_eq hsound]
  exact card_closure_gensAt_eq_prod_of_coversOrbits bs hcov

/-! ### Route B — the swap decomposition of orbit coverage (the imprimitive recursion's core)

For an **imprimitive** residual, `Aut_S` *permutes* a block system, so orbit pairs cross block boundaries —
the symmetry-respecting (non-block-swapping) case cannot reach it.
The decomposition uses that `CoversOrbits`'s coverage clause is keyed on `Subgroup.closure (gensAt …)` — a
group, **closed under composition** — so a cross-block orbit pair is realized by composing a **block-swap**
(reach the orbit-mate's block) with a **fiber move** (within that block). This is the wreath structure of an
imprimitive group, and it factors the full-orbit coverage into:
* **block-reach** (`hreach`, the *quotient* recovery): the closure can send `b` into the block of every
  orbit-mate `w` (`β (σ b) = β w`);
* **within-block coverage** (`hfiber`, the *fiber* recovery): the closure realizes every *same-block* orbit
  pair.

The two constituents are recovered on the *smaller* quotient and fiber actions — both transitive/schurian by
the Phase-0 gate (`schemeBlock_fiber_transitive`, `schemeBlocks_transitive`, `Scheme.lean §11.1`) — so the
size-induction (Phase 2) discharges them via its IH. Discharging the seal's `hImprimitive`
([exhaustive-obstruction §0.7.6](../../../docs/chain-descent-exhaustive-obstruction.md)). -/

/-- **Phase 1 core — swap decomposition of a coverage clause.** The closure-based coverage of base point
`b`'s full residual orbit factors, along a partition `β`, into **block-reach** `hreach` and **within-block
coverage** `hfiber`. The realizer is the composite `h * σ` (block-swap `σ` then fiber move `h`), which lands
in the closure subgroup — why this needs `closure (gensAt …)` (composition-closed), not single generators.
Handles the Aut-**permuted** (block-swapping) imprimitive case (orbits crossing block boundaries). -/
theorem orbitCoverage_of_blockDecomposition {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))} {S : Finset (Fin n)} (b : Fin n)
    (hreach : ∀ w, OrbitPartition adj P S b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens S), β (σ b) = β w)
    (hfiber : ∀ u w, OrbitPartition adj P S u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h u = w) :
    ∀ w, OrbitPartition adj P S b w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h b = w := by
  intro w hbw
  obtain ⟨σ, hσcl, hσβ⟩ := hreach w hbw
  have hσres : ResidualAut adj P S σ := mem_stabilizerAt.mp (closure_gensAt_le_stabilizerAt hσcl)
  have hb_σb : OrbitPartition adj P S b (σ b) :=
    orbitPartition_iff_residualAut.mpr ⟨σ, hσres, rfl⟩
  have hσb_w : OrbitPartition adj P S (σ b) w := (hb_σb.symm).trans hbw
  obtain ⟨h, hhcl, hhσb⟩ := hfiber (σ b) w hσb_w hσβ
  exact ⟨h * σ, mul_mem hhcl hσcl, by rw [Equiv.Perm.mul_apply, hhσb]⟩

/-- **Phase 1 wiring — a `CoversOrbits` step from the block decomposition.** Assembles one
`CoversOrbits (b :: bs) S` level: the head clause from `orbitCoverage_of_blockDecomposition` (block-reach +
within-block coverage at `b`) and the tail from the recursion on `insert b S`. The recursion-ready interface
the Phase-2 size-induction iterates down the base sequence. -/
theorem coversOrbits_cons_of_blockDecomposition {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))} {S : Finset (Fin n)} (b : Fin n) (bs : List (Fin n))
    (hreach : ∀ w, OrbitPartition adj P S b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens S), β (σ b) = β w)
    (hfiber : ∀ u w, OrbitPartition adj P S u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens S), h u = w)
    (htail : CoversOrbits adj P gens bs (insert b S)) :
    CoversOrbits adj P gens (b :: bs) S :=
  ⟨orbitCoverage_of_blockDecomposition β b hreach hfiber, htail⟩

/-- **Phase 2 — assemble full coverage from per-level block decomposition.** Iterating
`coversOrbits_cons_of_blockDecomposition` down a base sequence `bs`: if at *every* level `T` the closure has
**block-reach** (`hreach`, the quotient constituent) and **within-block coverage** (`hfiber`, the fiber
constituent) for the partition `β`, and the accumulated set is a base, then `CoversOrbits adj P gens bs S`
holds. The induction is on `bs` and stays entirely on `Fin n` — `hreach`/`hfiber` are block-restricted
quantifiers over the *original* vertex set, so **no sub-scheme is ever materialized** (the rejected
quotient-`AdjMatrix` route is sidestepped; the recursion lives in the coverage predicate, not in new types). -/
theorem coversOrbits_of_blockDecomposition {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n)) (S : Finset (Fin n))
    (hreach : ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w)
    (hfiber : ∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    CoversOrbits adj P gens bs S := by
  induction bs generalizing S with
  | nil => exact hbase
  | cons b bs ih =>
      exact coversOrbits_cons_of_blockDecomposition β b bs (hreach S b) (hfiber S)
        (ih (insert b S) hbase)

/-- **Phase 2 — `ReachesRigid` (the harvest reproduces `Aut_S`) from the block decomposition.** With the
per-level block-reach + within-block coverage and a terminal base, the path-fixing harvest reproduces the
residual group: `closure (gensAt … S) = StabilizerAt adj P S`. This is the Route-B reduction completed at the
harvest level — the imprimitive residual's group is reproduced from **quotient** (block-reach) + **fiber**
(within-block) coverage, each on the smaller constituent (transitive/schurian by the §11.1 gate
`schemeBlock_fiber_transitive`/`schemeBlocks_transitive`), with **no sub-scheme materialized**. The remaining
open content is discharging `hreach`/`hfiber` from the constituents' recovery (the substrate-conditional
depth-graded block-visibility, A2-ii) — the honest frontier, now localized to two intrinsic coverage interfaces. -/
theorem reachesRigid_of_blockDecomposition {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n)) (S : Finset (Fin n))
    (hreach : ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w)
    (hfiber : ∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  stabilizerAt_eq_closure_gensAt_of_coversOrbits bs
    (coversOrbits_of_blockDecomposition β bs S hreach hfiber hbase)

/-! ### Class-agnostic suppliers for the Route B coverage interfaces `hreach`/`hfiber`

The Route B chain (`reachesRigid_of_blockDecomposition`) reduces the imprimitive branch to two coverage
interfaces, `hreach` (quotient / block-reach) and `hfiber` (fiber / within-block). These suppliers discharge
them **class-agnostically**, each from a hypothesis strictly *weaker* than whole-residual recovery — exposing
the general decomposition the eventual unconditional proof must follow:

* `hreach` needs only **quotient realizers** — residual auts in `gens` that land `b` in the *block* of every
  orbit-mate `w` (`β (σ b) = β w`), **not** `σ b = w`. This is recovery of the (coarser) action on blocks.
* `hfiber` needs only **fiber realizers** — residual auts realizing *same-block* orbit pairs exactly. This is
  recovery on the (smaller) within-block action.

Full orbit realizers imply both (`blockHarvest_of_realizers`, with `β` unused) — so any whole-graph-recoverable
class satisfies both interfaces (non-vacuity floor); the *independent* value of the block decomposition is
exactly the regime where the quotient and fiber recover at lower depth than the whole. The class-agnostic crux
the open general case turns on is a **separability-number reduction-to-constituents** (`s(C)` of an imprimitive
scheme bounded via its quotient and fiber — exhaustive-obstruction §0.7.6, sought-and-not-located): supplying
`hquot`/`hfib` from the constituents and assembling via the Route B chain is precisely that shape, with only
per-constituent recovery carried. -/

/-- A harvested residual automorphism (`g ∈ gens`, `ResidualAut adj P T g`) sits in the path-fixing closure
`Subgroup.closure (gensAt adj P gens T)` — the single membership step both Route B suppliers below share. -/
theorem mem_closure_gensAt_of_realizer {gens : Set (Equiv.Perm (Fin n))} {T : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} (hg : g ∈ gens) (hres : ResidualAut adj P T g) :
    g ∈ Subgroup.closure (gensAt adj P gens T) :=
  Subgroup.subset_closure ⟨hg, mem_stabilizerAt.mpr hres⟩

/-- **`hreach` from quotient realizers (the weaker, block-accurate interface).** If at every level the harvest
contains a residual automorphism sending each base point `b` into the *block* of every orbit-mate `w`
(`β (σ b) = β w` — not necessarily `σ b = w`), then the block-reach interface `hreach` holds. This is recovery
of the **quotient** (action on blocks) only — strictly weaker than full orbit recovery, and the part of Route B
that can hold when the whole residual does not recover. -/
theorem hreach_of_quotientRealizers {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hquot : ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ, σ ∈ gens ∧ ResidualAut adj P T σ ∧ β (σ b) = β w) :
    ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w := by
  intro T b w hbw
  obtain ⟨σ, hσmem, hσres, hσβ⟩ := hquot T b w hbw
  exact ⟨σ, mem_closure_gensAt_of_realizer hσmem hσres, hσβ⟩

/-- **`hfiber` from fiber realizers (recovery on the smaller within-block action).** If at every level the
harvest contains a residual automorphism exactly realizing every *same-block* orbit pair (`β u = β w → h u = w`),
then the within-block interface `hfiber` holds. This is recovery of the **fiber** (the block action, on
`|B| < n` points) only — the second, smaller constituent of the imprimitive decomposition. -/
theorem hfiber_of_fiberRealizers {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hfib : ∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h, h ∈ gens ∧ ResidualAut adj P T h ∧ h u = w) :
    ∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w := by
  intro T u w huw hβ
  obtain ⟨h, hmem, hres, hhuw⟩ := hfib T u w huw hβ
  exact ⟨h, mem_closure_gensAt_of_realizer hmem hres, hhuw⟩

/-- **`hfiber` from within-block *visible* realizers — the fiber discharged from refinement-computable
recovery (Approach A, fiber half).** The refinement-computable form of `hfiber_of_fiberRealizers`: the harvest
need only realize the *same-`warmRefine`-cell* pairs that lie **within a block** (`β u = β w`), and `hfiber`
follows. Since orbits refine cells (`OrbitPartition.subset_warmRefine`), a same-block orbit pair is a same-block
cell pair, so the within-block visible realizer applies. This is **strictly weaker than whole-graph recovery**:
the hypothesis is satisfiable exactly when *within each block* cells = orbits (the **fiber recovers**), even
when globally cells ⊋ orbits (the whole does not recover) — the regime where the block decomposition earns its
keep (e.g. Shrikhande, whose 1-WL merges happen *across* blocks). The fiber half of the per-level
quotient/fiber split that `orbitCoverage_of_blockDecomposition` composes; the quotient half (`hreach` from
block-orbit recovery) needs a block-level 1-WL and is the next step. -/
theorem hfiber_of_fiberVisibleRealizers {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hfvis : ∀ T : Finset (Fin n), ∀ u w : Fin n, β u = β w →
        warmRefine adj P (individualizedColouring n T) u
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g u = w) :
    ∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w := by
  intro T u w huw hβ
  obtain ⟨g, hmem, hres, hguw⟩ := hfvis T u w hβ (OrbitPartition.subset_warmRefine huw)
  exact ⟨g, mem_closure_gensAt_of_realizer hmem hres, hguw⟩

/-- **`hreach` from quotient *visible* realizers — the block-move half discharged from refinement-computable
recovery (Approach A, quotient half; the named next step).** The quotient analogue of
`hfiber_of_fiberVisibleRealizers`, completing the refinement-computable supply for *both* halves of the block
decomposition. The harvest need only realize the *block-move* of each same-`warmRefine`-cell pair — a residual
aut `σ ∈ gens` carrying `b` into the **block** of `w` (`β (σ b) = β w`, not `σ b = w`) — and `hreach` follows:
since orbits refine cells (`OrbitPartition.subset_warmRefine`), an orbit pair is a cell pair, so the visible
block-mover applies, and `mem_closure_gensAt_of_realizer` lands it in the path-fixing closure. **Non-vacuity /
the content:** same-block cell pairs are free (take `σ = id`, `β b = β w`), so the only real obligations are
*cross-block* same-cell pairs — exactly the recovery of the (coarser) **block action** (a block-level 1-WL),
satisfiable when blocks are visibly resolved even where globally cells ⊋ orbits. The G2-A finding (2026-06-07)
pinned this as the missing quotient half: block-visibility (cells ⊆ blocks) supports the *fiber*, not
block-moves; this supplies the block-moves from the visible block-mover hypothesis. (Stated against the full
`warmRefine` cell — a sound over-approximation of the genuine coarser `blockCell`; the block-cell form is a
further refinement.) -/
theorem hreach_of_quotientVisibleRealizers {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hqvis : ∀ T : Finset (Fin n), ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ σ, σ ∈ gens ∧ ResidualAut adj P T σ ∧ β (σ b) = β w) :
    ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w := by
  intro T b w hbw
  obtain ⟨σ, hmem, hres, hσβ⟩ := hqvis T b w (OrbitPartition.subset_warmRefine hbw)
  exact ⟨σ, mem_closure_gensAt_of_realizer hmem hres, hσβ⟩

/-- **Imprimitive recovery from a fully refinement-computable block decomposition (the shallow-phase discharge,
imprimitive case).** Both halves of the block decomposition are now supplied from **visible**
(refinement-computable) realizers — the quotient/block-move half (`hreach_of_quotientVisibleRealizers`,
the shallow phase) and the within-block/fiber half (`hfiber_of_fiberVisibleRealizers`, the deep phase) — so the
path-fixing harvest reproduces the residual group `closure (gensAt … S) = StabilizerAt adj P S` from a
**non-vacuous, refinement-computable** decomposition, with **no sub-scheme materialized**. This completes
`reachesRigid_of_blockDecomposition`'s reduction to the two coverage interfaces *with both keyed on visible
realizers* (matching `SchemeRecovered`'s non-vacuity), rather than raw orbit coverage. The residual carried
content is exactly the two visible hypotheses `hqvis`/`hfvis` — *whether* the quotient (block action) and fiber
(within-block action) recover, i.e. their block-level / within-block WL-dimension — the substrate-conditional
unit, now properly localized to the two smaller constituents (transitive/schurian by the §11.1 gate). -/
theorem reachesRigid_of_blockVisibleDecomposition {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n)) (S : Finset (Fin n))
    (hqvis : ∀ T : Finset (Fin n), ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ σ, σ ∈ gens ∧ ResidualAut adj P T σ ∧ β (σ b) = β w)
    (hfvis : ∀ T : Finset (Fin n), ∀ u w : Fin n, β u = β w →
        warmRefine adj P (individualizedColouring n T) u
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g u = w)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  reachesRigid_of_blockDecomposition β bs S
    (hreach_of_quotientVisibleRealizers β hqvis)
    (hfiber_of_fiberVisibleRealizers β hfvis)
    hbase

/-- **Full orbit realizers supply both interfaces (the subsumption / non-vacuity floor).** If the harvest
contains an exact realizer (`g b = w`) for every orbit pair at every level, then *both* `hreach` and `hfiber`
hold — for **any** partition `β`, which is left unused: an exact realizer is a fortiori block-accurate
(`β (g b) = β w` since `g b = w`) and within-block-exact. So any whole-residual-recoverable class satisfies the
Route B interfaces; the block decomposition's independent content is strictly the regime where `hquot`/`hfib`
are reachable but full recovery is not. -/
theorem blockHarvest_of_realizers {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hreal : ∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w) :
    (∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w)
    ∧ (∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w) :=
  ⟨hreach_of_quotientRealizers β (fun T b w hbw => by
      obtain ⟨g, hg, hres, hgw⟩ := hreal T b w hbw
      exact ⟨g, hg, hres, by rw [hgw]⟩),
   hfiber_of_fiberRealizers β (fun T u w huw _ => hreal T u w huw)⟩

/-- **Witness supplier — recovery + visible realizers supply both interfaces.** The refinement-computable
form: where orbits are recovered at every level (`CellsAreOrbits T`) and the leaf-collision harvest collected a
path-fixing realizer for every *visible cell-mate*, both `hreach` and `hfiber` hold (for any `β`). A visible
cell-mate is a genuine orbit-mate under recovery (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`), so
the orbit realizers `blockHarvest_of_realizers` needs are supplied. The metric/DRG
(`recoverableByDepth_pPolynomial`) and CFI (`recoverableByDepth_cfi`) recovery witnesses plug straight in to
discharge the imprimitive branch on the whole recoverable class. -/
theorem blockHarvest_of_visibleRecovery {ι : Type*} (β : Fin n → ι)
    {gens : Set (Equiv.Perm (Fin n))}
    (hrec : ∀ T : Finset (Fin n), CellsAreOrbits adj P T)
    (hvis : ∀ T : Finset (Fin n), ∀ b w : Fin n,
        warmRefine adj P (individualizedColouring n T) b
          = warmRefine adj P (individualizedColouring n T) w →
        ∃ g, g ∈ gens ∧ ResidualAut adj P T g ∧ g b = w) :
    (∀ T : Finset (Fin n), ∀ b w, OrbitPartition adj P T b w →
        ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w)
    ∧ (∀ T : Finset (Fin n), ∀ u w, OrbitPartition adj P T u w → β u = β w →
        ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w) :=
  blockHarvest_of_realizers β
    (fun T => (orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits (hrec T)).mpr (hvis T))

/-- **De-classed coverage — `CoversOrbits` from an exponent-2 residual.** If the residual group at `S` is
involutive (`ResidualInvolutive`, hence at every deeper node by `residualInvolutive_mono`), the generating set
`gens` contains every involutive residual automorphism (`hgens` — what the leaf-collision harvest supplies),
and the base sequence `bs` terminates at a base, then `CoversOrbits adj P gens bs S` holds. Per level, the
swap brick `orbitPartition_swap_of_involutive` realizes each orbit-mate of the base point by a single
involutive path-fixing generator, discharged through `coversOrbits_realize_of_mem`. Discharges the
A2-complete coverage witness for the whole elementary-abelian-residual class in one theorem — no per-class
structure theorem. -/
theorem coversOrbits_of_residualInvolutive {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hinv : ResidualInvolutive adj P S)
    (hgens : ∀ g, ResidualAut adj P S g → g * g = 1 → g ∈ gens)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    CoversOrbits adj P gens bs S := by
  refine coversOrbits_of_realizers bs (fun T hT b w hw => ?_) hbase
  have hinvT : ResidualInvolutive adj P T := residualInvolutive_mono hinv hT
  obtain ⟨g, hgT, hgbw, _⟩ := orbitPartition_swap_of_involutive hinvT hw
  have hgS : ResidualAut adj P S g := ⟨hgT.1, hgT.2.1, fun v hv => hgT.2.2 v (hT hv)⟩
  exact ⟨g, hgens g hgS (hinvT g hgT), hgT, hgbw⟩

/-- **De-classed harvest completeness — the involutive residual *is* the closure of harvested involutions.**
Combining `coversOrbits_of_residualInvolutive` with the A2-complete equality
`stabilizerAt_eq_closure_gensAt_of_coversOrbits`: at an exponent-2 node the path-fixing closure of the
harvested involutive generators equals the residual, `Subgroup.closure (gensAt adj P gens S) = StabilizerAt
adj P S`. The cross-branch completeness for *every* elementary-abelian-residual class, with no per-class
structure theorem (CFI's gauge regime is a witness, supplying only `ResidualInvolutive` at a gauge-regime
`S`). The cross-branch analogue of `theorem_2_HOR_of_pPolynomial`. -/
theorem closure_eq_stabilizerAt_of_residualInvolutive {gens : Set (Equiv.Perm (Fin n))}
    (bs : List (Fin n)) {S : Finset (Fin n)}
    (hinv : ResidualInvolutive adj P S)
    (hgens : ∀ g, ResidualAut adj P S g → g * g = 1 → g ∈ gens)
    (hbase : IsBase adj P (bs.foldl (fun s b => insert b s) S)) :
    Subgroup.closure (gensAt adj P gens S) = StabilizerAt adj P S :=
  stabilizerAt_eq_closure_gensAt_of_coversOrbits bs
    (coversOrbits_of_residualInvolutive bs hinv hgens hbase)

/-! ### Part A (Stage A2-complete) — CFI instance: gauge flips as path-fixing residual generators

The cross-branch harvest for a CFI graph folds in **gauge flips** (`cfiFlipAut`, the cycle-space `Z₂^β`
generators built in `CFI.lean`). This block bridges those flips to the A2-complete vocabulary: a gauge flip
that is `F`-free on the committed path's gadgets fixes the path pointwise
(`cfiFlipAut_eq_self_of_flipSet_empty`), is an automorphism (`isAut_cfiFlipAut`), and preserves an
automorphism-invariant `P` (`cfiFlipAut_preserves_P`) — i.e. it is a path-fixing `ResidualAut adj P S`,
hence an element of `StabilizerAt adj P S` and of the path-fixing generators `gensAt`. So the harvested
gauge generators `cfiGaugeGens` populate `gensAt`, and each moves a vertex within its `Aut_S^P`-orbit.

**This is the *forward* direction of coverage** (flips ⟹ orbit moves). The *reverse* — that the path-fixing
flips' closure realizes the *full* orbit of each base point (the genuine `CoversOrbits` discharge) — is the
cycle-space content staged next (CFI-cov.2/3): it needs the `Z₂^β` structure and a base sequence. -/

/-- **A path-fixing gauge flip is a residual automorphism.** A symmetric (`hFsymm`), even (`hEven`) gauge
flip `cfiFlipAut F` whose flip-set is empty on every gadget of `S` (`hS`, so it fixes `S` pointwise) is an
`IsAut` preserving any automorphism-invariant `P` (`hP`) — i.e. a `ResidualAut adj P S`. The bridge from the
`CFI.lean` gauge-flip layer to the A2-complete residual vocabulary. -/
theorem cfiFlipAut_residualAut (h : IsCFI' adj) (F : Fin h.m → Fin h.m → Bool)
    (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0) (hFsymm : ∀ v w, F v w = F w v)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, h.H.flipSet F (h.H.gadget (h.e i)) = ∅) :
    ResidualAut adj P S (h.cfiFlipAut F hEven) :=
  ⟨h.isAut_cfiFlipAut F hEven hFsymm,
   h.cfiFlipAut_preserves_P F hEven hFsymm hP,
   fun i hi => h.cfiFlipAut_eq_self_of_flipSet_empty F hEven (hS i hi)⟩

/-- A path-fixing gauge flip is an element of the residual group `StabilizerAt adj P S`. -/
theorem cfiFlipAut_mem_stabilizerAt (h : IsCFI' adj) (F : Fin h.m → Fin h.m → Bool)
    (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0) (hFsymm : ∀ v w, F v w = F w v)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, h.H.flipSet F (h.H.gadget (h.e i)) = ∅) :
    h.cfiFlipAut F hEven ∈ StabilizerAt adj P S :=
  mem_stabilizerAt.mpr (cfiFlipAut_residualAut h F hEven hFsymm hP hS)

/-- **Forward coverage — a path-fixing gauge flip moves `v` within its `Aut_S^P`-orbit.**
`OrbitPartition adj P S v (cfiFlipAut F v)`: every gauge flip fixing the path realizes one orbit move.
(The *reverse* — realizing the full orbit — is the staged cycle-space content.) -/
theorem cfiFlipAut_orbitPartition (h : IsCFI' adj) (F : Fin h.m → Fin h.m → Bool)
    (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0) (hFsymm : ∀ v w, F v w = F w v)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, h.H.flipSet F (h.H.gadget (h.e i)) = ∅) (v : Fin n) :
    OrbitPartition adj P S v (h.cfiFlipAut F hEven v) :=
  orbitPartition_iff_residualAut.mpr ⟨_, cfiFlipAut_residualAut h F hEven hFsymm hP hS, rfl⟩

/-- **The CFI gauge generating set.** All symmetric, even gauge flips `cfiFlipAut F` — the cycle-space
`Z₂^β` generators the harvest folds in. `Subgroup.closure (cfiGaugeGens h)` is the gauge group; the
A2-complete machinery (`closure_eq_stabilizerAt_empty_of_coversOrbits`) turns a coverage witness over these
into `closure = StabilizerAt ∅`. -/
def cfiGaugeGens (h : IsCFI' adj) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ (F : Fin h.m → Fin h.m → Bool) (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0),
        (∀ v w, F v w = F w v) ∧ h.cfiFlipAut F hEven = g}

/-- **Root soundness of the gauge generators.** Every gauge flip is a `P`-preserving automorphism
(`ResidualAut adj P ∅`, the path-fixing condition vacuous at `∅`) — the Stage-A2 soundness hypothesis
`closure_eq_stabilizerAt_empty_of_coversOrbits` consumes. -/
theorem cfiGaugeGens_residualAut_empty (h : IsCFI' adj)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u) :
    ∀ g ∈ cfiGaugeGens h, ResidualAut adj P ∅ g := by
  rintro g ⟨F, hEven, hFsymm, rfl⟩
  exact cfiFlipAut_residualAut h F hEven hFsymm hP (by simp)

/-- A path-fixing gauge flip lies in the path-fixing generators `gensAt adj P (cfiGaugeGens h) S` — it is
both a gauge generator and a member of `StabilizerAt adj P S`. The hook the coverage discharge (CFI-cov.3)
will use to realize orbits from `cfiGaugeGens`. -/
theorem cfiFlipAut_mem_gensAt (h : IsCFI' adj) (F : Fin h.m → Fin h.m → Bool)
    (hEven : ∀ v, (h.H.flipSet F v).card % 2 = 0) (hFsymm : ∀ v w, F v w = F w v)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, h.H.flipSet F (h.H.gadget (h.e i)) = ∅) :
    h.cfiFlipAut F hEven ∈ gensAt adj P (cfiGaugeGens h) S :=
  ⟨⟨F, hEven, hFsymm, rfl⟩, cfiFlipAut_mem_stabilizerAt h F hEven hFsymm hP hS⟩

/-! ### Part A (Stage A2-complete) — CFI-cov.2: the base sequence

`CoversOrbits adj P gens bs ∅` terminates in `IsBase adj P (bs.foldl insert ∅)`. For an odd-degree CFI
graph the axiom-free cascade discreteness (`theorem_1_HOR_cfi_oddDeg`) gives a discrete set, hence a base
(`isBase_of_discrete_warmRefine`); enumerating it yields the ordered base sequence the coverage witness
quantifies over. (The per-level coverage clauses are CFI-cov.3.) -/

/-- **Discreteness ⟹ base.** If `warmRefine adj P (individualizedColouring n S)` is discrete then `S` is a
base (`IsBase adj P S`) — at discrete depth the orbit partition collapses to equality
(`orbit_iff_eq_of_discrete_warmRefine`). The general bridge from the cascade's `Discrete` output to the
`IsBase` terminal of `CoversOrbits`. -/
theorem isBase_of_discrete_warmRefine {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S))) : IsBase adj P S :=
  fun v w hvw => (orbit_iff_eq_of_discrete_warmRefine hd v w).mp hvw

/-- Folding `insert` over a list from `s` accumulates the list's elements: `= s ∪ l.toFinset`. -/
theorem foldl_insert_eq_union (l : List (Fin n)) (s : Finset (Fin n)) :
    l.foldl (fun acc b => insert b acc) s = s ∪ l.toFinset := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, List.toFinset_cons, Finset.insert_union, Finset.union_insert]

/-- Folding `insert` over a list from `∅` rebuilds the list's underlying finset. -/
theorem foldl_insert_empty_eq_toFinset (l : List (Fin n)) :
    l.foldl (fun acc b => insert b acc) ∅ = l.toFinset := by
  rw [foldl_insert_eq_union]; exact Finset.empty_union _

/-- **CFI base sequence (odd-degree).** From the axiom-free cascade discreteness
(`theorem_1_HOR_cfi_oddDeg`), an odd-degree CFI graph has an ordered base sequence: a list `bs` whose
accumulated set `bs.foldl insert ∅` is a base. This is the terminal (`IsBase`) case a `CoversOrbits`
witness for CFI requires; the per-level coverage is CFI-cov.3. -/
theorem cfi_exists_base_seq (h : IsCFI' adj) (h_odd : h.OddDegree) :
    ∃ bs : List (Fin n), IsBase adj P (bs.foldl (fun acc b => insert b acc) ∅) := by
  obtain ⟨S, _, hd, _⟩ := h.theorem_1_HOR_cfi_oddDeg h_odd P
  refine ⟨S.toList, ?_⟩
  rw [foldl_insert_empty_eq_toFinset, Finset.toList_toFinset]
  exact isBase_of_discrete_warmRefine hd

/-! ### Part A (Stage A2-complete) — CFI-cov.3 (de-classed): the gauge group + harvest from gauge-generation

The de-classed coverage `coversOrbits_of_residualInvolutive` discharges `CoversOrbits` for any exponent-2
residual, from a generating set containing the harvested involutions. For CFI the gauge flips `cfiGaugeGens`
are exactly such involutions: by the cycle-space homomorphism (`cfiFlipAut_xorF` / `cfiFlipAut_one`) they form
a **subgroup** (`gaugeSubgroup`), and each is an involution (`cfiFlipAut_involutive`), so the gauge group is
elementary-abelian `Z₂^β` — every element squares to `1`.

This collapses the entire CFI cross-branch harvest — `cfi_coversOrbits`, `closure cfiGaugeGens = StabilizerAt
∅`, and the order `|Aut(CFI)^P| = ∏ basic-orbit sizes` — onto a **single** CFI obligation: **gauge-generation**
`StabilizerAt adj P ∅ ≤ closure (cfiGaugeGens h)` (every `P`-preserving automorphism is a product of gauge
flips — the surjective half of the classical `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` structure theorem; the converse `≤`
is free, `cfiGaugeGens_residualAut_empty`). The `Φ(σ)` base-aut lift, the semidirect decomposition, and the
per-level orbit-coverage clauses are **gone**; only this containment remains. Firing content (C# canonizes
CFI(K₄–K₇)), not GI-hard. -/

/-- **The CFI gauge group as a `Subgroup` — the `Z₂^β` factor.** `cfiGaugeGens h` is closed under the group
operations: `cfiFlipAut_xorF` gives `cfiFlipAut F * cfiFlipAut F' = cfiFlipAut (xorF F F')` (a flip), with the
flip-subgraph `xorF F F'` even (`even_xorF`) and symmetric; `cfiFlipAut_one` gives the identity; and
`cfiFlipAut_involutive` makes each its own inverse. So the gauge generators are already a subgroup, not merely
a generating set. -/
def gaugeSubgroup (h : IsCFI' adj) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := cfiGaugeGens h
  one_mem' := by
    have hcf : ∀ v, (h.H.flipSet (fun _ _ => false) v).card % 2 = 0 := by
      intro v
      have : h.H.flipSet (fun _ _ => false) v = ∅ := by ext w; simp [CFIBase.mem_flipSet]
      rw [this]; rfl
    exact ⟨fun _ _ => false, hcf, fun _ _ => rfl, h.cfiFlipAut_one hcf⟩
  mul_mem' := by
    rintro a b ⟨F, hF, hFs, rfl⟩ ⟨F', hF', hF's, rfl⟩
    exact ⟨CFIBase.xorF F F', h.H.even_xorF hF hF',
      fun v w => by simp only [CFIBase.xorF]; rw [hFs v w, hF's v w],
      h.cfiFlipAut_xorF F F' hF hF'⟩
  inv_mem' := by
    rintro a ⟨F, hF, hFs, rfl⟩
    have hinv : h.cfiFlipAut F hF * h.cfiFlipAut F hF = 1 :=
      Equiv.ext fun v => by
        rw [Equiv.Perm.mul_apply, h.cfiFlipAut_involutive F hF v, Equiv.Perm.one_apply]
    rw [inv_eq_of_mul_eq_one_right hinv]
    exact ⟨F, hF, hFs, rfl⟩

@[simp] theorem mem_gaugeSubgroup (h : IsCFI' adj) {g : Equiv.Perm (Fin n)} :
    g ∈ gaugeSubgroup h ↔ g ∈ cfiGaugeGens h := Iff.rfl

/-- The closure of the gauge generators *is* the gauge subgroup — they already form a subgroup. -/
theorem closure_cfiGaugeGens_eq (h : IsCFI' adj) :
    Subgroup.closure (cfiGaugeGens h) = gaugeSubgroup h :=
  le_antisymm ((Subgroup.closure_le _).mpr (fun _ hg => hg))
    (fun _ hg => Subgroup.subset_closure hg)

/-- **The gauge group is exponent-2 (elementary-abelian).** Every gauge generator is a flip `cfiFlipAut F`,
and flips are involutions (`cfiFlipAut_involutive`), so `g * g = 1`. The exponent-2 fact the de-classed
coverage `coversOrbits_of_residualInvolutive` needs of the residual, supplied here for the gauge group. -/
theorem cfiGauge_mul_self (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ cfiGaugeGens h) : g * g = 1 := by
  obtain ⟨F, hF, _, rfl⟩ := hg
  exact Equiv.ext fun v => by
    rw [Equiv.Perm.mul_apply, h.cfiFlipAut_involutive F hF v, Equiv.Perm.one_apply]

/-- **`cfi_coversOrbits` — the CFI coverage witness, via de-classing (no structure theorem).** Given
**gauge-generation** (`hgen`: every `P`-preserving automorphism is a product of gauge flips), the odd-degree
CFI graph's gauge flips cover every level's residual orbit along the base sequence — discharging the
A2-complete `CoversOrbits`. Obtained from `coversOrbits_of_residualInvolutive`: gauge-generation makes the
residual exponent-2 (`ResidualInvolutive`, via `cfiGauge_mul_self`) and puts every residual automorphism in
`cfiGaugeGens` (`hgens`), with **no** `Φ(σ)` lift or semidirect decomposition. This is the long-sought
`cfi_coversOrbits`, reached by de-classing the per-class structure theorem down to the single `hgen`.
(No `P`-invariance hypothesis is needed: the coverage follows purely from gauge-generation and the
exponent-2 structure of the gauge group.) -/
theorem cfi_coversOrbits (h : IsCFI' adj) (h_odd : h.OddDegree)
    (hgen : StabilizerAt adj P ∅ ≤ Subgroup.closure (cfiGaugeGens h)) :
    ∃ bs : List (Fin n), CoversOrbits adj P (cfiGaugeGens h) bs ∅ := by
  obtain ⟨bs, hbase⟩ := cfi_exists_base_seq (P := P) h h_odd
  refine ⟨bs, coversOrbits_of_residualInvolutive bs ?_ ?_ hbase⟩
  · intro g hg
    have hgc : g ∈ cfiGaugeGens h := by
      have := hgen (mem_stabilizerAt.mpr hg); rwa [closure_cfiGaugeGens_eq, mem_gaugeSubgroup] at this
    exact cfiGauge_mul_self h hgc
  · intro g hg _
    have := hgen (mem_stabilizerAt.mpr hg); rwa [closure_cfiGaugeGens_eq, mem_gaugeSubgroup] at this

/-- **CFI cross-branch harvest completeness, via de-classing.** With gauge-generation the harvested gauge
chain *is* the residual `P`-preserving automorphism group: `closure (cfiGaugeGens h) = StabilizerAt adj P ∅`.
(The `≤` is free — `cfiGaugeGens_residualAut_empty`; `hgen` supplies the `≥`.) The de-classed coverage's
genuine new content is the *order* below; this equality also follows directly from the two containments. -/
theorem cfi_closure_eq_stabilizerAt (h : IsCFI' adj)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (hgen : StabilizerAt adj P ∅ ≤ Subgroup.closure (cfiGaugeGens h)) :
    Subgroup.closure (cfiGaugeGens h) = StabilizerAt adj P ∅ :=
  le_antisymm
    ((Subgroup.closure_le _).mpr
      (fun g hg => mem_stabilizerAt.mpr (cfiGaugeGens_residualAut_empty h hP g hg)))
    hgen

/-- **`|Aut(CFI(H))^P| = ∏ basic-orbit sizes`, via the harvested gauge chain.** With gauge-generation, the
order of the residual `P`-preserving automorphism group is the basic-orbit-size product along the CFI base
sequence — the `Order = ∏ OrbitSize` of `PermutationGroup.cs`, for CFI, computed from the *folded* gauge
generators. The genuine de-classed payoff: it needs the full coverage chain (`cfi_coversOrbits` →
`card_closure_gensAt_eq_prod_of_coversOrbits`), not just the two containments of the group equality. -/
theorem cfi_card_stabilizerAt_eq_prod (h : IsCFI' adj) (h_odd : h.OddDegree)
    (hP : ∀ (π : Equiv.Perm (Fin n)), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (hgen : StabilizerAt adj P ∅ ≤ Subgroup.closure (cfiGaugeGens h)) :
    ∃ bs : List (Fin n), Nat.card (StabilizerAt adj P ∅) = orbitSizeProd adj P bs ∅ := by
  obtain ⟨bs, hcov⟩ := cfi_coversOrbits h h_odd hgen
  refine ⟨bs, ?_⟩
  have hge : gensAt adj P (cfiGaugeGens h) ∅ = cfiGaugeGens h :=
    gensAt_empty_eq (fun g hg => mem_stabilizerAt.mpr (cfiGaugeGens_residualAut_empty h hP g hg))
  have hcard := card_closure_gensAt_eq_prod_of_coversOrbits bs hcov
  rw [hge] at hcard
  rwa [cfi_closure_eq_stabilizerAt h hP hgen] at hcard

/-! ### Part A (Stage A2-complete) — CFI-cov.4 (the gauge nut): `ResidualInvolutive` via P-separation

The de-classed coverage (`coversOrbits_of_residualInvolutive`) reduced the CFI harvest to the **faithful**
hypothesis `ResidualInvolutive adj P S` (the residual is exponent-2), *strictly weaker* than gauge-generation
(`g² = 1`, not "`g` is a literal cycle-space flip"). This block discharges `ResidualInvolutive` for CFI in
the **base-resolved regime** — where the committed individualization, through the partial order `P`, already
distinguishes gadgets (the `Aut(H)` factor killed). That regime is exactly the decomposability premise
(calculator §7): resolve the cascading base layer first, leaving the gauge `Z₂^β` as a clean exponent-2
residual.

**The key move (Lemma A): gadget-preservation comes from `P`-preservation, not from a structural recovery
argument.** A residual automorphism fixes the committed set `S` pointwise *and* preserves `P`, so it
preserves each vertex's `P`-relations to `S` (`P (g x) s = P (g x)(g s) = P x s`). If those relations
determine the gadget (`PSeparatesGadgets`), `g` fixes gadgets — sidestepping the subtle "every CFI
automorphism preserves gadgets" (which would need a graph-recovery proof). Full plan:
[`docs/chain-descent-cfi-gauge-discharge-plan.md`](../../../docs/chain-descent-cfi-gauge-discharge-plan.md). -/

/-- The **gadget (base vertex) of a CFI vertex** `x : Fin n`, through the CFI labelling `h.e`. -/
def gadgetOf (h : IsCFI' adj) (x : Fin n) : Fin h.m := h.H.gadget (h.e x)

/-- **`P` separates gadgets** — the honest "base layer resolved" hypothesis. The committed set `S`, through
the partial order `P` it induces, distinguishes gadgets: if two vertices have the same `P`-relations to every
committed vertex, they live in the same gadget. This is what makes a residual automorphism (which preserves
those relations) fix gadgets, with no structural gadget-recovery argument. -/
def PSeparatesGadgets (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) (h : IsCFI' adj) : Prop :=
  ∀ x y : Fin n, (∀ s ∈ S, P x s = P y s) → gadgetOf h x = gadgetOf h y

/-- **Lemma A — gadget-preservation from `P`-separation.** A residual automorphism `g` (fixing the committed
set `S` pointwise and preserving `P`) preserves each vertex's `P`-relations to `S`
(`P (g x) s = P (g x)(g s) = P x s`), so under `PSeparatesGadgets` it fixes every gadget:
`gadgetOf (g x) = gadgetOf x`. The reduction that replaces the subtle structural "CFI automorphisms preserve
gadgets" with an honest hypothesis on `P` (the base-resolved regime). -/
theorem gadgetPreserving_of_pSeparates (h : IsCFI' adj) {S : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} (hg : ResidualAut adj P S g)
    (hsep : PSeparatesGadgets adj P S h) :
    ∀ x, gadgetOf h (g x) = gadgetOf h x := by
  intro x
  refine hsep (g x) x (fun s hs => ?_)
  have hgs : g s = s := hg.2.2 s hs
  have hP : P (g x) (g s) = P x s := hg.2.1 x s
  rwa [hgs] at hP

/-- **`warmRefine` separates gadgets** — the colour-model "base layer resolved" hypothesis, matching the
recovery framework (fresh-colour individualization of `S`) rather than the `P`-relation form
`PSeparatesGadgets`. Two vertices in the same `warmRefine` cell (after individualizing `S`) live in the
same gadget. This is the form the descent's actual mechanism can discharge: with the recovery framework's
trivial `P`, `PSeparatesGadgets` is vacuously *false* (no `P`-relation distinguishes anything), but the
`warmRefine` colouring does the separating — and the cascade discretizes it at a gadget-resolving `S`. -/
def CellSeparatesGadgets (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) (h : IsCFI' adj) : Prop :=
  ∀ x y : Fin n,
    warmRefine adj P (individualizedColouring n S) x
      = warmRefine adj P (individualizedColouring n S) y →
    gadgetOf h x = gadgetOf h y

/-- **Lemma A, colour model — gadget-preservation from cell-separation.** A residual automorphism `g`
preserves `(adj, P)` and fixes `S` pointwise, so it preserves the `warmRefine` partition of the
`S`-individualized colouring (`warmRefine (g x) = warmRefine x`, via `warmRefine_invariant_of_isAut` +
`individualizedColouring_invariant`); under `CellSeparatesGadgets` it therefore fixes every gadget. The
colour-model counterpart of `gadgetPreserving_of_pSeparates`, dischargeable by the cascade (`warmRefine`
discreteness at a gadget-resolving `S`) where the `P`-relation form is not (trivial `P` ⟹ that form
vacuously false). -/
theorem gadgetPreserving_of_cellSeparates (h : IsCFI' adj) {S : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} (hg : ResidualAut adj P S g)
    (hsep : CellSeparatesGadgets adj P S h) :
    ∀ x, gadgetOf h (g x) = gadgetOf h x := by
  intro x
  refine hsep (g x) x ?_
  exact warmRefine_invariant_of_isAut hg.1 hg.2.1
    (fun v => individualizedColouring_invariant hg.2.2 v) x

/-! #### CFI-cov.4 Lemma B — a gadget-fixing CFI automorphism is an involution

Building blocks first (data/adjacency helpers), then the three steps (type preservation, `g²` fixes
endpoints, `g²` fixes subsets), then the assembly `cfiAut_gadgetFixing_mul_self`. Plan:
[`docs/chain-descent-cfi-gauge-discharge-plan.md`](../../../docs/chain-descent-cfi-gauge-discharge-plan.md) §4. -/

/-- `gadgetOf` of a subset vertex is its gadget. -/
@[simp] theorem gadgetOf_subsetVertex (h : IsCFI' adj) {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) : gadgetOf h (h.subsetVertex hS) = v := by
  unfold gadgetOf; rw [h.e_subsetVertex]; rfl

/-- `gadgetOf` of an endpoint vertex is its gadget. -/
@[simp] theorem gadgetOf_endpointVertex (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) : gadgetOf h (h.endpointVertex hw b) = v := by
  unfold gadgetOf; rw [h.e_endpointVertex]; rfl

/-- **Vertex destructor.** Every `x : Fin n` is a subset vertex or an endpoint vertex of the CFI graph. -/
theorem exists_vertex_form (h : IsCFI' adj) (x : Fin n) :
    (∃ (v : Fin h.m) (S : Finset (Fin h.m)) (hS : S ∈ h.H.evenSubsetsOfNeighbors v),
        x = h.subsetVertex hS) ∨
    (∃ (v w : Fin h.m) (hw : w ∈ h.H.neighbors v) (b : Bool), x = h.endpointVertex hw b) := by
  rcases hex : h.e x with ⟨v, S, hS⟩ | ⟨v, ⟨w, hw⟩, b⟩
  · refine Or.inl ⟨v, S, hS, h.e.injective ?_⟩
    rw [h.e_subsetVertex, hex]; rfl
  · refine Or.inr ⟨v, w, hw, b, h.e.injective ?_⟩
    rw [h.e_endpointVertex, hex]; rfl

/-- Endpoint vertices at the same gadget/direction are equal only for equal parity bits. -/
theorem endpointVertex_bool_inj (h : IsCFI' adj) {v w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {b₁ b₂ : Bool} (heq : h.endpointVertex hw b₁ = h.endpointVertex hw b₂) : b₁ = b₂ := by
  have h2 : h.H.endpoint hw b₁ = h.H.endpoint hw b₂ := by
    have := congrArg h.e heq; rwa [h.e_endpointVertex, h.e_endpointVertex] at this
  rw [CFIBase.endpoint, CFIBase.endpoint] at h2
  simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h2
  exact h2

/-- Endpoint vertices at gadget `v` are equal only for equal direction and parity. -/
theorem endpointVertex_inj (h : IsCFI' adj) {v w₁ w₂ : Fin h.m}
    (hw₁ : w₁ ∈ h.H.neighbors v) (hw₂ : w₂ ∈ h.H.neighbors v) {b₁ b₂ : Bool}
    (heq : h.endpointVertex hw₁ b₁ = h.endpointVertex hw₂ b₂) : w₁ = w₂ ∧ b₁ = b₂ := by
  have h2 : h.H.endpoint hw₁ b₁ = h.H.endpoint hw₂ b₂ := by
    have := congrArg h.e heq; rwa [h.e_endpointVertex, h.e_endpointVertex] at this
  rw [CFIBase.endpoint, CFIBase.endpoint] at h2
  simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq, true_and] at h2
  exact h2

/-- **A subset vertex's membership is read off its adjacency to the `b=false` endpoints.**
`w ∈ S ↔ e^0_{v→w} ~ a_S^v`. The fact that lets `g²` (fixing endpoints) pin a subset vertex. -/
theorem subset_mem_iff_adj (h : IsCFI' adj) {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) {w : Fin h.m} (hw : w ∈ h.H.neighbors v) :
    adj.adj (h.endpointVertex hw false) (h.subsetVertex hS) = 1 ↔ w ∈ S := by
  rw [h.adj_subsetVertex_eq_one_iff hS (h.endpointVertex hw false)]
  constructor
  · rintro ⟨w', hw', b, hpar, heq⟩
    obtain ⟨hww, hbb⟩ := endpointVertex_inj h hw hw' heq
    subst hww; subst hbb
    simpa using hpar
  · intro hwS
    exact ⟨w, hw, false, by simp [hwS], rfl⟩

/-- **Has a cross-gadget neighbour.** The structural distinguisher of endpoint vertices: an endpoint has a
bridge neighbour in another gadget, a subset vertex's neighbours are all in its own gadget. -/
def isEndpt (h : IsCFI' adj) (x : Fin n) : Prop :=
  ∃ y, adj.adj x y = 1 ∧ gadgetOf h y ≠ gadgetOf h x

/-- An endpoint vertex has a cross-gadget neighbour (its bridge partner). -/
theorem isEndpt_endpointVertex (h : IsCFI' adj) {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) (b : Bool) :
    isEndpt h (h.endpointVertex hw b) := by
  refine ⟨h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b, ?_, ?_⟩
  · rw [h.adj_endpointVertex_eq_one_iff]; exact ⟨rfl, rfl, rfl⟩
  · simp only [gadgetOf_endpointVertex]
    intro heq
    exact h.H.not_self_mem_neighbors v (heq ▸ hw)

/-- A subset vertex has no cross-gadget neighbour (all its neighbours are endpoints at its gadget). -/
theorem not_isEndpt_subsetVertex (h : IsCFI' adj) {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) : ¬ isEndpt h (h.subsetVertex hS) := by
  rintro ⟨y, hadj, hg⟩
  rw [h.adj_symm] at hadj
  obtain ⟨w', hw', b, _, rfl⟩ := (h.adj_subsetVertex_eq_one_iff hS y).mp hadj
  apply hg
  rw [gadgetOf_endpointVertex, gadgetOf_subsetVertex]

/-- **`isEndpt` is automorphism-invariant** for a gadget-fixing automorphism: substitute `y = g z`. -/
theorem isEndpt_equivariant (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x) (x : Fin n) :
    isEndpt h (g x) ↔ isEndpt h x := by
  constructor
  · rintro ⟨y, hadj, hg⟩
    refine ⟨g.symm y, ?_, ?_⟩
    · have h1 := hAut x (g.symm y); rw [Equiv.apply_symm_apply] at h1; rw [← h1]; exact hadj
    · have e1 := hfix (g.symm y); rw [Equiv.apply_symm_apply] at e1
      rw [← e1, ← hfix x]; exact hg
  · rintro ⟨z, hadj, hg⟩
    exact ⟨g z, by rw [hAut x z]; exact hadj, by rw [hfix z, hfix x]; exact hg⟩

/-- **B1 (type preservation, endpoints).** A gadget-fixing automorphism maps an endpoint vertex to an
endpoint vertex at the same gadget. -/
theorem gadgetFixingAut_endpoint (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) (b : Bool) :
    ∃ (w' : Fin h.m) (hw' : w' ∈ h.H.neighbors v) (b' : Bool),
      g (h.endpointVertex hw b) = h.endpointVertex hw' b' := by
  have hE : isEndpt h (g (h.endpointVertex hw b)) :=
    (isEndpt_equivariant h hAut hfix _).mpr (isEndpt_endpointVertex h hw b)
  rcases exists_vertex_form h (g (h.endpointVertex hw b)) with ⟨v2, S2, hS2, hx⟩ | ⟨v2, w2, hw2, b2, hx⟩
  · exact absurd (hx ▸ hE) (not_isEndpt_subsetVertex h hS2)
  · have hgad : gadgetOf h (g (h.endpointVertex hw b)) = v := by
      rw [hfix (h.endpointVertex hw b), gadgetOf_endpointVertex]
    rw [hx, gadgetOf_endpointVertex] at hgad
    subst hgad
    exact ⟨w2, hw2, b2, hx⟩

/-- **B1 (type preservation, subsets).** A gadget-fixing automorphism maps a subset vertex to a subset
vertex at the same gadget. -/
theorem gadgetFixingAut_subset (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x)
    {v : Fin h.m} {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v) :
    ∃ (S' : Finset (Fin h.m)) (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v),
      g (h.subsetVertex hS) = h.subsetVertex hS' := by
  have hNE : ¬ isEndpt h (g (h.subsetVertex hS)) := by
    rw [isEndpt_equivariant h hAut hfix]; exact not_isEndpt_subsetVertex h hS
  rcases exists_vertex_form h (g (h.subsetVertex hS)) with ⟨v2, S2, hS2, hx⟩ | ⟨v2, w2, hw2, b2, hx⟩
  · have hgad : gadgetOf h (g (h.subsetVertex hS)) = v := by
      rw [hfix (h.subsetVertex hS), gadgetOf_subsetVertex]
    rw [hx, gadgetOf_subsetVertex] at hgad
    subst hgad
    exact ⟨S2, hS2, hx⟩
  · exact absurd (isEndpt_endpointVertex h hw2 b2) (hx ▸ hNE)

/-- **B2 (direction preservation).** A gadget-fixing automorphism maps `e^b_{v→w}` to `e^{b'}_{v→w}` (the
bridge target `w` is preserved): only the parity bit may change. -/
theorem gadgetFixingAut_dir (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) (b : Bool) :
    ∃ b', g (h.endpointVertex hw b) = h.endpointVertex hw b' := by
  obtain ⟨w', hw', b', hx⟩ := gadgetFixingAut_endpoint h hAut hfix hw b
  obtain ⟨w'', hw'', b'', hy⟩ := gadgetFixingAut_endpoint h hAut hfix (h.H.mem_neighbors_symm.mp hw) b
  have hbridge : adj.adj (h.endpointVertex hw b)
      (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b) = 1 := by
    rw [h.adj_endpointVertex_eq_one_iff]; exact ⟨rfl, rfl, rfl⟩
  have hg : adj.adj (h.endpointVertex hw' b') (h.endpointVertex hw'' b'') = 1 := by
    rw [← hx, ← hy, hAut]; exact hbridge
  rw [h.adj_endpointVertex_eq_one_iff] at hg
  obtain ⟨_, hw'w, _⟩ := hg
  subst hw'w
  exact ⟨b', hx⟩

/-- **B2 (`g²` fixes endpoints).** A gadget-fixing automorphism maps the parity pair `{e^0_{v→w}, e^1_{v→w}}`
into itself (direction preserved, `gadgetFixingAut_dir`); being injective on a 2-element set, it squares to
the identity there. -/
theorem mulSelf_endpoint (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) (b : Bool) :
    g (g (h.endpointVertex hw b)) = h.endpointVertex hw b := by
  obtain ⟨b1, h1⟩ := gadgetFixingAut_dir h hAut hfix hw b
  obtain ⟨b2, h2⟩ := gadgetFixingAut_dir h hAut hfix hw b1
  have key : b2 = b := by
    by_cases hb1b : b1 = b
    · subst hb1b
      exact (endpointVertex_bool_inj h hw (h1.symm.trans h2)).symm
    · by_cases hb2b1 : b2 = b1
      · exfalso; subst hb2b1
        exact hb1b (endpointVertex_bool_inj h hw (g.injective (h1.trans h2.symm))).symm
      · have bp : ∀ {a x y : Bool}, x ≠ a → y ≠ x → y = a := by decide
        exact bp hb1b hb2b1
  rw [h1, h2, key]

/-- **B3 (`g²` fixes subsets).** `g²` preserves adjacency and fixes every endpoint (B2), so a subset vertex
and its `g²`-image have identical adjacency to all endpoints; a subset vertex is determined by that
(`subset_mem_iff_adj`), so `g²` fixes it. -/
theorem mulSelf_subset (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x)
    {v : Fin h.m} {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v) :
    g (g (h.subsetVertex hS)) = h.subsetVertex hS := by
  obtain ⟨S1, hS1, h1⟩ := gadgetFixingAut_subset h hAut hfix hS
  obtain ⟨S2, hS2, h2⟩ := gadgetFixingAut_subset h hAut hfix hS1
  rw [h1, h2]
  have hSsub : S ⊆ h.H.neighbors v := (h.H.mem_evenSubsetsOfNeighbors.mp hS).1
  have hS2sub : S2 ⊆ h.H.neighbors v := (h.H.mem_evenSubsetsOfNeighbors.mp hS2).1
  have hSeq : S2 = S := by
    ext w
    by_cases hw : w ∈ h.H.neighbors v
    · have ha := mulSelf_endpoint h hAut hfix hw false
      have hb : g (g (h.subsetVertex hS)) = h.subsetVertex hS2 := by rw [h1, h2]
      have step : adj.adj (g (g (h.endpointVertex hw false))) (g (g (h.subsetVertex hS)))
                = adj.adj (h.endpointVertex hw false) (h.subsetVertex hS) := by rw [hAut, hAut]
      rw [ha, hb] at step
      constructor
      · intro hwS2
        exact (subset_mem_iff_adj h hS hw).mp (step.symm.trans ((subset_mem_iff_adj h hS2 hw).mpr hwS2))
      · intro hwS
        exact (subset_mem_iff_adj h hS2 hw).mp (step.trans ((subset_mem_iff_adj h hS hw).mpr hwS))
    · constructor
      · intro hwS2; exact absurd (hS2sub hwS2) hw
      · intro hwS; exact absurd (hSsub hwS) hw
  subst hSeq
  rfl

/-- **Lemma B — a gadget-fixing CFI automorphism is an involution.** `IsAut g adj` together with
gadget-preservation (`hfix`) forces `g * g = 1`: by the destructor every vertex is a subset (B3) or endpoint
(B2) vertex, and `g²` fixes both. Combined with Lemma A (`gadgetPreserving_of_pSeparates`), this discharges
`ResidualInvolutive` for CFI in the base-resolved (`PSeparatesGadgets`) regime. -/
theorem cfiAut_gadgetFixing_mul_self (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x) :
    g * g = 1 := by
  refine Equiv.ext (fun x => ?_)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases exists_vertex_form h x with ⟨v, S, hS, rfl⟩ | ⟨v, w, hw, b, rfl⟩
  · exact mulSelf_subset h hAut hfix hS
  · exact mulSelf_endpoint h hAut hfix hw b

/-- **CFI-cov.4 capstone — `ResidualInvolutive` for CFI in the base-resolved regime (Lemma A + Lemma B).**
Where the committed `P` separates gadgets (`PSeparatesGadgets`, the `Aut(H)` factor killed), every residual
automorphism fixes gadgets (Lemma A, `gadgetPreserving_of_pSeparates`) and a gadget-fixing CFI automorphism
is an involution (Lemma B, `cfiAut_gadgetFixing_mul_self`), so the residual is exponent-2. This is the CFI
witness the de-classed `coversOrbits_of_residualInvolutive` consumes — discharged with **no** structure
theorem, no `Φ(σ)` lift, no gauge-flip identification. (The remaining input is a base sequence from `S`, which
feeds the harvest completeness + order.) -/
theorem cfi_residualInvolutive (h : IsCFI' adj) {S : Finset (Fin n)}
    (hsep : PSeparatesGadgets adj P S h) : ResidualInvolutive adj P S :=
  fun _g hg => cfiAut_gadgetFixing_mul_self h hg.1 (gadgetPreserving_of_pSeparates h hg hsep)

/-! #### CFI-cov.4 — the harvest wiring at a base-resolved `S`

With `cfi_residualInvolutive` supplying the exponent-2 hypothesis, the de-classed coverage discharges the
cross-branch harvest at any base-resolved `S` — *provided a base sequence from `S`*. The cascade gives a base
at `allSeeds` (`theorem_1_HOR_cfi_oddDeg`); since `IsBase` is upward-closed, `(allSeeds \ S).toList` is a base
sequence from `S`. The headline is at a **nonempty** `S` (`PSeparatesGadgets` at `∅` is vacuously false), so
the order is the gauge-layer residual order, matching the decomposability picture. -/

/-- **`IsBase` is upward-closed.** Individualizing more can only shrink the residual, so a base stays a base:
`IsBase adj P S → S ⊆ T → IsBase adj P T`. -/
theorem isBase_mono {S T : Finset (Fin n)} (hbase : IsBase adj P S) (hST : S ⊆ T) :
    IsBase adj P T := by
  rw [← stabilizerAt_eq_bot_iff_isBase] at hbase ⊢
  rw [eq_bot_iff] at hbase ⊢
  exact le_trans (stabilizerAt_mono hST) hbase

/-- **A base sequence from any `S`** for an odd-degree CFI graph: the cascade discretizes at `allSeeds`
(`theorem_1_HOR_cfi_oddDeg`), giving `IsBase allSeeds`; appending `allSeeds \ S` to `S` reaches a superset of
`allSeeds`, still a base by `isBase_mono`. Generalizes `cfi_exists_base_seq` (the `S = ∅` case). -/
theorem cfi_exists_base_seq_from (h : IsCFI' adj) (h_odd : h.OddDegree) (S : Finset (Fin n)) :
    ∃ bs : List (Fin n), IsBase adj P (bs.foldl (fun acc b => insert b acc) S) := by
  obtain ⟨S₀, _, hd, _⟩ := h.theorem_1_HOR_cfi_oddDeg h_odd P
  have hbase₀ : IsBase adj P S₀ := isBase_of_discrete_warmRefine hd
  refine ⟨(S₀ \ S).toList, ?_⟩
  rw [foldl_insert_eq_union, Finset.toList_toFinset]
  refine isBase_mono hbase₀ (fun x hx => ?_)
  by_cases hxS : x ∈ S
  · exact Finset.mem_union_left _ hxS
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)

/-- **CFI cross-branch harvest completeness in the base-resolved regime.** Where `P` separates gadgets at a
committed set `S` (`PSeparatesGadgets`, so the residual is the exponent-2 gauge group), the closure of the
harvested involutive residual automorphisms *is* the residual: `closure {g | ResidualAut adj P S g ∧ g²=1} =
StabilizerAt adj P S`. Via `cfi_residualInvolutive` + the de-classed `closure_eq_stabilizerAt_of_residualInvolutive`
over the base sequence `cfi_exists_base_seq_from` — **no** structure theorem, no `Φ(σ)` lift. -/
theorem cfi_closure_eq_stabilizerAt_of_pSeparates (h : IsCFI' adj) (h_odd : h.OddDegree)
    {S : Finset (Fin n)} (hsep : PSeparatesGadgets adj P S h) :
    Subgroup.closure {g | ResidualAut adj P S g ∧ g * g = 1} = StabilizerAt adj P S := by
  obtain ⟨bs, hbase⟩ := cfi_exists_base_seq_from (P := P) h h_odd S
  have hgensAt : gensAt adj P {g | ResidualAut adj P S g ∧ g * g = 1} S
               = {g | ResidualAut adj P S g ∧ g * g = 1} :=
    Set.Subset.antisymm (fun g hg => hg.1) (fun g hg => ⟨hg, mem_stabilizerAt.mpr hg.1⟩)
  have hmain := stabilizerAt_eq_closure_gensAt_of_coversOrbits (gens := {g | ResidualAut adj P S g ∧ g * g = 1})
    bs (coversOrbits_of_residualInvolutive bs (cfi_residualInvolutive h hsep)
      (fun g hg hginv => ⟨hg, hginv⟩) hbase)
  rwa [hgensAt] at hmain

/-- **`|Aut_S^P| = ∏ basic-orbit sizes` in the base-resolved regime.** Where `P` separates gadgets at `S`,
the order of the residual group is the basic-orbit-size product along the CFI base sequence — the gauge-layer
`Order = ∏ OrbitSize` of `PermutationGroup.cs`, computed from the folded involutive generators. The genuine
de-classed payoff (needs the full coverage chain). -/
theorem cfi_card_stabilizerAt_of_pSeparates (h : IsCFI' adj) (h_odd : h.OddDegree)
    {S : Finset (Fin n)} (hsep : PSeparatesGadgets adj P S h) :
    ∃ bs : List (Fin n), Nat.card (StabilizerAt adj P S) = orbitSizeProd adj P bs S := by
  obtain ⟨bs, hbase⟩ := cfi_exists_base_seq_from (P := P) h h_odd S
  refine ⟨bs, ?_⟩
  have hcov := coversOrbits_of_residualInvolutive (gens := {g | ResidualAut adj P S g ∧ g * g = 1})
    bs (cfi_residualInvolutive h hsep) (fun g hg hginv => ⟨hg, hginv⟩) hbase
  have hcard := card_closure_gensAt_eq_prod_of_coversOrbits bs hcov
  rwa [stabilizerAt_eq_closure_gensAt_of_coversOrbits bs hcov] at hcard

/-! #### CFI-cov.4 — the harvest wiring on the colour model (`CellSeparatesGadgets`)

The `PSeparatesGadgets` versions above are stated over `P`-relations, but the descent's CFI recovery runs on
trivial `P` + colour individualization, where `PSeparatesGadgets` is **vacuously false** (no `P`-relation
distinguishes anything, and it is vacuous at `S=∅`). The colour-model `CellSeparatesGadgets` is the
dischargeable form — separation lives in the `warmRefine` colouring, which the cascade discretizes. These
re-wire `cfi_residualInvolutive` / `cfi_closure_eq_stabilizerAt` / `cfi_card_stabilizerAt` onto it, via the
colour-model Lemma A (`gadgetPreserving_of_cellSeparates`); the existing Lemma B
(`cfiAut_gadgetFixing_mul_self`) is reused verbatim (it is independent of how gadget-preservation is obtained).
They **supersede** the `pSeparates` versions for consuming the descent's actual mechanism. -/

/-- **CFI-cov.4 capstone, colour model — `ResidualInvolutive` from cell-separation (Lemma A colour + Lemma B).**
Where `warmRefine` separates gadgets at `S` (`CellSeparatesGadgets`), every residual automorphism fixes gadgets
(`gadgetPreserving_of_cellSeparates`) and a gadget-fixing CFI automorphism is an involution
(`cfiAut_gadgetFixing_mul_self`), so the residual is exponent-2. The dischargeable counterpart of
`cfi_residualInvolutive` (which keys on the vacuous-on-trivial-`P` `PSeparatesGadgets`). -/
theorem cfi_residualInvolutive_cell (h : IsCFI' adj) {S : Finset (Fin n)}
    (hsep : CellSeparatesGadgets adj P S h) : ResidualInvolutive adj P S :=
  fun _g hg => cfiAut_gadgetFixing_mul_self h hg.1 (gadgetPreserving_of_cellSeparates h hg hsep)

/-- **Cascade bridge — `CellSeparatesGadgets` from `warmRefine` discreteness.** When the cascade discretizes
the `S`-individualized colouring (every cell a singleton, e.g. `theorem_1_HOR_cfi_oddDeg` at `allSeeds`), the
colour-model separation holds for free: same cell ⟹ same vertex ⟹ same gadget. The connection from the proven
CFI cascade to the colour-model base-resolved hypothesis (the `P`-form had no such bridge). -/
theorem cellSeparatesGadgets_of_discrete (h : IsCFI' adj) {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S))) :
    CellSeparatesGadgets adj P S h :=
  fun x y hxy => by rw [hd x y hxy]

/-- **CFI cross-branch harvest completeness, colour model.** Where `warmRefine` separates gadgets at `S`, the
closure of the harvested involutive residual automorphisms *is* the residual:
`closure {g | ResidualAut adj P S g ∧ g²=1} = StabilizerAt adj P S`. Colour-model counterpart of
`cfi_closure_eq_stabilizerAt_of_pSeparates`, dischargeable by the cascade (`cellSeparatesGadgets_of_discrete`). -/
theorem cfi_closure_eq_stabilizerAt_of_cellSeparates (h : IsCFI' adj) (h_odd : h.OddDegree)
    {S : Finset (Fin n)} (hsep : CellSeparatesGadgets adj P S h) :
    Subgroup.closure {g | ResidualAut adj P S g ∧ g * g = 1} = StabilizerAt adj P S := by
  obtain ⟨bs, hbase⟩ := cfi_exists_base_seq_from (P := P) h h_odd S
  have hgensAt : gensAt adj P {g | ResidualAut adj P S g ∧ g * g = 1} S
               = {g | ResidualAut adj P S g ∧ g * g = 1} :=
    Set.Subset.antisymm (fun g hg => hg.1) (fun g hg => ⟨hg, mem_stabilizerAt.mpr hg.1⟩)
  have hmain := stabilizerAt_eq_closure_gensAt_of_coversOrbits (gens := {g | ResidualAut adj P S g ∧ g * g = 1})
    bs (coversOrbits_of_residualInvolutive bs (cfi_residualInvolutive_cell h hsep)
      (fun g hg hginv => ⟨hg, hginv⟩) hbase)
  rwa [hgensAt] at hmain

/-- **`|Aut_S^P| = ∏ basic-orbit sizes`, colour model.** Where `warmRefine` separates gadgets at `S`, the
residual order is the basic-orbit-size product along the CFI base sequence. Colour-model counterpart of
`cfi_card_stabilizerAt_of_pSeparates`. -/
theorem cfi_card_stabilizerAt_of_cellSeparates (h : IsCFI' adj) (h_odd : h.OddDegree)
    {S : Finset (Fin n)} (hsep : CellSeparatesGadgets adj P S h) :
    ∃ bs : List (Fin n), Nat.card (StabilizerAt adj P S) = orbitSizeProd adj P bs S := by
  obtain ⟨bs, hbase⟩ := cfi_exists_base_seq_from (P := P) h h_odd S
  refine ⟨bs, ?_⟩
  have hcov := coversOrbits_of_residualInvolutive (gens := {g | ResidualAut adj P S g ∧ g * g = 1})
    bs (cfi_residualInvolutive_cell h hsep) (fun g hg hginv => ⟨hg, hginv⟩) hbase
  have hcard := card_closure_gensAt_eq_prod_of_coversOrbits bs hcov
  rwa [stabilizerAt_eq_closure_gensAt_of_coversOrbits bs hcov] at hcard

/-! #### CFI base-graph projection — discharging `CellSeparatesGadgets` from base identification

`CellSeparatesGadgets` at a non-trivial (gauge-remaining) `S` is **substrate-conditional on the base `H`**:
it holds exactly when 1-WL identifies `H`'s vertices — the gadget-level analogue of `RecoverableByDepth`,
false when 1-WL cannot crack `H`.

**Design (settled): `CellSeparatesGadgets` is carried as a WITNESS, not proved.** Following the project's
recovery pattern (`RecoverableByDepth` / `CellsAreOrbits`), base-identification is a substrate-conditional
*witness* the harvest consumes (`cfi_closure_eq_stabilizerAt_of_cellSeparates`), with
`cellSeparatesGadgets_of_discrete` discharging the full-discreteness base case. The *implication* "1-WL
identifies `H` ⟹ `CellSeparatesGadgets`" is a genuine theorem but heavy (a base-relative CFI cascade); its
only payoff would be a non-vacuity *demonstration*, so it is deferred to a future witness-discharge.

What is **landed** here is the structural foundation that makes any such projection well-defined: CFI
refinement projects onto base-graph refinement along the gadget map — **Brick 1**
(`gadget_mem_neighbors_of_adj_cross`: cross-gadget adjacency is a base-graph edge) and its **sharpening**
(`endpoint_crossGadget_gadget`: the cross-gadget neighbour lands in the bridge-target gadget exactly). -/

/-- **Brick 1 — a cross-gadget adjacency is a base-graph edge.** The only cross-gadget adjacencies in CFI(H)
are the endpoint bridges (subset vertices have only same-gadget neighbours, `not_isEndpt_subsetVertex`), and a
bridge `e^b_{v→w} ~ e^b_{w→v}` connects gadgets `v, w` that are neighbours in the base `H`
(`adj_endpointVertex_eq_one_iff`). So `adj x y = 1` with `x, y` in different gadgets forces
`gadgetOf y ∈ N_H(gadgetOf x)`: a vertex's cross-gadget neighbourhood projects onto its gadget's
`H`-neighbourhood — the structural foundation tying CFI 1-WL to base-graph 1-WL. -/
theorem gadget_mem_neighbors_of_adj_cross (h : IsCFI' adj) {x y : Fin n}
    (hadj : adj.adj x y = 1) (hg : gadgetOf h x ≠ gadgetOf h y) :
    gadgetOf h y ∈ h.H.neighbors (gadgetOf h x) := by
  rcases exists_vertex_form h x with ⟨vx, Sx, hSx, rfl⟩ | ⟨vx, wx, hwx, bx, rfl⟩
  · exact absurd ⟨y, hadj, hg.symm⟩ (not_isEndpt_subsetVertex h hSx)
  rcases exists_vertex_form h y with ⟨vy, Sy, hSy, rfl⟩ | ⟨vy, wy, hwy, by', rfl⟩
  · exact absurd ⟨h.endpointVertex hwx bx, by rw [h.adj_symm]; exact hadj, hg⟩
      (not_isEndpt_subsetVertex h hSy)
  · simp only [gadgetOf_endpointVertex] at hg ⊢
    obtain ⟨_, hwxvy, _⟩ := (h.adj_endpointVertex_eq_one_iff hwx hwy bx by').mp hadj
    rw [← hwxvy]; exact hwx

/-- **Brick 1, sharpened — an endpoint's cross-gadget neighbour lands in the bridge-target gadget.** A
cross-gadget neighbour of `e^b_{v→w}` lies in gadget `w` *exactly* (the bridge target), not merely in some
`H`-neighbour gadget: each endpoint has a *single* cross-gadget (bridge) neighbour, in gadget `w`. This pins
the projection's multiplicity — a vertex's cross-gadget neighbourhood is distributed over `N_H(gadget)` by
the bridge structure, one neighbour per outgoing endpoint direction. -/
theorem endpoint_crossGadget_gadget (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) {y : Fin n}
    (hadj : adj.adj (h.endpointVertex hw b) y = 1) (hg : gadgetOf h y ≠ v) :
    gadgetOf h y = w := by
  rcases exists_vertex_form h y with ⟨vy, Sy, hSy, rfl⟩ | ⟨vy, wy, hwy, by', rfl⟩
  · exact absurd ⟨h.endpointVertex hw b, by rw [h.adj_symm]; exact hadj,
      by simp only [gadgetOf_endpointVertex]; exact hg.symm⟩ (not_isEndpt_subsetVertex h hSy)
  · rw [gadgetOf_endpointVertex]
    obtain ⟨_, hwvy, _⟩ := (h.adj_endpointVertex_eq_one_iff hw hwy b by').mp hadj
    exact hwvy.symm

/-! ## Screen predicate D1 — visible / symmetry-only chain (leg A)

**D1**, the *unconditional / cascade* leg of the screen ([harvest-window §3](../../../docs/chain-descent-harvest-window.md)).
The symmetry is **exposed by symmetry-only individualization**: starting from `S₀`, a chain of
single-vertex individualizations — each one **symmetry-only**, i.e. the individualized vertex's cell at
that node is a single `Aut`-orbit, so no *real* decision is committed — reaches `CellsAreOrbits` at the
**end**. This admits depth-≥2-recoverable graphs (the Johnson / Hamming *graphs*, recoverable DRGs) while
still excluding CFI and the hidden Johnson *wall*: their intermediate cells are strictly coarser than
orbits, so no symmetry-only step past depth 1 can be certified — the chain gets stuck before reaching
cells = orbits. So `¬D1 ∧ ¬D2` = hidden + non-abelian = the leg-C Johnson/Cameron fingerprint.

Asymmetry with D2: `D1 ⟹ RecoverableByDepth` is *free* (the def carries cells = orbits at its endpoint),
so D1's content is the per-class *instance* check (scheme ✓ — `visiblyRecoverable_scheme`); D2's open
content was the abelian-sufficiency bridge instead.

History: this is the **multi-step** form. An earlier draft required `IsBase` (over-shot depth-1 scheme
recovery, admitted trivial-∅); a second collapsed D1-from-∅ to *one-step* recovery (cells = orbits at
every step), which would false-wall depth-≥2-recoverable graphs. The per-step *symmetry-only* condition
below is the fix — cells = orbits only at the end, each step certified symmetry-only. The bound stays
loose (≤ `n` suffices). -/

/-- **D1 — visibly recoverable.** A single-vertex, **symmetry-only** chain from `S₀` reaching
`CellsAreOrbits` within `bound`: `T 0 = S₀` (`0 < k`), each `T (i+1) = insert v (T i)` where `v`'s cell at
`T i` is a single `Aut_{T i}`-orbit (every `T i`-cellmate of `v` is `OrbitPartition`-related to it — the
step commits no real decision), and `CellsAreOrbits adj P (T k)` at the end, `|T k| ≤ bound`. The visible
/ cascade leg of the screen, relative to `S₀`. -/
def VisiblyRecoverable (adj : AdjMatrix n) (P : PMatrix n) (S₀ : Finset (Fin n))
    (bound : Nat) : Prop :=
  ∃ (k : Nat) (T : Nat → Finset (Fin n)),
    0 < k ∧
    T 0 = S₀ ∧
    (∀ i, i < k → ∃ v,
      T (i + 1) = insert v (T i) ∧
      (∀ u, warmRefine adj P (individualizedColouring n (T i)) u
            = warmRefine adj P (individualizedColouring n (T i)) v
          → OrbitPartition adj P (T i) v u)) ∧
    CellsAreOrbits adj P (T k) ∧
    (T k).card ≤ bound

/-- **The D1 leg of the harvest-window lemma.** `D1 ⟹ RecoverableByDepth` — free, since the chain ends on
a set carrying `CellsAreOrbits` within the bound. -/
theorem recoverableByDepth_of_visiblyRecoverable {S₀ : Finset (Fin n)} {bound : Nat}
    (h : VisiblyRecoverable adj P S₀ bound) : RecoverableByDepth adj P bound := by
  obtain ⟨k, T, _, _, _, hcells, hcard⟩ := h
  exact ⟨T k, hcard, hcells⟩

/-- **D1 is monotone in the depth bound** (a looser bound is easier). -/
theorem visiblyRecoverable_bound_mono {S₀ : Finset (Fin n)} {b b' : Nat}
    (h : VisiblyRecoverable adj P S₀ b) (hbb' : b ≤ b') : VisiblyRecoverable adj P S₀ b' := by
  obtain ⟨k, T, hk, hT0, hinc, hcells, hcard⟩ := h
  exact ⟨k, T, hk, hT0, hinc, hcells, le_trans hcard hbb'⟩

/-- **Schurian scheme graphs are vertex-transitive: `CellsAreOrbits adj P ∅`.** At `∅` the `Aut`-orbit
relation is total (any two vertices are related), so it trivially refines the cell relation. The witness
comes from `schurian_transitive` at the **diagonal** relation `R₀` (`rel_zero_iff_eq`): for any `a, b`,
the diagonal pairs `(a,a), (b,b)` are connected by a graph automorphism `a ↦ b`, transported to `adj`
via `matching` and made `P`-preserving by `hP_invariant`. This unblocks the symmetry-only first step. -/
theorem cellsAreOrbits_empty_of_schurian (h : IsSchurianSchemeGraph' adj)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj → ∀ x u, P (π x) (π u) = P x u) :
    CellsAreOrbits adj P ∅ := by
  intro a b _
  have hrel0a : h.G.scheme.rel 0 a a = true := (h.G.scheme.rel_zero_iff_eq a a).mpr rfl
  have hrel0b : h.G.scheme.rel 0 b b = true := (h.G.scheme.rel_zero_iff_eq b b).mpr rfl
  obtain ⟨π, hπ, hπa, _⟩ := h.G.schurian_transitive 0 a a b b hrel0a hrel0b
  have hπ' : IsAut π adj := h.matching ▸ hπ
  exact ⟨π, hπ', hP_invariant hπ', fun x hx => absurd hx (Finset.notMem_empty x), hπa⟩

/-- **`CellsAreOrbits` at a singleton (plus vertex-transitivity) gives D1 at depth 1.** The one-step chain
`∅ → {v}` is symmetry-only: `htrans` (`CellsAreOrbits adj P ∅`) certifies the step (`v`'s `∅`-cell is a
single orbit), and `hco` (`CellsAreOrbits adj P {v}`) is the endpoint recovery. The positive direction;
`visiblyRecoverable_scheme` is its scheme corollary. -/
theorem visiblyRecoverable_of_cellsAreOrbits_singleton {v : Fin n}
    (htrans : CellsAreOrbits adj P ∅) (hco : CellsAreOrbits adj P {v}) :
    VisiblyRecoverable adj P ∅ 1 := by
  refine ⟨1, fun i => match i with | 0 => ∅ | _ + 1 => {v}, Nat.one_pos, rfl, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨v, by simp, fun u hu => htrans v u hu.symm⟩
  · exact hco
  · simp

/-- **D1 instance check — the rank-2 / `|J| = 1` schurian scheme is visibly recoverable.** The one-step
chain `∅ → {v}` is symmetry-only: vertex-transitivity (`cellsAreOrbits_empty_of_schurian`) certifies the
step, and `CellsAreOrbits adj P {v}` (the proved depth-1 orbit recovery `orbitRecoverable_scheme`) is the
endpoint. Validates the *multi-step* `VisiblyRecoverable` against the proved scheme instance. -/
theorem visiblyRecoverable_scheme (h : IsSchurianSchemeGraph' adj)
    (hrank : h.G.scheme.rank = 2) (hJ : h.G.toSchemeGraph.J.card = 1) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj → ∀ x u, P (π x) (π u) = P x u) :
    VisiblyRecoverable adj P ∅ 1 :=
  visiblyRecoverable_of_cellsAreOrbits_singleton
    (cellsAreOrbits_empty_of_schurian h hP_invariant)
    (orbitRecoverableAt_iff_cellsAreOrbits.mp (orbitRecoverable_scheme h hrank hJ P v hP_invariant))

/-! ### Screen primitive — the per-decision symmetry-only step (§6.10) -/

/-- **D1, per-decision: a symmetry-only step.** At committed set `S`, individualizing `v` commits
**no real decision**: `v`'s 1-WL cell is **non-singleton** (some `u ≠ v` shares its colour) and is a
**single `Aut_S`-orbit** (every cell-mate is `OrbitPartition`-related to `v`). The non-singleton
conjunct is load-bearing — without it a singleton cell satisfies the orbit condition vacuously (only
`u = v`), so `∃ v, SymmetryOnlyStep` would be trivially true and the descent could spin on no-op steps;
with it, the step strictly refines the partition and forces `v ∉ S`. This is the step-condition
formerly inlined in `VisiblyRecoverable` (lines above), lifted out as the screen's D1 primitive
([harvest-window §6.10](../../../docs/chain-descent-harvest-window.md)). -/
def SymmetryOnlyStep (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  (∃ u, u ≠ v ∧ warmRefine adj P (individualizedColouring n S) u
                = warmRefine adj P (individualizedColouring n S) v)
  ∧ (∀ u, warmRefine adj P (individualizedColouring n S) u
          = warmRefine adj P (individualizedColouring n S) v
        → OrbitPartition adj P S v u)

/-- **`CellsAreOrbits` upgrades any non-singleton cell to a symmetry-only step.** When cells coincide
with orbits at `S`, a vertex `v` whose cell is non-singleton has every cell-mate in its orbit, so the
step `S → insert v S` is symmetry-only. The bridge from the recovery predicate to the screen's D1
primitive (and the route by which a `CellsAreOrbits` non-discrete node always offers a `SymmetryOnlyStep`
to recurse on — the §6.11 soundness of using `Discrete`, not bare `CellsAreOrbits`, as the stop). -/
theorem symmetryOnlyStep_of_cellsAreOrbits {S : Finset (Fin n)} {v : Fin n}
    (hco : CellsAreOrbits adj P S)
    (hns : ∃ u, u ≠ v ∧ warmRefine adj P (individualizedColouring n S) u
                       = warmRefine adj P (individualizedColouring n S) v) :
    SymmetryOnlyStep adj P S v :=
  ⟨hns, fun u hu => hco v u hu.symm⟩

/-- **Validation: the first step is symmetry-only on a schurian scheme.** A vertex-transitive scheme is
one `Aut`-orbit at `∅`, so individualizing any `v` (with `n ≥ 2`, witnessed by a second vertex `u ≠ v`)
is a `SymmetryOnlyStep`: vertex-transitivity (`cellsAreOrbits_empty_of_schurian`) gives the single-orbit
half, and `u, v` share the `∅`-cell because the transitivity automorphism `π : v ↦ u`
(`schurian_transitive` at `R₀`) preserves warm refinement (`warmRefine_invariant_of_isAut`; the empty
individualization is the constant colour, so `π`-invariant). Validates the new `SymmetryOnlyStep`
primitive on the same instance as `visiblyRecoverable_scheme`. -/
theorem symmetryOnlyStep_empty_scheme (h : IsSchurianSchemeGraph' adj)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {v u : Fin n} (huv : u ≠ v) :
    SymmetryOnlyStep adj P ∅ v := by
  refine symmetryOnlyStep_of_cellsAreOrbits
    (cellsAreOrbits_empty_of_schurian h hP_invariant) ⟨u, huv, ?_⟩
  have hrel0v : h.G.scheme.rel 0 v v = true := (h.G.scheme.rel_zero_iff_eq v v).mpr rfl
  have hrel0u : h.G.scheme.rel 0 u u = true := (h.G.scheme.rel_zero_iff_eq u u).mpr rfl
  obtain ⟨π, hπ, hπv, _⟩ := h.G.schurian_transitive 0 v v u u hrel0v hrel0u
  have hπ' : IsAut π adj := h.matching ▸ hπ
  have hχ : ∀ w, individualizedColouring n ∅ (π w) = individualizedColouring n ∅ w := by
    intro w; simp [individualizedColouring]
  have hinv := warmRefine_invariant_of_isAut hπ' (hP_invariant hπ') hχ v
  rw [hπv] at hinv
  exact hinv

/-! ### The screen `Findable` — the sequential D1/D2 screen (§6.10 + §6.11 F1 fix)

The seal's discriminator, made **sequential** (consume visible D1 symmetry, *then* classify the
residual). Realised as a least-fixed-point inductive, the faithful Lean form of the doc's recursive
`Findable S := Discrete S ∨ (ResidualAbelian S ∧ ¬IsBase S) ∨ (∃ v, SymmetryOnlyStep S v ∧ Findable (insert v S))`.

Two precision points baked in:
- **§6.11 F1** — the recovered/stop disjunct is `Discrete`, **not** bare `CellsAreOrbits`: the latter is
  *vacuously true at a vertex-transitive node* (one cell = one orbit), so it would mark a Johnson graph
  (the Cameron wall) `Findable` at `∅`. `Discrete` is the genuine stop, and is non-false-walling
  (`symmetryOnlyStep_of_cellsAreOrbits`: a `CellsAreOrbits` non-discrete node offers a step to recurse on).
- **D2 `¬IsBase` guard** — bare `ResidualAbelian` is vacuously true on a trivial residual (the
  multipede / IR-blind-spot), which would falsely assert `D2 ⟹ recoverable` on a refinement-stuck rigid
  graph; `¬IsBase` keeps it out (= "a symmetry exists").

`¬Findable` is the seal's wall, split by residual-group order: trivial ⟹ IR-blind-spot, non-trivial
non-abelian ⟹ Cameron (leg C). -/
inductive Findable (adj : AdjMatrix n) (P : PMatrix n) : Finset (Fin n) → Prop where
  /-- **Recovered.** Warm refinement at `S` is `Discrete` — fully canonized (the §6.11 F1-correct stop). -/
  | recovered {S : Finset (Fin n)} :
      Discrete (warmRefine adj P (individualizedColouring n S)) → Findable adj P S
  /-- **D2 — hidden non-trivial abelian.** The residual is abelian (`ResidualAbelian`) and non-trivial
  (`¬IsBase`): the linear oracle's unique-candidate twist. The `¬IsBase` guard excludes the IR-blind-spot. -/
  | abelian {S : Finset (Fin n)} :
      ResidualAbelian adj P S → ¬ IsBase adj P S → Findable adj P S
  /-- **D1 — consume a symmetry-only step, recurse.** A symmetry-only step at `v` is available and the
  residual after taking it is `Findable`. The non-singleton guard in `SymmetryOnlyStep` forces `v ∉ S`,
  so `S` strictly grows and the recursion is well-founded (bounded by `n`). -/
  | step {S : Finset (Fin n)} {v : Fin n} :
      SymmetryOnlyStep adj P S v → Findable adj P (insert v S) → Findable adj P S

/-! ### The bound-carrying recoverability layer (Phase 0)

`Findable` (above) is the *bound-free classification* — the right object for the screen and its negation
(the wall). `FindableWithin adj P S b` is its **bound-indexed** companion, pinning the **polynomial recovery
depth `b`** at which `CellsAreOrbits` is reached. This is the form the recoverability lemma needs:
`RecoverableByDepth adj P n` is *trivially* true for every graph (`recoverableByDepth_univ`, by individualizing
`univ`), so "`∃ b, RecoverableByDepth`" is **vacuous** and only a *specific* bound carries content — the
project convention (`recoverableByDepth_cfi` concludes at `cfi_depth_bound`, never `∃ b`). -/

/-- **`Findable` with its recovery depth.** Same three legs as `Findable`, each pinning the bound `b`:
- `recovered` at `S` (Discrete) ⟹ `CellsAreOrbits S`, so `b = S.card`;
- `step` consumes a symmetry-only individualization and **propagates the same `b`** (the recovery node is
  unchanged — `RecoverableByDepth` is a whole-graph property);
- `abelian` **carries `RecoverableByDepth adj P b` as a field** — this field *is the D2-bridge interface*:
  building the abelian leg requires supplying the hidden-abelian residual's recoverability at a specific `b`
  (discharged per instance — `recoverableByDepth_cfi` for the CFI gauge; the general discharge is the open
  `cfi_cascades`-generalisation = `AbelianSufficiencyHolds`). -/
inductive FindableWithin (adj : AdjMatrix n) (P : PMatrix n) : Finset (Fin n) → Nat → Prop where
  /-- **Recovered at depth `S.card`.** Warm refinement at `S` is `Discrete` ⟹ `CellsAreOrbits S`. -/
  | recovered {S : Finset (Fin n)} :
      Discrete (warmRefine adj P (individualizedColouring n S)) → FindableWithin adj P S S.card
  /-- **D2 leg, carrying the bridge.** A hidden non-trivial abelian residual, *together with* its
  recoverability at a specific bound `b` (the field to discharge — the D2 bridge). -/
  | abelian {S : Finset (Fin n)} {b : Nat} :
      ResidualAbelian adj P S → ¬ IsBase adj P S → RecoverableByDepth adj P b → FindableWithin adj P S b
  /-- **D1 leg.** Consume a symmetry-only step; the recovery depth `b` is inherited from the residual. -/
  | step {S : Finset (Fin n)} {v : Fin n} {b : Nat} :
      SymmetryOnlyStep adj P S v → FindableWithin adj P (insert v S) b → FindableWithin adj P S b

/-- **Soundness of the screen — NON-VACUOUS, at a specific bound.** `FindableWithin adj P S b` implies the
graph is `RecoverableByDepth adj P b` for the **carried** `b`, not a free `∃ b`. The `recovered` case is
free (`cellsAreOrbits_of_discrete`, witness `S` of card `≤ S.card`); the `step` case is the induction
hypothesis verbatim; the `abelian` case returns its carried recoverability field. So the D1 fragment (no
`abelian`) is unconditional, and the abelian leg's recoverability is exactly the supplied bridge. -/
theorem recoverableByDepth_of_findableWithin {S : Finset (Fin n)} {b : Nat}
    (h : FindableWithin adj P S b) : RecoverableByDepth adj P b := by
  induction h with
  | @recovered S hd => exact ⟨S, le_refl _, cellsAreOrbits_of_discrete hd⟩
  | @abelian S b h1 h2 hrec => exact hrec
  | step _ _ ih => exact ih

/-- **The bound-carrying descent is a `Findable` classification.** Forgetting the bound (and the abelian
leg's recoverability witness) collapses `FindableWithin` to the bound-free screen `Findable`. The reverse
fails in general — recovering the bound requires the D2 bridge — so `FindableWithin` is the strictly
stronger object, exactly because it carries it. -/
theorem findable_of_findableWithin {S : Finset (Fin n)} {b : Nat}
    (h : FindableWithin adj P S b) : Findable adj P S := by
  induction h with
  | recovered hd => exact Findable.recovered hd
  | abelian h1 h2 _ => exact Findable.abelian h1 h2
  | step hstep _ ih => exact Findable.step hstep ih

/-! ### Phase 1 — the D2-bridge anchor for the CFI gauge (axiom-clean)

The `abelian` constructor of `FindableWithin` carries a `RecoverableByDepth adj P b` **field** — the
**D2-bridge interface** ([harvest-window §6.12](../../../docs/chain-descent-harvest-window.md)): building
the abelian leg requires supplying the hidden-abelian residual's recoverability at a *specific* polynomial
bound. This section discharges that field for the **odd-degree CFI gauge** with the **axiom-free**
`recoverableByDepth_cfi` — *not* the open `AbelianSufficiencyHolds` axiom. It is the D2 analogue of the
D1 anchor `visiblyRecoverable_scheme`: a real, central example showing the abelian leg is populated by
proved recoverability, not a placeholder.

**Two index-grounded facts make this the right wiring** (§6.12):
- The CFI recovery is **discretizing**, prototyped by `recoverableByDepth_cfi` (individualize the gauge's
  base, `warmRefine` there is `Discrete`) — *not* the structural connector `cascadeComposition_pathFixing`,
  which needs `CellsAreOrbits` at layer 1, false for a *hidden* (cell-coarser-than-orbit) D2 residual.
- `recoverableByDepth_cfi` is **axiom-free for `OddDegree`** and carries **no `P`-invariance hypothesis**,
  so the recovery field is free at `cfi_depth_bound h` for *every* committed set `S` (whole-graph property).

**What stays a hypothesis (honest scope).** `ResidualAbelian adj P S` and `¬ IsBase adj P S` are the
screen's **D2 predicate** — *consumed, never decided* (deciding it is GI-hard; the seal flags on
budget-exceed, [harvest-window §3](../../../docs/chain-descent-harvest-window.md)). Discharging
`ResidualAbelian` *unconditionally* for a real CFI residual would need the `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)`
**surjectivity** (a `Z₂^β` upper bound on the residual) — deliberately **not** built (`CFI.lean §15` builds
only generator *existence*). The asymmetry with the D1 anchor is intrinsic: D1's positive content
(cells = orbits) is *refinement-visible* hence provable (`visiblyRecoverable_scheme`); D2's (residual is
abelian) is *hidden* hence needs unbuilt group structure. -/

/-- **D2-bridge anchor — CFI gauge.** For an odd-degree CFI graph, whenever the residual at a committed
set `S` is the hidden non-trivial abelian gauge (`ResidualAbelian adj P S ∧ ¬ IsBase adj P S`, the screen's
D2 predicate), the `FindableWithin.abelian` recoverability field is discharged by the **axiom-free**
`recoverableByDepth_cfi` at depth `cfi_depth_bound h` (`≤ baseSize ≤ n/6`). The D2 analogue of
`visiblyRecoverable_scheme`: the abelian leg's recoverability obligation is met by proved math on the
central CFI example, isolating the only open content to the (consumed, not decided) D2 *predicate*. -/
theorem findableWithin_cfi_gauge (P : PMatrix n) {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) {S : Finset (Fin n)}
    (habelian : ResidualAbelian adj P S) (hnonbase : ¬ IsBase adj P S) :
    FindableWithin adj P S (cfi_depth_bound h) :=
  FindableWithin.abelian habelian hnonbase (recoverableByDepth_cfi h h_odd P)

/-- **Recoverability of the CFI gauge, via the anchored D2 leg.** The bound-carrying soundness applied to
`findableWithin_cfi_gauge`: a hidden non-trivial abelian CFI residual is `RecoverableByDepth` at
`cfi_depth_bound h`. (Unfolds to `recoverableByDepth_cfi` — but routed *through* the screen, certifying the
D2 leg is non-vacuous end-to-end.) -/
theorem recoverableByDepth_of_cfi_gauge (P : PMatrix n) {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) {S : Finset (Fin n)}
    (habelian : ResidualAbelian adj P S) (hnonbase : ¬ IsBase adj P S) :
    RecoverableByDepth adj P (cfi_depth_bound h) :=
  recoverableByDepth_of_findableWithin (findableWithin_cfi_gauge P h h_odd habelian hnonbase)

/-- **The CFI gauge is `Findable`** (bound-free classification): forgetting the bound, a hidden non-trivial
abelian CFI residual lands in the screen's D2 leg. The screen's abelian disjunct is populated by the
central recoverable, non-Cameron example — the §6.9 escape (`CFI(Kₘ)` slips the *flat* screen) closed at
the predicate level by the sequential screen's `abelian` constructor. -/
theorem findable_cfi_gauge (P : PMatrix n) {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) {S : Finset (Fin n)}
    (habelian : ResidualAbelian adj P S) (hnonbase : ¬ IsBase adj P S) :
    Findable adj P S :=
  findable_of_findableWithin (findableWithin_cfi_gauge P h h_odd habelian hnonbase)

/-! ## Leg A — bounded termination of the symmetry-only process (engine transplant)

The first Leg-A deliverable, transplanting the `ChainDescent.Saturation` engine that closed
the scheme rank ladder (`Scheme.lean §10.12/§10.13`). The symmetry-only (D1) individualization
process is an **extensive closure** on the committed set: each `SymmetryOnlyStep` strictly grows
`S` (its non-singleton guard forces `v ∉ S` — `symmetryOnlyStep_not_mem`), so by
`exists_iterate_isFixed` it **saturates within `≤ n − |S₀|` rounds** at a node where no
symmetry-only step remains. This is the class-agnostic, engine-powered half of
[harvest-window](../../../docs/chain-descent-harvest-window.md) gap 3 (bounded termination of
the D1 chain). The forced-node iso-invariance (the spine) and "a *visible* symmetry keeps a step
available until `Discrete`" (the (c)-trichotomy) remain the open research core.

This is the Leg-A/D1 mirror of the scheme `isolationStep`/`EdgeGenerates` saturation — *same
engine, carrier = vertices instead of relations, bound `B = univ` (the support refinement is the
next step).* `EdgeGenerates`/`PPolynomial` were graded **D1** witnesses; here the saturated node
is the operational endpoint of the same D1 closure. -/

open Classical in
/-- One round of the **symmetry-only closure**: individualize a symmetry-only vertex if one
exists, else stay put. Extensive; strictly grows until no symmetry-only step remains. -/
noncomputable def soStep (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  if h : ∃ v, SymmetryOnlyStep adj P S v then insert h.choose S else S

/-- The closure round is **extensive** — it only ever adds the chosen vertex. -/
theorem soStep_extensive (S : Finset (Fin n)) : S ⊆ soStep adj P S := by
  unfold soStep; split_ifs with h
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- **A symmetry-only step's vertex is not yet committed** (`v ∉ S`). Its cell is
non-singleton, but a committed vertex is an initial `individualizedColouring` singleton that
warm refinement preserves (`warmRefine_refines` + `individualizedColouring_eq_iff_of_mem`) — so
no other vertex could share its colour. This is what makes `soStep` strictly grow until stuck. -/
theorem symmetryOnlyStep_not_mem {S : Finset (Fin n)} {v : Fin n}
    (h : SymmetryOnlyStep adj P S v) : v ∉ S := by
  intro hvS
  obtain ⟨u, huv, hcol⟩ := h.1
  exact huv ((individualizedColouring_eq_iff_of_mem S hvS).mp
    (warmRefine_refines adj P (individualizedColouring n S) hcol))

/-- When a symmetry-only step exists, the closure round takes it. -/
theorem soStep_pos {S : Finset (Fin n)} (hex : ∃ v, SymmetryOnlyStep adj P S v) :
    soStep adj P S = insert hex.choose S := by
  unfold soStep; rw [dif_pos hex]

/-- **Leg A — bounded termination of the symmetry-only process.** From any committed `S₀`,
iterating the symmetry-only closure reaches a **saturated** node `S* ⊇ S₀` — one with *no*
symmetry-only step available — within `≤ n − |S₀|` rounds. The engine-powered, class-agnostic
half of the harvest-window trichotomy's termination: the D1 chain cannot run forever. At `S*`
the symmetry is either fully recovered (`Discrete`) or genuinely hidden (→ D2 / the wall). -/
theorem exists_symmetryOnly_saturated (adj : AdjMatrix n) (P : PMatrix n)
    (S₀ : Finset (Fin n)) :
    ∃ k, k ≤ Fintype.card (Fin n) - S₀.card ∧
      S₀ ⊆ (soStep adj P)^[k] S₀ ∧
      ¬ ∃ v, SymmetryOnlyStep adj P ((soStep adj P)^[k] S₀) v := by
  obtain ⟨k, hk, hfix⟩ :=
    Saturation.exists_iterate_isFixed (soStep adj P) (soStep_extensive) S₀
  refine ⟨k, hk, ?_, ?_⟩
  · have hm := Saturation.iterate_mono (soStep adj P) (soStep_extensive) S₀ (Nat.zero_le k)
    rwa [Function.iterate_zero_apply] at hm
  · intro hex
    rw [soStep_pos hex] at hfix
    exact symmetryOnlyStep_not_mem hex.choose_spec (Finset.insert_eq_self.mp hfix)

/-! ## Leg A — the general support induction (reaching a base)

`exists_symmetryOnly_saturated` saturates the *D1 (symmetry-only)* chain, but a symmetry-only
step is unavailable in the hidden/CFI case (the cell is coarser than the orbit — `¬D1`). The
*general* support induction tracks **moved** vertices instead (weaker than symmetry-only) and
**provably reaches a base**: it is the class-agnostic formalization of harvest-window §2's
termination — "case (c) strictly shrinks the residual's support, bottoming out at
`base(g) ≤ |support|`" — for *every* graph, via the same `Saturation` engine. -/

/-- **A vertex moved by some residual automorphism at `S`.** Weaker than a `SymmetryOnlyStep`
(a moved vertex's cell may be *coarser* than its orbit — the hidden/CFI case), so this is the
right object for the *general* support induction. `MovedAt ⟹ v ∉ S` is immediate (a residual
auto fixes `S` pointwise). -/
def MovedAt (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  ∃ π, ResidualAut adj P S π ∧ π v ≠ v

theorem movedAt_not_mem {S : Finset (Fin n)} {v : Fin n} (h : MovedAt adj P S v) : v ∉ S := by
  obtain ⟨π, hπ, hπv⟩ := h
  exact fun hvS => hπv (hπ.2.2 v hvS)

/-- A node with **no moved vertex is a base** (trivial residual): an `OrbitPartition` pair
`v ↦ w` with `v ≠ w` would be a residual automorphism moving `v`. -/
theorem isBase_of_no_moved {S : Finset (Fin n)} (h : ¬ ∃ v, MovedAt adj P S v) :
    IsBase adj P S := by
  intro v w hvw
  by_contra hne
  rw [orbitPartition_iff_residualAut] at hvw
  obtain ⟨π, hπ, hπv⟩ := hvw
  exact h ⟨v, π, hπ, fun hpvv => hne (by rw [← hπv, hpvv])⟩

open Classical in
/-- One round of the **moved-vertex closure**: individualize a moved vertex if one exists, else
stay. Extensive; strictly grows until the residual is trivial (a base). -/
noncomputable def movedStep (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  if h : ∃ v, MovedAt adj P S v then insert h.choose S else S

theorem movedStep_extensive (S : Finset (Fin n)) : S ⊆ movedStep adj P S := by
  unfold movedStep; split_ifs with h
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem movedStep_pos {S : Finset (Fin n)} (hex : ∃ v, MovedAt adj P S v) :
    movedStep adj P S = insert hex.choose S := by
  unfold movedStep; rw [dif_pos hex]

/-- **Leg A — the general support induction (every graph reaches a base).** From any `S₀`,
individualizing moved vertices reaches a **base** `S* ⊇ S₀` (trivial residual,
`base(g) ≤ |support|`) within `≤ n − |S₀|` rounds. The class-agnostic termination of the
harvest-window trichotomy, via the `Saturation` engine — holding for *every* graph (CFI,
schemes, rigid alike). Recovery at the base additionally needs `Discrete` there
(`CellsAreOrbits`-at-base ⟺ `Discrete`), the orthogonal IR-stickiness axis. -/
theorem exists_isBase_saturated (adj : AdjMatrix n) (P : PMatrix n) (S₀ : Finset (Fin n)) :
    ∃ k, k ≤ Fintype.card (Fin n) - S₀.card ∧
      S₀ ⊆ (movedStep adj P)^[k] S₀ ∧ IsBase adj P ((movedStep adj P)^[k] S₀) := by
  obtain ⟨k, hk, hfix⟩ :=
    Saturation.exists_iterate_isFixed (movedStep adj P) movedStep_extensive S₀
  refine ⟨k, hk, ?_, ?_⟩
  · have hm := Saturation.iterate_mono (movedStep adj P) movedStep_extensive S₀ (Nat.zero_le k)
    rwa [Function.iterate_zero_apply] at hm
  · apply isBase_of_no_moved
    intro hex
    rw [movedStep_pos hex] at hfix
    exact movedAt_not_mem hex.choose_spec (Finset.insert_eq_self.mp hfix)

/-! ## Leg A — the tight support bound (`base(g) ≤ |support|`)

`exists_isBase_saturated` reaches a base within `≤ n − |S₀|` rounds (enough for *polynomial*,
but vacuous as the harvest-window depth claim). The sharp bound is the **support of the
residual group at `S₀`** — the vertices moved by *some* residual automorphism. The
ingredient that turns the `n` bound into `|support|` is that the moved-set only *shrinks* as
`S₀` grows (`MovedAt.anti`), so it is an interval-invariant saturation bound for `movedStep`;
the engine's `exists_iterate_isFixed_within'` then closes within `|support|` rounds. The gap
between `|support|` and the cruder `n − |S₀|` envelope is exactly the orthogonal IR-stickiness
axis (harvest-window §2.3), not the symmetry axis. -/

/-- **Moved-set anti-monotonicity.** A residual automorphism fixing `S` pointwise also fixes
every `S₀ ⊆ S`, so it is a residual automorphism at `S₀`. Hence a vertex moved by the residual
at `S` is already moved by the residual at `S₀`: the moved-set *shrinks* as the individualized
set grows — what makes it a saturation bound. -/
theorem MovedAt.anti {S₀ S : Finset (Fin n)} (hsub : S₀ ⊆ S) {v : Fin n}
    (h : MovedAt adj P S v) : MovedAt adj P S₀ v := by
  obtain ⟨π, ⟨hAut, hP, hFix⟩, hv⟩ := h
  exact ⟨π, ⟨hAut, hP, fun x hx => hFix x (hsub hx)⟩, hv⟩

open Classical in
/-- **The residual support at `S₀`:** the vertices moved by *some* residual automorphism
fixing `S₀` — the support of the residual group `Aut_{S₀}^P`. Disjoint from `S₀`
(`movedAt_not_mem`); its cardinality is `|support(g)|`, the harvest-window depth. -/
noncomputable def movedSet (adj : AdjMatrix n) (P : PMatrix n) (S₀ : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun v => MovedAt adj P S₀ v)

theorem mem_movedSet {S₀ : Finset (Fin n)} {v : Fin n} :
    v ∈ movedSet adj P S₀ ↔ MovedAt adj P S₀ v := by
  simp [movedSet]

/-- **Interval invariance of the support bound.** On every `f`-reachable set `S₀ ⊆ s ⊆
S₀ ∪ movedSet`, `movedStep` stays inside the bound: the vertex it individualizes is moved at
`s`, hence (anti-monotonicity) moved at `S₀`, hence in `movedSet`. Full invariance would
fail — a vertex moved at `s ⊉ S₀` need not be moved at `S₀` — which is why the saturation
engine's interval-invariant form is needed. -/
theorem movedStep_subset_bound {S₀ s : Finset (Fin n)}
    (hS₀s : S₀ ⊆ s) (hsB : s ⊆ S₀ ∪ movedSet adj P S₀) :
    movedStep adj P s ⊆ S₀ ∪ movedSet adj P S₀ := by
  unfold movedStep
  split_ifs with hex
  · rw [Finset.insert_subset_iff]
    refine ⟨?_, hsB⟩
    exact Finset.mem_union_right _ (mem_movedSet.mpr ((hex.choose_spec).anti hS₀s))
  · exact hsB

/-- **Leg A — the tight support bound (`base(g) ≤ |support|`).** Sharpens
`exists_isBase_saturated`: from any `S₀`, the moved-vertex closure reaches a **base** within
`≤ |movedSet adj P S₀|` rounds — the **support of the residual group at `S₀`**, not the full
`n`. This is the harvest-window depth claim (§2.3) made precise; the gap to the `n − |S₀|`
envelope is the orthogonal IR-stickiness axis. Via the interval-invariant saturation engine,
since `movedStep` preserves the support bound only on supersets of `S₀`. -/
theorem exists_isBase_saturated_support (adj : AdjMatrix n) (P : PMatrix n)
    (S₀ : Finset (Fin n)) :
    ∃ k, k ≤ (movedSet adj P S₀).card ∧
      S₀ ⊆ (movedStep adj P)^[k] S₀ ∧ IsBase adj P ((movedStep adj P)^[k] S₀) := by
  obtain ⟨k, hk, hfix⟩ :=
    Saturation.exists_iterate_isFixed_within' (movedStep adj P) movedStep_extensive
      (S₀ ∪ movedSet adj P S₀) S₀ Finset.subset_union_left
      (fun s hS₀s hsB => movedStep_subset_bound hS₀s hsB)
  refine ⟨k, ?_, ?_, ?_⟩
  · have hle : (S₀ ∪ movedSet adj P S₀).card ≤ S₀.card + (movedSet adj P S₀).card :=
      Finset.card_union_le _ _
    omega
  · have hm := Saturation.iterate_mono (movedStep adj P) movedStep_extensive S₀ (Nat.zero_le k)
    rwa [Function.iterate_zero_apply] at hm
  · apply isBase_of_no_moved
    intro hex
    rw [movedStep_pos hex] at hfix
    exact movedAt_not_mem hex.choose_spec (Finset.insert_eq_self.mp hfix)

/-! ## Leg A — forced-node iso-invariance (the choice-free canonical base)

`exists_isBase_saturated`/`movedStep` reach a base via `Classical.choice` (`h.choose` picks
*some* moved vertex), so the node they land on is not canonical. The fix is to bypass the
choice entirely: individualizing the **whole residual support** `movedSet adj P S₀` at once
already yields a base (fixing every moved point trivializes the residual group), and this
node — `forcedNode adj P S₀` — is a *deterministic* function of `(adj, P, S₀)`,
**automorphism-equivariant** (`forcedNode_image`), hence iso-invariant: it commutes with the
graph's symmetries rather than depending on an arbitrary choice.

Note this does **not** go through the spine (`SpineChain.eq_default`): the spine reaches
discreteness of the *index-based* `defaultColouring`, which is not automorphism-invariant, so
it cannot constrain the semantic residual group except at `D = univ`. The semantic
`movedSet` is directly equivariant, which is cleaner. Refinement-*computing* `forcedNode` at a
node (rather than defining it) is the open recovery content (declassing §5 item 3). The
arbitrary-relabelling form (any `σ`, not just `σ ∈ Aut`) is the same conjugation over an
`(adj, P)`-relabel action. -/

/-- **The canonical forced node:** individualize `S₀` together with the *entire* residual
support `movedSet adj P S₀`. Choice-free — the deterministic, iso-invariant counterpart of the
`Classical.choice`-driven `movedStep` saturation. -/
noncomputable def forcedNode (adj : AdjMatrix n) (P : PMatrix n) (S₀ : Finset (Fin n)) :
    Finset (Fin n) :=
  S₀ ∪ movedSet adj P S₀

/-- **The forced node is a base — choice-free.** Individualizing the full residual support
trivializes the residual group: a residual automorphism at `forcedNode` moving some `v` would,
by `MovedAt.anti`, move `v` already at `S₀`, putting `v ∈ movedSet ⊆ forcedNode`; but residual
automorphisms fix `forcedNode` pointwise. The deterministic counterpart of
`exists_isBase_saturated` (no `Classical.choice`). -/
theorem forcedNode_isBase (S₀ : Finset (Fin n)) : IsBase adj P (forcedNode adj P S₀) := by
  apply isBase_of_no_moved
  rintro ⟨v, hv⟩
  have hvnotin : v ∉ forcedNode adj P S₀ := movedAt_not_mem hv
  have hv0 : MovedAt adj P S₀ v := hv.anti Finset.subset_union_left
  exact hvnotin (Finset.mem_union_right _ (mem_movedSet.mpr hv0))

/-- **Automorphism-equivariance of `MovedAt` (one direction).** A graph automorphism `g`
preserving `P` carries a moved vertex at `S₀` to a moved vertex at the relabelled set
`S₀.image g`, via the conjugate residual automorphism `g π g⁻¹`. -/
theorem movedAt_image {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (hgP : ∀ x u, P (g x) (g u) = P x u) {S₀ : Finset (Fin n)} {v : Fin n}
    (h : MovedAt adj P S₀ v) : MovedAt adj P (S₀.image g) (g v) := by
  obtain ⟨π, ⟨hAut, hP, hFix⟩, hπv⟩ := h
  refine ⟨(g.symm.trans π).trans g,
    ⟨IsAut.trans (IsAut.trans (IsAut.symm hg) hAut) hg, ?_, ?_⟩, ?_⟩
  · -- `P`-preservation of `g π g⁻¹`
    intro x u
    show P (g (π (g.symm x))) (g (π (g.symm u))) = P x u
    rw [hgP (π (g.symm x)) (π (g.symm u)), hP (g.symm x) (g.symm u)]
    have h2 := hgP (g.symm x) (g.symm u)
    simp only [Equiv.apply_symm_apply] at h2
    exact h2.symm
  · -- fixes `S₀.image g` pointwise
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    show g (π (g.symm (g s₀))) = g s₀
    rw [Equiv.symm_apply_apply, hFix s₀ hs₀]
  · -- moves `g v`
    show g (π (g.symm (g v))) ≠ g v
    rw [Equiv.symm_apply_apply]
    exact fun heq => hπv (g.injective heq)

/-- **Automorphism-equivariance of `MovedAt`.** The iff form of `movedAt_image`; the reverse
direction is `movedAt_image` applied at `g⁻¹`. -/
theorem movedAt_image_iff {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (hgP : ∀ x u, P (g x) (g u) = P x u) {S₀ : Finset (Fin n)} (v : Fin n) :
    MovedAt adj P (S₀.image g) (g v) ↔ MovedAt adj P S₀ v := by
  refine ⟨fun h => ?_, movedAt_image hg hgP⟩
  have hgP' : ∀ x u, P (g.symm x) (g.symm u) = P x u := by
    intro x u
    have := hgP (g.symm x) (g.symm u)
    simpa only [Equiv.apply_symm_apply] using this.symm
  have key := movedAt_image (IsAut.symm hg) hgP' (S₀ := S₀.image g) (v := g v) h
  simpa only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id,
    Equiv.symm_apply_apply] using key

/-- **The residual support commutes with automorphisms.** A `P`-preserving graph automorphism
`g` carries the support at `S₀` to the support at the relabelled set `S₀.image g`. -/
theorem movedSet_image {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (hgP : ∀ x u, P (g x) (g u) = P x u) (S₀ : Finset (Fin n)) :
    movedSet adj P (S₀.image g) = (movedSet adj P S₀).image g := by
  ext w
  rw [mem_movedSet, Finset.mem_image]
  constructor
  · intro hw
    refine ⟨g.symm w, ?_, by rw [Equiv.apply_symm_apply]⟩
    rw [mem_movedSet]
    have key : MovedAt adj P (S₀.image g) (g (g.symm w)) ↔ MovedAt adj P S₀ (g.symm w) :=
      movedAt_image_iff hg hgP (g.symm w)
    rw [Equiv.apply_symm_apply] at key
    exact key.mp hw
  · rintro ⟨v, hv, rfl⟩
    exact (movedAt_image_iff hg hgP v).mpr (mem_movedSet.mp hv)

/-- **The forced node is automorphism-equivariant (iso-invariance).** `forcedNode` commutes
with every `P`-preserving graph automorphism: it is a canonical function of iso-invariant
data, not an arbitrary `Classical.choice`. -/
theorem forcedNode_image {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (hgP : ∀ x u, P (g x) (g u) = P x u) (S₀ : Finset (Fin n)) :
    forcedNode adj P (S₀.image g) = (forcedNode adj P S₀).image g := by
  unfold forcedNode
  rw [Finset.image_union, movedSet_image hg hgP]

/-- **The forced node is fixed by the residual group it resolves.** Every residual
automorphism at `S₀` maps `forcedNode adj P S₀` to itself setwise — the canonical node is
invariant under exactly the symmetry it is meant to consume. -/
theorem forcedNode_residual_invariant (S₀ : Finset (Fin n)) {g : Equiv.Perm (Fin n)}
    (hg : ResidualAut adj P S₀ g) :
    (forcedNode adj P S₀).image g = forcedNode adj P S₀ := by
  obtain ⟨hAut, hP, hFix⟩ := hg
  have hS₀ : S₀.image g = S₀ := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; rwa [hFix y hy]
    · intro hx; exact ⟨x, hx, hFix x hx⟩
  rw [← forcedNode_image hAut hP S₀, hS₀]

/-! ## Leg A — tying the two axes: recovery at the base ⟺ no IR-stickiness

The harvest-window §2.3 thesis is that orbit recovery has **two orthogonal obstructions**:
the *symmetry axis* (consume the hidden symmetry — reach a base) and the *IR-stickiness axis*
(refinement must actually singletonize — `Discrete`). The symmetry axis is closed
(`forcedNode_isBase`). At a base these two collapse into a single equivalence: since a base
already has discrete *orbits* and "orbits refine cells" is free (`subset_warmRefine`),
**recovery holds iff refinement is discrete there**. So the *only* remaining obstruction is
stickiness — the multipede / IR-blind-spot (strategy §15 gap 5), correctly *flagged*, not
solved. This separates the axes formally and pins the flag to exactly `¬ Discrete` at the
canonical node. -/

/-- **Recovery at a base ⟺ discreteness there.** Once the residual symmetry is consumed (`S`
is a base), orbit recovery reduces *exactly* to the IR-stickiness axis: `OrbitRecoverableAt`
holds iff `warmRefine` is `Discrete`. The `⟸` direction (`cellsAreOrbits_of_discrete`) needs
no base; the base is what upgrades it to an iff (same cell ⟹ orbit ⟹ equal). -/
theorem recoverableAt_base_iff_discrete (S : Finset (Fin n)) (hbase : IsBase adj P S) :
    OrbitRecoverableAt adj P S ↔
      Discrete (warmRefine adj P (individualizedColouring n S)) := by
  constructor
  · intro hrec i j hcell
    exact hbase i j ((hrec i j).mpr hcell)
  · intro hd
    exact orbitRecoverableAt_iff_cellsAreOrbits.mpr (cellsAreOrbits_of_discrete hd)

/-- **Tying the axes at the canonical forced node.** At `forcedNode adj P S₀` (a base by
`forcedNode_isBase`), orbit recovery is *exactly* discreteness of `warmRefine`. Symmetry
consumed (the forced node is a base) **and** no IR-stickiness (`Discrete`) ⟺ recovery — the
two obstructions of harvest-window §2.3 separated, with the second the sole remaining (flagged)
input. -/
theorem forcedNode_recoverable_iff_discrete (S₀ : Finset (Fin n)) :
    OrbitRecoverableAt adj P (forcedNode adj P S₀) ↔
      Discrete (warmRefine adj P
        (individualizedColouring n (forcedNode adj P S₀))) :=
  recoverableAt_base_iff_discrete (forcedNode adj P S₀) (forcedNode_isBase S₀)

/-! ## Leg A — computability of the support at recoverable nodes

`movedSet` (hence `forcedNode`) is defined semantically (via the residual group), GI-hard to
compute in general. But at a node where recovery *does* hold, the residual group is visible to
1-WL: `v` is moved iff it sits in a **non-singleton cell**. So where it matters, `forcedNode`
is refinement-computable — the bridge turning the canonical node into an actual algorithm input. -/

/-- **The support is the non-singleton cells, at a recoverable node.** When
`OrbitRecoverableAt adj P S`, a vertex `v` is moved by the residual at `S` iff it shares its
1-WL cell with some other vertex. Refinement therefore computes `movedSet` (and `forcedNode`)
exactly where orbit recovery holds. -/
theorem mem_movedSet_iff_nonsingleton_cell_of_recoverable (S : Finset (Fin n))
    (hrec : OrbitRecoverableAt adj P S) {v : Fin n} :
    v ∈ movedSet adj P S ↔ ∃ w, w ≠ v ∧
      warmRefine adj P (individualizedColouring n S) v =
        warmRefine adj P (individualizedColouring n S) w := by
  rw [mem_movedSet]
  constructor
  · rintro ⟨π, hres, hπv⟩
    exact ⟨π v, hπv, (hrec v (π v)).mp ⟨π, hres.1, hres.2.1, hres.2.2, rfl⟩⟩
  · rintro ⟨w, hwv, hcell⟩
    obtain ⟨π, hAut, hP, hFix, hπvw⟩ := (hrec v w).mpr hcell
    exact ⟨π, ⟨hAut, hP, hFix⟩, by rw [hπvw]; exact hwv⟩

open Classical in
/-- **`movedSet` is refinement-computed at a recoverable node** (Finset form): it equals the
union of the non-singleton 1-WL cells. The literal statement that `forcedNode` is computable
where recovery holds. -/
theorem movedSet_eq_nonsingletonCells_of_recoverable (S : Finset (Fin n))
    (hrec : OrbitRecoverableAt adj P S) :
    movedSet adj P S = Finset.univ.filter (fun v => ∃ w, w ≠ v ∧
      warmRefine adj P (individualizedColouring n S) v =
        warmRefine adj P (individualizedColouring n S) w) := by
  ext v
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact mem_movedSet_iff_nonsingleton_cell_of_recoverable S hrec

/-! ## Leg A — arbitrary-relabelling equivariance of the forced node (full iso-invariance)

§2 proved the forced node commutes with graph *automorphisms* (`forcedNode_image`, `g ∈ Aut`).
The canonization-sense iso-invariance is stronger: relabelling the *input* by **any** `σ` maps
the forced node correspondingly. A relabelling `σ` carries `(adj, P)` to `(relabelAdj σ adj,
relabelP σ P)` — `σ` is a graph isomorphism — and the conjugate `σ π σ⁻¹` carries residual
automorphisms across it. So `forcedNode (relabel… σ) (S₀.image σ) = (forcedNode adj P S₀).image
σ`: the canonical construction commutes with relabelling, which is exactly iso-invariance. -/

/-- **Relabel a graph by `σ`:** the adjacency where `σ v` plays the role `v` did. -/
def relabelAdj (σ : Equiv.Perm (Fin n)) (A : AdjMatrix n) : AdjMatrix n :=
  ⟨fun i j => A.adj (σ.symm i) (σ.symm j)⟩

@[simp] theorem relabelAdj_adj (σ : Equiv.Perm (Fin n)) (A : AdjMatrix n) (i j : Fin n) :
    (relabelAdj σ A).adj i j = A.adj (σ.symm i) (σ.symm j) := rfl

/-- **Relabel a `P`-matrix by `σ`.** -/
def relabelP (σ : Equiv.Perm (Fin n)) (Q : PMatrix n) : PMatrix n :=
  fun i j => Q (σ.symm i) (σ.symm j)

@[simp] theorem relabelP_apply (σ : Equiv.Perm (Fin n)) (Q : PMatrix n) (i j : Fin n) :
    relabelP σ Q i j = Q (σ.symm i) (σ.symm j) := rfl

/-- **Residual automorphisms transport along a relabelling** (forward), via the conjugate
`σ π σ⁻¹`. -/
theorem residualAut_relabel (σ : Equiv.Perm (Fin n)) {S : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hres : ResidualAut adj P S π) :
    ResidualAut (relabelAdj σ adj) (relabelP σ P) (S.image σ) ((σ.symm.trans π).trans σ) := by
  obtain ⟨hAut, hP, hFix⟩ := hres
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simp only [relabelAdj_adj, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact hAut (σ.symm a) (σ.symm b)
  · intro x u
    simp only [relabelP_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact hP (σ.symm x) (σ.symm u)
  · intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hFix s₀ hs₀]

/-- **Residual automorphisms transport back from a relabelling** (reverse), via `σ⁻¹ π σ`. -/
theorem residualAut_relabel_symm (σ : Equiv.Perm (Fin n)) {S : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)}
    (hres : ResidualAut (relabelAdj σ adj) (relabelP σ P) (S.image σ) π) :
    ResidualAut adj P S ((σ.trans π).trans σ.symm) := by
  obtain ⟨hAut, hP, hFix⟩ := hres
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := hAut (σ a) (σ b)
    simp only [relabelAdj_adj, Equiv.symm_apply_apply] at h
    simpa only [Equiv.trans_apply] using h
  · intro x u
    have h := hP (σ x) (σ u)
    simp only [relabelP_apply, Equiv.symm_apply_apply] at h
    simpa only [Equiv.trans_apply] using h
  · intro s hs
    simp only [Equiv.trans_apply]
    rw [hFix (σ s) (Finset.mem_image_of_mem σ hs), Equiv.symm_apply_apply]

/-- **`MovedAt` is equivariant under relabelling.** A vertex `v` is moved at `S₀` iff its
relabelled image `σ v` is moved at `S₀.image σ` in the relabelled graph. -/
theorem movedAt_relabel_iff (σ : Equiv.Perm (Fin n)) {S₀ : Finset (Fin n)} (v : Fin n) :
    MovedAt (relabelAdj σ adj) (relabelP σ P) (S₀.image σ) (σ v) ↔ MovedAt adj P S₀ v := by
  constructor
  · rintro ⟨π, hres, hπv⟩
    refine ⟨(σ.trans π).trans σ.symm, residualAut_relabel_symm σ hres, ?_⟩
    simp only [Equiv.trans_apply]
    intro h
    apply hπv
    have hc := congrArg σ h
    simpa only [Equiv.apply_symm_apply] using hc
  · rintro ⟨π, hres, hπv⟩
    refine ⟨(σ.symm.trans π).trans σ, residualAut_relabel σ hres, ?_⟩
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    exact fun h => hπv (σ.injective h)

/-- **The residual support is equivariant under relabelling.** -/
theorem movedSet_relabel (σ : Equiv.Perm (Fin n)) (S₀ : Finset (Fin n)) :
    movedSet (relabelAdj σ adj) (relabelP σ P) (S₀.image σ)
      = (movedSet adj P S₀).image σ := by
  ext w
  rw [mem_movedSet, Finset.mem_image]
  constructor
  · intro hw
    refine ⟨σ.symm w, ?_, by rw [Equiv.apply_symm_apply]⟩
    rw [mem_movedSet]
    have key : MovedAt (relabelAdj σ adj) (relabelP σ P) (S₀.image σ) (σ (σ.symm w))
        ↔ MovedAt adj P S₀ (σ.symm w) := movedAt_relabel_iff σ (σ.symm w)
    rw [Equiv.apply_symm_apply] at key
    exact key.mp hw
  · rintro ⟨v, hv, rfl⟩
    exact (movedAt_relabel_iff σ v).mpr (mem_movedSet.mp hv)

/-- **The forced node is equivariant under arbitrary relabelling — full iso-invariance.**
Relabelling the input by *any* `σ` (not just an automorphism) maps the canonical forced node
correspondingly. The construction commutes with relabelling, which is exactly what it means for
the forced node to be a function of iso-invariant data. -/
theorem forcedNode_relabel (σ : Equiv.Perm (Fin n)) (S₀ : Finset (Fin n)) :
    forcedNode (relabelAdj σ adj) (relabelP σ P) (S₀.image σ)
      = (forcedNode adj P S₀).image σ := by
  unfold forcedNode
  rw [Finset.image_union, movedSet_relabel]

/-! ## Leg A / D1 — the whole metric/DRG family (de-classing `visiblyRecoverable_scheme`)

The scheme de-classing (`Scheme.lean §10.13`, `theorem_2_HOR_of_pPolynomial`) recovers orbits
at **depth 1** for the *entire* metric family — schemes are algebraic, so 1-WL captures them
after one individualization regardless of diameter. That makes the one-step chain `∅ → {v}`
visibly recoverable for every P-polynomial scheme, generalizing the rank-2 `visiblyRecoverable_scheme`
to all of Johnson/Hamming/cycles/DRGs: Leg-A's D1 is now class-general on the metric class. -/

/-- **D1 for every P-polynomial (metric / DRG) scheme graph.** Generalizes
`visiblyRecoverable_scheme` (rank-2 / `|J|=1`) to the whole distance-regular family via the
depth-1 metric recovery `theorem_2_HOR_of_pPolynomial`. -/
theorem visiblyRecoverable_pPolynomial (h : IsSchurianSchemeGraph' adj) (v : Fin n)
    (j0 : Fin (h.G.scheme.rank + 1)) (hJ : h.G.toSchemeGraph.J = {j0})
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (hpp : PPolynomial h.G v j0) :
    VisiblyRecoverable adj P ∅ 1 := by
  have hrec : OrbitRecoverableAt adj P {v} :=
    theorem_2_HOR_of_pPolynomial h P v j0 hJ hP_invariant hpp
  exact visiblyRecoverable_of_cellsAreOrbits_singleton
    (cellsAreOrbits_empty_of_schurian h hP_invariant)
    (orbitRecoverableAt_iff_cellsAreOrbits.mp hrec)

/-! ## M-D instance — the canonical exploration rule discharges the lockstep

The multi-step oracle `matchOracleSet` (`CascadeOracle.lean §C.6`) reduces completeness to
`LockstepExpand` — the *equivariance* of the exploration-set selector. This is **discharged** (not
assumed) for the canonical iso-invariant rule: individualize the rep together with its residual support
(`forcedExpand`), whose equivariance is exactly Leg A's `movedSet_image`. So the multi-step oracle's
only remaining hypothesis is the set-footprint depth witness ("B's core") — the lockstep is a theorem. -/

/-- **The canonical exploration rule.** For rep `r` at a node, explore `r` together with the residual
support after committing it: `insert r (movedSet adj chain.P (insert r chain.D))`. Iso-invariant and
automorphism-equivariant (the forced-node idea, per rep). -/
noncomputable def forcedExpand (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n) :
    Finset (Fin n) :=
  insert r (movedSet adj chain.P (insert r chain.D))

/-- **The lockstep is a theorem (M-D).** `forcedExpand` satisfies `LockstepExpand`: a `P`-preserving
automorphism `g` fixing the committed path carries one branch's exploration set onto the other's. The
residual-support half is exactly `movedSet_image`; the committed prefix is fixed setwise by `g`. So the
multi-step oracle `matchOracleSet (forcedExpand …)` needs no lockstep hypothesis — only the depth
witness. -/
theorem lockstepExpand_forcedExpand (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) :
    LockstepExpand (forcedExpand adj P₀ χι₀ sel) := by
  intro k chain g v hg hgP hgD
  have hDfix : chain.D.image (g : Fin n → Fin n) = chain.D := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; rw [hgD a ha]; exact ha
    · intro hx; exact ⟨x, hx, hgD x hx⟩
  show forcedExpand adj P₀ χι₀ sel chain (g v)
      = (forcedExpand adj P₀ χι₀ sel chain v).image g
  unfold forcedExpand
  rw [Finset.image_insert, ← movedSet_image hg hgP, Finset.image_insert, hDfix]

/-! ### The scheme-as-labelled-graph bridge — `SchemeAutGroup` as a graph stabilizer

The seal capstones live on bare `SchurianScheme` (no `AdjMatrix`), but the cross-branch harvest and the
`LargenessBridge` (`Scheme.lean §12.1`) are graph-side. `schemeAdj` faithfully encodes a scheme as a *labelled*
graph, bridging the two:

* `schemeAdj` encodes `S` as the labelled adjacency `(v, w) ↦ (relOfPair v w).val` — a single graph whose
  edge labels are the relation indices, so `IsAut` on it coincides exactly with `IsSchemeAut`
  (`isAut_schemeAdj_iff`); hence `StabilizerAt (schemeAdj S) ⊥ ∅ = SchemeAutGroup S`
  (`stabilizerAt_schemeAdj_empty_eq`, trivial all-`unknown` `P`).
* `IsLargeSchemeViaAut` is the concrete largeness predicate: super-polynomiality of `|SchemeAutGroup|` (the
  genuine Cameron driver). The seal capstones instantiate the abstract `NonCascade`/`IsLargeScheme` at this
  predicate with the **identity** `LargenessBridge` (`fun _ _ h => h`): largeness is *carried* honestly, not
  fake-"derived" — `¬ IsLargeSchemeViaAut` = "small" is the cascade branch's antecedent. (The earlier
  `NoFusion`/`largenessBridge_viaHarvest` "derivation" was orbit-level **vacuous** — seal-handoff §2–§3 — and
  has been excised; the abstract `IsLarge : Nat → Prop` super-polynomiality citation is never concretized.) -/

/-- **A scheme as a labelled graph.** Encodes `S` into a single `AdjMatrix` whose entry `(v, w)` is the
index of the relation containing `(v, w)`. The labels make graph automorphisms of `schemeAdj S` coincide
with scheme automorphisms (`isAut_schemeAdj_iff`), bridging the scheme to the graph-side stabilizer-chain
machinery. -/
noncomputable def schemeAdj {m : Nat} (S : AssociationScheme m) : AdjMatrix m :=
  ⟨fun v w => (S.relOfPair v w).val⟩

/-- **Faithfulness of the encoding.** A permutation is a graph automorphism of `schemeAdj S` iff it is a
scheme automorphism of `S`: the labelled adjacency separates the relations, so preserving it is exactly
preserving every relation index. -/
theorem isAut_schemeAdj_iff {m : Nat} (S : AssociationScheme m) (π : Equiv.Perm (Fin m)) :
    IsAut π (schemeAdj S) ↔ IsSchemeAut S π := by
  constructor
  · intro hAut i v w
    have hr : S.relOfPair (π v) (π w) = S.relOfPair v w := by
      apply Fin.ext; exact hAut v w
    have h1 : S.rel i (π v) (π w) = true ↔ i = S.relOfPair v w := by
      rw [S.rel_iff_relOfPair, hr]
    have h2 : S.rel i v w = true ↔ i = S.relOfPair v w := S.rel_iff_relOfPair
    cases hb1 : S.rel i (π v) (π w) <;> cases hb2 : S.rel i v w <;> simp_all
  · intro hSA v w
    show (S.relOfPair (π v) (π w)).val = (S.relOfPair v w).val
    rw [IsSchemeAut.relOfPair_eq hSA v w]

/-- **The scheme-Aut group is the graph-stabilizer of the encoding.** With the trivial all-`unknown` `P`
(no order constraint), `StabilizerAt (schemeAdj S) ⊥ ∅` — the `P`-preserving automorphisms of the labelled
graph — is exactly `SchemeAutGroup S`. Carries `|·|` equality across the two sides of the bridge. -/
theorem stabilizerAt_schemeAdj_empty_eq {m : Nat} (S : SchurianScheme m) :
    StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅
      = S.toAssociationScheme.SchemeAutGroup := by
  ext π
  rw [mem_stabilizerAt_empty, isAut_schemeAdj_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-! ### §13a — Single-base recovery on `schemeAdj` is free (the self-detection base case)

The seal's recovery predicate `CellsAreOrbits (schemeAdj S) …` is keyed on `schemeAdj S`, which encodes the
**full** scheme (`adj v w = (relOfPair v w).val`, a multi-valued edge label `signature` reads in full — *not*
the single-relation `SchurianSchemeGraph`/`EdgeGenerates` setting). On `schemeAdj`, **single-base** recovery is
unconditional for *every* schurian scheme: `warmRefine` from `{v}` separates by `relOfPair(v,·)` (the unique
colour of the individualized `v` makes the `v`-neighbour tuple identify the relation), and for a schurian
scheme `relOfPair(v,·)`-classes **are** the `Stab(v)`-orbits (`vProfile_iff_schemeOrbit`). So the entire
self-detection crux lives at **multi-base** (`|T| ≥ 2`), where the *joint* profile can fall short of the joint
orbit (the `s(C)` gap). This subsection lands the single-base base case (the affine multi-base argument
extends it); full account: `docs/chain-descent-self-detection-plan.md` §5.1. -/

/-- **Iterated refinement is split-only** (the general `k`-fold colour-equality form of
`warmRefine_refines`): equal colour after `k` rounds implies equal colour before. -/
theorem iterate_refineStep_colour_refines {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∀ (k : Nat) (χ : Colouring n) {v w : Fin n},
      ((refineStep adj P)^[k]) χ v = ((refineStep adj P)^[k]) χ w → χ v = χ w := by
  intro k
  induction k with
  | zero => intro χ v w h; exact h
  | succ k ih =>
    intro χ v w h
    rw [Function.iterate_succ, Function.comp_apply] at h
    exact refineStep_refines adj P χ (ih (refineStep adj P χ) h)

/-- The individualized vertex `v` carries a unique colour: `individualizedColouring n {v}` separates `v`
from every other vertex. -/
private theorem individualizedColouring_singleton_sep {n : Nat} (v : Fin n) :
    ∀ x : Fin n, x ≠ v → individualizedColouring n {v} x ≠ individualizedColouring n {v} v := by
  intro x hx
  have h1 : individualizedColouring n {v} x = 0 := by simp [individualizedColouring, hx]
  have h2 : individualizedColouring n {v} v = v.val + 1 := by simp [individualizedColouring]
  rw [h1, h2]; omega

/-- **`warmRefine` from `{v}` separates by the relation to `v`.** For non-`v` vertices `w, u` in the same
`warmRefine (schemeAdj S) … {v}` cell, `relOfPair v w = relOfPair v u`. Proof: peel `warmRefine` to one
`refineStep` round (`iterate_refineStep_refines`), read off `signature` equality (`refineStep_iff`), and use
the count bridge (`signature_eq_card_eq`): the unique-colour entry for the individualized `v` is the only
tuple with first component `χ v`, so the two `v`-neighbour tuples coincide — i.e. `adj.adj w v = adj.adj u v`,
which on `schemeAdj` is `(relOfPair v w).val = (relOfPair v u).val`. -/
theorem relOfPair_eq_of_warmRefine_singleton {n : Nat} (S : AssociationScheme n) {v w u : Fin n}
    (hwv : w ≠ v) (huv : u ≠ v)
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n {v}) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n {v}) u) :
    S.relOfPair v w = S.relOfPair v u := by
  classical
  have hpos : 0 < n := Fin.pos v
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set adj := schemeAdj S
  set P : PMatrix (m + 1) := fun _ _ => POE.unknown
  set χ := individualizedColouring (m + 1) {v} with hχ
  -- peel warmRefine = refineStep^[m+1] to a single refineStep round, then to signature equality
  simp only [warmRefine] at h
  rw [Function.iterate_succ_apply] at h
  have hrs : refineStep adj P χ w = refineStep adj P χ u :=
    iterate_refineStep_colour_refines adj P m (refineStep adj P χ) h
  have hsig : signature adj P χ w = signature adj P χ u :=
    ((refineStep_iff adj P χ w u).mp hrs).2
  -- χ v is the unique individualized colour
  have hχv : χ v = v.val + 1 := by rw [hχ]; simp [individualizedColouring]
  have hχ_eq_v : ∀ x : Fin (m + 1), χ x = v.val + 1 → x = v := by
    intro x hx
    by_contra hxv
    have hx0 : χ x = 0 := by rw [hχ]; simp [individualizedColouring, hxv]
    omega
  have hcard := signature_eq_card_eq adj P χ hsig (χ v, adj.adj w v, P w v)
  -- LHS filter = {v}: the unique-colour `v`-tuple is the only match
  have hFw : (Finset.univ.filter (fun u' : Fin (m + 1) =>
      u' ≠ w ∧ (χ v, adj.adj w v, P w v) = (χ u', adj.adj w u', P w u'))) = {v} := by
    apply Finset.ext; intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, heq⟩
      exact hχ_eq_v x ((congrArg Prod.fst heq).symm.trans hχv)
    · rintro rfl; exact ⟨Ne.symm hwv, rfl⟩
  rw [hFw, Finset.card_singleton] at hcard
  -- RHS filter has card 1, hence nonempty; its witness gives the relation equality
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hcard ▸ Nat.one_pos)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨_, hxeq⟩ := hx
  have hxv : v = x := (hχ_eq_v x ((congrArg Prod.fst hxeq).symm.trans hχv)).symm
  subst hxv
  -- second component: adj.adj w v = adj.adj u v, i.e. (relOfPair v w).val = (relOfPair v u).val
  have hval : adj.adj w v = adj.adj u v := congrArg (fun p : Nat × Nat × POE => p.2.1) hxeq
  have hrel : S.relOfPair w v = S.relOfPair u v := Fin.val_injective hval
  rw [S.relOfPair_symm v w, S.relOfPair_symm v u]; exact hrel

/-- **Single-base recovery is free (the self-detection base case).** For *every* schurian scheme, the
`warmRefine` cells after individualizing a single vertex `v` coincide with the `Stab(v)`-orbits:
`CellsAreOrbits (schemeAdj S) … {v}`. Combines `relOfPair_eq_of_warmRefine_singleton` (cells ⊆
`relOfPair(v,·)`-classes) with `vProfile_iff_schemeOrbit` (`relOfPair(v,·)`-classes = orbits, schurian) and
`isAut_schemeAdj_iff` (scheme-aut = graph-aut). The entire crux is therefore the *multi-base* extension. -/
theorem cellsAreOrbits_schemeAdj_singleton {n : Nat} (S : SchurianScheme n) (v : Fin n) :
    CellsAreOrbits (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) {v} := by
  classical
  intro w u hcell
  by_cases hwv : w = v
  · by_cases huv : u = v
    · rw [hwv, huv]; exact OrbitPartition.refl v
    · rw [hwv] at hcell
      exact absurd hcell.symm (iterate_refineStep_preserves_singleton
        (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) v n
        (individualizedColouring n {v}) (individualizedColouring_singleton_sep v) u huv)
  · by_cases huv : u = v
    · rw [huv] at hcell
      exact absurd hcell (iterate_refineStep_preserves_singleton
        (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) v n
        (individualizedColouring n {v}) (individualizedColouring_singleton_sep v) w hwv)
    · have hrel : S.toAssociationScheme.relOfPair v w = S.toAssociationScheme.relOfPair v u :=
        relOfPair_eq_of_warmRefine_singleton S.toAssociationScheme hwv huv hcell
      have hvp : vProfile S.toAssociationScheme v w = vProfile S.toAssociationScheme v u := by
        unfold vProfile; rw [hrel]
      obtain ⟨π, hπ, hπv, hπwu⟩ := (S.vProfile_iff_schemeOrbit v w u).mp hvp
      exact ⟨π, (isAut_schemeAdj_iff _ π).mpr hπ, fun _ _ => rfl,
        fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hπv, hπwu⟩

/-- **Concrete largeness predicate (the genuine Cameron driver).** A scheme is large when its automorphism
group `SchemeAutGroup` has super-polynomial order, with `IsLarge : Nat → Prop` the abstract asymptotic
citation. The instantiation of the §12 `IsLargeScheme` parameter the bridge discharges into. -/
def IsLargeSchemeViaAut (IsLarge : Nat → Prop) : ∀ (m : Nat), SchurianScheme m → Prop :=
  fun _ S => IsLarge (Nat.card S.toAssociationScheme.SchemeAutGroup)

/-! ### The oracle-capability seal, assembled — "reaches a rigid or Cameron residual"

The project's top-level goal (`docs/00-START-HERE.md` §2, strategy §15 the two guarantees, exhaustive-obstruction
§0.5 the seal) as a **single theorem**: every rank-≥3 schurian scheme residual either **reaches a rigid
residual** (is driven to a trivial residual by the cascade/abelian oracles — legs A/B) or **is a Cameron
section** (the honest flag — leg C). It wires the landed `exhaustiveObstruction_scheme_nonCascade_trichotomy`
(`¬IsPrimitive ∨ ¬NonCascade ∨ IsCameronScheme`) into that dichotomy, mapping each non-Cameron branch to its
leg via an explicit reduction hypothesis. The value is **crystallization**: the goal becomes one object, and the
hypothesis list + `#print axioms` are the exact, honest remainder.

`ReachesRigid : ∀ m, SchurianScheme m → Prop` is the abstract residual-outcome predicate (the descent drives this
residual to a rigid/discrete node) — kept abstract because the descent dynamics are not a single Lean object; the
two reduction hypotheses are its interface. **Status of each input:**
* `hClassify` — the cited Babai 1981 / Sun–Wilmes classification (a legitimate external citation, never an axiom).
* `hCascade` — `¬NonCascade` (the residual cascades / recovers at poly depth) ⟹ reaches rigid. This is **leg A**
  (orbit recovery), the well-supported branch — `recoverableByDepth_pPolynomial`/`_cfi` are its witnesses.
* `hImprimitive` — `¬IsPrimitive` (imprimitive) ⟹ reaches rigid (refine on the block system). This is the **one
  genuine open, in-scope, theorem-shaped gap** (the primitivity reduction; `cell_splits_of_imprimitive` modulo
  `BlockRefinementVisible`, the depth-graded boundary Shrikhande pinned). The correctness-form route (eventual
  block visibility + cell-size induction) is the live target. -/

/-- **The seal capstone (general form): a scheme residual reaches rigid or is Cameron.** Given the cited
classification, the largeness bridge, and the two leg-reduction hypotheses (cascade ⟹ rigid; imprimitive ⟹
rigid), every rank-≥3 schurian scheme residual satisfies `ReachesRigid ∨ IsCameronScheme`. Pure assembly of
`exhaustiveObstruction_scheme_nonCascade_trichotomy`; the conclusion is the project's goal as one statement. -/
theorem reachesRigidOrCameron {n : Nat}
    {NonCascade IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    {ReachesRigid : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (hbridge : LargenessBridge NonCascade IsLargeScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : ¬ NonCascade n S → ReachesRigid n S)
    (hImprimitive : ¬ S.toAssociationScheme.IsPrimitive → ReachesRigid n S) :
    ReachesRigid n S ∨ IsCameronScheme n S := by
  rcases exhaustiveObstruction_scheme_nonCascade_trichotomy hClassify hbridge S hne hrank with
    h | h | h
  · exact Or.inl (hImprimitive h)
  · exact Or.inl (hCascade h)
  · exact Or.inr h

/-- **The seal capstone, primitivity-carrying form (the self-detection wiring).** Identical to
`reachesRigidOrCameron` but the cascade reduction is sharpened to the **primitive floor**:
`hCascade : IsPrimitive ∧ ¬ NonCascade → ReachesRigid`. This is the honest shape of the open content — the
cascade obligation is *self-detection* (a primitive small residual recovers), not an all-`¬NonCascade`
claim (imprimitive small residuals are routed through `hImprimitive` first). Wires the strengthened
`exhaustiveObstruction_scheme_nonCascade_trichotomy'`. -/
theorem reachesRigidOrCameron' {n : Nat}
    {NonCascade IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    {ReachesRigid : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (hbridge : LargenessBridge NonCascade IsLargeScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : S.toAssociationScheme.IsPrimitive ∧ ¬ NonCascade n S → ReachesRigid n S)
    (hImprimitive : ¬ S.toAssociationScheme.IsPrimitive → ReachesRigid n S) :
    ReachesRigid n S ∨ IsCameronScheme n S := by
  rcases exhaustiveObstruction_scheme_nonCascade_trichotomy' hClassify hbridge S hne hrank with
    h | h | h
  · exact Or.inl (hImprimitive h)
  · exact Or.inl (hCascade h)
  · exact Or.inr h

/-! ### The seal's rigid side, concretely — the NON-VACUOUS recovery predicate

`reachesRigidOrCameron` keeps `ReachesRigid` abstract; a concrete capstone must instantiate it with a
*meaningful* predicate. **Cautionary correction — do not regress (2026-06-07).** The earlier instance
`SchemeReproduced := ∃ gens, closure gens = SchemeAutGroup S` is **vacuously true**: every finite group is
finitely generated, so `gens = the group's own carrier` witnesses it with no recovery hypothesis whatsoever
(machine-checked: `⟨↑SchemeAutGroup, Subgroup.closure_eq _⟩` proves it for *every* scheme). The same vacuity
infects *orbit*-level coverage (`OrbitPartition b w → ∃ g ∈ gens, g b = w`): orbit-mates are
automorphism-related by definition, so `gens = all automorphisms` always satisfies it. The genuine,
algorithmic content of "reaches a rigid residual" is that the **refinement-computable** (same-`warmRefine`-cell)
harvest suffices — and the same-cell clause is **false when cells ⊋ orbits** (high `s(C)`), since a same-cell
non-orbit pair has no realizing automorphism. So the rigid predicate is keyed on **visible** realizers below,
making it hold exactly on the recoverable class and genuinely unprovable for a non-recovering scheme.

The block-decomposition capstones that concluded `SchemeReproduced ∨ Cameron` were therefore proving a
trivially-true disjunction and are **retired**. The graph-level coverage theory
(`reachesRigid_of_blockDecomposition`, the `hreach`/`hfiber` suppliers, `coversOrbits_*`,
`hfiber_of_fiberVisibleRealizers`) remains valid as *conditional* statements (coverage ⟹ closure = stabilizer);
it was the existential *packaging* into "the scheme recovers" that was vacuous, not those lemmas. The
genuinely-open content — *visible* recovery holding without whole-graph recovery, via visible quotient + fiber
recovery — is the `s(C)` frontier (`hfiber_of_fiberVisibleRealizers` is its fiber half). -/

/-- **The non-vacuous `ReachesRigid`: the refinement-computable harvest recovers the scheme.** `S` is
*recovered* when there is a harvested generating set `gens` (path-fixing at the root, `hsound`) and a base
sequence `bs` such that **at every level** every same-`warmRefine`-cell pair is realized by a harvested
residual automorphism in `gens`, and `bs` reaches a base. The same-cell (visible) realizer clause is the
non-vacuity: it is satisfiable only where cells = orbits (recovery), false for high `s(C)`. Contrast the retired
`SchemeReproduced` (`∃ gens, closure gens = group`), which was trivially true. -/
def SchemeRecovered : ∀ (m : Nat), SchurianScheme m → Prop :=
  fun m S => ∃ (gens : Set (Equiv.Perm (Fin m))) (bs : List (Fin m)),
    (∀ g ∈ gens, g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
    (∀ T : Finset (Fin m), (∅ : Finset (Fin m)) ⊆ T → ∀ b w : Fin m,
        warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) b
            = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) w →
        ∃ g, g ∈ gens
          ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g b = w) ∧
    IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
      (bs.foldl (fun s b => insert b s) ∅)

/-- **Recovery ⟹ the group is reproduced (the "reaches rigid" payoff, a theorem now, not a free existential).**
From `SchemeRecovered` (visible realizers + base), the harvested generators generate exactly `SchemeAutGroup S`,
via `closure_eq_stabilizerAt_of_visibleRealizers` + the `schemeAdj` bridge (`gensAt_empty_eq` +
`stabilizerAt_schemeAdj_empty_eq`). This is the content the vacuous `SchemeReproduced` asserted for free; here it
is *earned* from the (non-vacuous) visible-recovery witness. -/
theorem schemeAutGroup_eq_closure_of_recovered {n : Nat} {S : SchurianScheme n}
    (h : SchemeRecovered n S) :
    ∃ gens : Set (Equiv.Perm (Fin n)),
      Subgroup.closure gens = S.toAssociationScheme.SchemeAutGroup := by
  obtain ⟨gens, bs, hsound, hreal, hbase⟩ := h
  refine ⟨gens, ?_⟩
  have hreaches := closure_eq_stabilizerAt_of_visibleRealizers bs hreal hbase
  rw [gensAt_empty_eq hsound] at hreaches
  exact hreaches.trans (stabilizerAt_schemeAdj_empty_eq S)

/-- **Discharge `SchemeRecovered` from the visible-realizer harvest.** Bundling the harvest interface: the
path-fixing soundness, the per-level visible (same-cell) realizers, and a terminal base *are* a recovery
witness. The single tool both non-Cameron branches of the seal use; the visible-realizer hypothesis is
satisfiable on the recoverable class (`recoverableByDepth_pPolynomial` metric/DRG, `recoverableByDepth_cfi` CFI)
and false off it — exactly the non-vacuity. -/
theorem schemeRecovered_of_visibleRealizers {n : Nat} (S : SchurianScheme n)
    {gens : Set (Equiv.Perm (Fin n))} (bs : List (Fin n))
    (hsound : ∀ g ∈ gens,
        g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅)
    (hreal : ∀ T : Finset (Fin n), (∅ : Finset (Fin n)) ⊆ T → ∀ b w : Fin n,
        warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring n T) b
            = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring n T) w →
        ∃ g, g ∈ gens
          ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g b = w)
    (hbase : IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
        (bs.foldl (fun s b => insert b s) ∅)) :
    SchemeRecovered n S :=
  ⟨gens, bs, hsound, hreal, hbase⟩

/-- **The seal capstone — both non-Cameron branches reduce to visible recovery (NON-VACUOUS).** Every rank-≥3
schurian scheme residual `SchemeRecovered ∨ IsCameronScheme`: if it cascades (`¬NonCascade`) or is imprimitive
(`¬IsPrimitive`) it is **recovered** (the refinement-computable harvest reproduces `SchemeAutGroup`), else it is
a **Cameron section** (the cited classification). Both non-Cameron branches are discharged *identically* from a
visible-realizer harvest via `schemeRecovered_of_visibleRealizers` — the imprimitivity/cascade distinction is
only *which descent observation triggers* the recovery obligation, not a different mechanism (the orbit-level
block decomposition that previously distinguished them was the vacuous detour; see the section note).
`hCascadeHarvest`/`hImprimRecovery` are the substrate-conditional recovery witnesses; `SchemeRecovered` is
genuinely false for a non-recovering scheme, so this disjunction is **not** trivially true — proving it for an
arbitrary residual needs the open "non-recovering ⟹ Cameron" leak (the `s(C)` frontier), which is exactly why
those hypotheses are carried. -/
theorem reachesRigidOrCameron_viaRecovery {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascadeHarvest : ¬ IsLargeSchemeViaAut IsLarge n S →
        ∃ (gens : Set (Equiv.Perm (Fin n))) (bs : List (Fin n)),
          (∀ g ∈ gens,
              g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
          (∀ T : Finset (Fin n), (∅ : Finset (Fin n)) ⊆ T → ∀ b w : Fin n,
              warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
                    (individualizedColouring n T) b
                  = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
                    (individualizedColouring n T) w →
              ∃ g, g ∈ gens
                ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g b = w) ∧
          IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
            (bs.foldl (fun s b => insert b s) ∅))
    (hImprimRecovery : ¬ S.toAssociationScheme.IsPrimitive →
        ∃ (gens : Set (Equiv.Perm (Fin n))) (bs : List (Fin n)),
          (∀ g ∈ gens,
              g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
          (∀ T : Finset (Fin n), (∅ : Finset (Fin n)) ⊆ T → ∀ b w : Fin n,
              warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
                    (individualizedColouring n T) b
                  = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
                    (individualizedColouring n T) w →
              ∃ g, g ∈ gens
                ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g b = w) ∧
          IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
            (bs.foldl (fun s b => insert b s) ∅)) :
    SchemeRecovered n S ∨ IsCameronScheme n S := by
  refine reachesRigidOrCameron (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := SchemeRecovered) hClassify (fun _ _ h => h) S hne hrank ?_ ?_
  · intro hnc
    obtain ⟨gens, bs, hsound, hreal, hbase⟩ := hCascadeHarvest hnc
    exact schemeRecovered_of_visibleRealizers S bs hsound hreal hbase
  · intro himp
    obtain ⟨gens, bs, hsound, hreal, hbase⟩ := hImprimRecovery himp
    exact schemeRecovered_of_visibleRealizers S bs hsound hreal hbase

/-! ### Leg B in the seal — the hidden-abelian consumption certificate (G1b)

`SchemeRecovered` (above) is **visible recovery only**: it asks that same-`warmRefine`-cell pairs be
realized by harvested automorphisms, which holds exactly where cells = orbits. A **hidden-abelian**
residual — a `Z₂^d`/abelian symmetry 1-WL cannot see (CFI gauge twists; high-WL circulants, whose
WL-dimension is *unbounded*, Wu–Ren–Ponomarenko 2025) — fails `SchemeRecovered` *and* is not Cameron, so
the recovery-only seal cannot place it. It is consumed by the **linear oracle (leg B)** instead: the
abelian residual's decision candidates are **uniquely determined on the cell** (L1–L3, `Group.lean`), so
the oracle reads the single determined candidate and collapses the branch — no 1-WL cell/orbit
coincidence required.

The honest, non-vacuous leg-B certificate is that **determinacy**, *earned* from abelianness via L3
(`aut_agree_on_orbit_of_comm`), not asserted by fiat. Contrast the bound-free `Findable.abelian`
constructor, which concludes from `ResidualAbelian ∧ ¬IsBase` with *no* consumption proof (a soft
vacuity), and `FindableWithin.abelian`, which keys on `RecoverableByDepth` = visible recovery and so
**conflates leg B into leg A** (the rev. 2 finding; do not use them here — see
[`chain-descent-seal-handoff.md`](../../docs/chain-descent-seal-handoff.md) §4 G1b). Non-vacuity check:
the determinacy clause is genuinely **false** for a non-abelian residual whose candidates disagree on a
cell — that is exactly `not_comm_of_orbit_disagree` (`Group.lean`). -/

/-- **The leg-B (hidden-abelian) consumption certificate.** A scheme residual is *abelian-consumed* when
its root residual is non-trivial (`¬ IsBase`) and every decision is **uniquely determined on its cell**:
any two automorphisms `g, h` that send `a ↦ b` agree on the whole orbit of `a`. This is the linear
oracle's "unique candidate" property — the content of leg B — keyed via L3, so it is *not*
orbit-level-vacuous: it **fails** for a non-abelian residual with disagreeing candidates
(`not_comm_of_orbit_disagree`). Earned from `ResidualAbelian` by `abelianConsumed_of_residualAbelian`. -/
def AbelianConsumed : ∀ (m : Nat), SchurianScheme m → Prop :=
  fun m S =>
    (¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
    ∀ (a b c : Fin m) (g h : Equiv.Perm (Fin m)),
      IsAut g (schemeAdj S.toAssociationScheme) → IsAut h (schemeAdj S.toAssociationScheme) →
      g a = b → h a = b →
      (∃ k : Equiv.Perm (Fin m), IsAut k (schemeAdj S.toAssociationScheme) ∧ k a = c) →
      g c = h c

/-- **Abelian residual ⟹ abelian-consumed (the leg-B core, citation-free).** If the root residual group
is abelian (`ResidualAbelian`) and non-trivial (`¬ IsBase`), the residual is consumed: its decisions are
uniquely determined on their cells. The determinacy is `aut_agree_on_orbit_of_comm` (L3, `Group.lean`) —
the consumption is *proven*, not assumed. No citation, no WL-dimension content; it survives CFI's
non-trivial global stabilizers exactly because L3 is faithfulness/quotient-free. -/
theorem abelianConsumed_of_residualAbelian {n : Nat} {S : SchurianScheme n}
    (hcomm : ResidualAbelian (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅)
    (hnb : ¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) :
    AbelianConsumed n S := by
  refine ⟨hnb, fun a b c g h hg hh hga hha hc => ?_⟩
  have hAG : ∀ p q : AutGroup (schemeAdj S.toAssociationScheme), p * q = q * p := by
    intro p q
    have hres : ∀ r : AutGroup (schemeAdj S.toAssociationScheme),
        ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅ (r : Equiv.Perm (Fin n)) :=
      fun r => ⟨mem_autGroup.mp r.2, fun _ _ => rfl, fun v hv => absurd hv (Finset.notMem_empty v)⟩
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin n)) (hres p) (hres q))
  exact aut_agree_on_orbit_of_comm hAG hg hh hga hha hc

/-- **The seal capstone with leg B — recovery OR hidden-abelian, else Cameron (NON-VACUOUS).** Widens
`reachesRigidOrCameron_viaRecovery` so each non-Cameron branch may discharge via **either** visible
recovery (`SchemeRecovered`, leg A) **or** a hidden-abelian residual (`ResidualAbelian ∧ ¬ IsBase`, leg
B) — the latter routed to `AbelianConsumed` by the citation-free `abelianConsumed_of_residualAbelian`.
The branch hypotheses are therefore strictly **weaker** than the recovery-only form: an
abelian-but-not-visibly-recovering residual (high-WL circulant, CFI `tw ≥ 2`) now satisfies them via the
abelian disjunct, where `reachesRigidOrCameron_viaRecovery` could not. Conclusion:
`(SchemeRecovered ∨ AbelianConsumed) ∨ IsCameronScheme` — the seal's honest `(legA ∨ legB) ∨ Cameron`
dichotomy on the symmetric case. The residual open content is the same `s(C)` leak (G2): a
*non-abelian, non-recovering, non-Cameron* residual still cannot be placed, which is why the branch
hypotheses are carried. -/
theorem reachesRigidOrCameron_viaRecoveryOrAbelian {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : ¬ IsLargeSchemeViaAut IsLarge n S →
        SchemeRecovered n S ∨
        (ResidualAbelian (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅ ∧
          ¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeRecovered n S ∨
        (ResidualAbelian (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅ ∧
          ¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅)) :
    (SchemeRecovered n S ∨ AbelianConsumed n S) ∨ IsCameronScheme n S := by
  refine reachesRigidOrCameron (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := fun m S => SchemeRecovered m S ∨ AbelianConsumed m S)
    hClassify (fun _ _ h => h) S hne hrank ?_ ?_
  · intro hnc
    rcases hCascade hnc with hrec | ⟨hab, hnb⟩
    · exact Or.inl hrec
    · exact Or.inr (abelianConsumed_of_residualAbelian hab hnb)
  · intro himp
    rcases hImprim himp with hrec | ⟨hab, hnb⟩
    · exact Or.inl hrec
    · exact Or.inr (abelianConsumed_of_residualAbelian hab hnb)

/-! ### Depth-graded recovery (G1a) — beyond per-level / metric recovery

`SchemeRecovered` (above) demands visible realizers at **every** level `T ⊇ ∅` — that is *per-level* (depth-1 /
metric) recovery. A **depth-graded** consumable scheme fails it: CFI recovers only after `tw(H)`
individualizations, Shrikhande only after 2; at shallower levels cells ⊋ orbits, so a same-cell non-orbit pair
breaks the clause. This section models the depth-graded case honestly by **splitting the base sequence into a
bounded shallow phase `∅ → S₀` and a deep phase from the recovery set `S₀`**, glued by `coversOrbits_append`:

- **Deep phase** (`T ⊇ S₀`): the visible (refinement-computable) realizer clause — *non-vacuous*, satisfiable
  exactly where refinement recovers orbits from `S₀` (`CellsAreOrbits`). This is the genuine recovery content;
  CFI / Shrikhande satisfy it at their bounded depth, where `SchemeRecovered`'s `∀ T ⊇ ∅` could not.
- **Shallow phase** (`∅ → S₀`): `CoversOrbitsAlong` orbit-coverage — the **carried localisation** (per-level
  orbit-realization is *intrinsic*: a deep automorphism fixes too much to move a shallow orbit, so deep recovery
  does not supply shallow coverage for free). It stays substrate-conditional, but is now **localized to a bounded
  phase** rather than required at every level.
- **The bound `|S₀| ≤ bound`** is essential for non-vacuity: the *unbounded* form is vacuous (individualize
  everything ⟹ discrete; mirroring `recoverableByDepth_univ`). So depth-graded recovery is partly a modelling
  refinement (captures CFI/Shrikhande) and partly the polynomiality boundary (the bound).

`SchemeRecoveredByDepth … 0` recovers `SchemeRecovered` (empty shallow phase, `S₀ = ∅`), so the depth-graded
predicate **strictly generalizes** the per-level one. -/

/-- **Depth-graded recovery.** `S` is *recovered by depth `bound`* when there is a harvested generating set
`gens` (path-fixing at the root) and a **two-phase** base sequence `bs₁ ++ bs₂`: a shallow phase `bs₁` building
the bounded recovery set `S₀ = bs₁.foldl insert ∅` (`|S₀| ≤ bound`), with orbit-coverage along it
(`CoversOrbitsAlong`, the carried localisation), then a deep phase `bs₂` from `S₀` whose every same-`warmRefine`-cell
pair is realized by a harvested residual automorphism (visible recovery, satisfiable only where cells = orbits
from `S₀`), terminating at a base. Generalizes `SchemeRecovered` (which is the `S₀ = ∅` case) to the
depth-graded family (CFI, Shrikhande). Non-vacuity comes from the deep visible clause **and** the bound: the
unbounded form is vacuous. -/
def SchemeRecoveredByDepth : ∀ (m : Nat), SchurianScheme m → Nat → Prop :=
  fun m S bound => ∃ (gens : Set (Equiv.Perm (Fin m))) (bs₁ bs₂ : List (Fin m)),
    (∀ g ∈ gens, g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
    (bs₁.foldl (fun s b => insert b s) (∅ : Finset (Fin m))).card ≤ bound ∧
    CoversOrbitsAlong (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) gens bs₁ ∅ ∧
    (∀ T : Finset (Fin m), (bs₁.foldl (fun s b => insert b s) ∅) ⊆ T → ∀ b w : Fin m,
        warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) b
            = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) w →
        ∃ g, g ∈ gens
          ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g b = w) ∧
    IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
      (bs₂.foldl (fun s b => insert b s) (bs₁.foldl (fun s b => insert b s) ∅))

/-- **Depth-graded recovery ⟹ the group is reproduced.** From `SchemeRecoveredByDepth`, the harvested `gens`
generate exactly `SchemeAutGroup S`. The deep phase supplies `CoversOrbits bs₂ S₀` from the visible realizers
(`coversOrbits_of_visibleRealizers`); `coversOrbits_append` glues the carried shallow `CoversOrbitsAlong bs₁ ∅`
to it for `CoversOrbits (bs₁ ++ bs₂) ∅`; then `closure_eq_stabilizerAt_empty_of_coversOrbits` +
`stabilizerAt_schemeAdj_empty_eq`. So the depth-graded harvest reproduces the full root group, with the shallow
∅→S₀ coverage the only carried (localisation) input. -/
theorem schemeAutGroup_eq_closure_of_recoveredByDepth {n : Nat} {S : SchurianScheme n} {bound : Nat}
    (h : SchemeRecoveredByDepth n S bound) :
    ∃ gens : Set (Equiv.Perm (Fin n)),
      Subgroup.closure gens = S.toAssociationScheme.SchemeAutGroup := by
  obtain ⟨gens, bs₁, bs₂, hsound, _hbound, hshallow, hdeep, hbase⟩ := h
  have hdeepcov := coversOrbits_of_visibleRealizers bs₂ hdeep hbase
  have hcov := coversOrbits_append bs₁ bs₂ hshallow hdeepcov
  exact ⟨gens, (closure_eq_stabilizerAt_empty_of_coversOrbits (bs₁ ++ bs₂) hsound hcov).trans
    (stabilizerAt_schemeAdj_empty_eq S)⟩

/-- **Per-level recovery is the depth-0 case — depth-graded strictly generalizes `SchemeRecovered`.** A
metric/depth-1 recovered scheme is recovered by depth `0`: empty shallow phase (`bs₁ = []`, `S₀ = ∅`, the
`CoversOrbitsAlong [] ∅` clause is `True`), with the original `∀ T ⊇ ∅` visible realizers as the deep phase. So
`SchemeRecovered` ⊆ `SchemeRecoveredByDepth … 0`, and the depth-graded predicate captures everything the
per-level one does plus the depth-graded family (CFI/Shrikhande) it could not. -/
theorem schemeRecoveredByDepth_of_schemeRecovered {n : Nat} {S : SchurianScheme n}
    (h : SchemeRecovered n S) : SchemeRecoveredByDepth n S 0 := by
  obtain ⟨gens, bs, hsound, hreal, hbase⟩ := h
  exact ⟨gens, [], bs, hsound, by simp, trivial, by simpa using hreal, by simpa using hbase⟩

/-! ### Increment 2 — the semantic recovery bridge (Phase 1 of the self-detection plan)

`SchemeRecoveredByDepth` is the seal's *harvest-witness* recovery predicate (a `gens`/base sequence + per-`T`
visible realizers). The self-detection lemma (Phase 2) is most naturally stated and attacked on a *semantic*
recovery predicate — **cells coincide with orbits above a bounded individualization set**. This subsection
builds that predicate (`StablyRecoverable`) and the clean bridge `StablyRecoverable ⟹ SchemeRecoveredByDepth`,
so the crux can be stated on the semantic object the catalogue/affine analysis measures.

**Why "above a bounded set", not "at a single set".** `SchemeRecoveredByDepth`'s deep clause quantifies over
*every* `T ⊇ S₀`; a single `CellsAreOrbits S₀` does **not** give per-`T` realizers fixing `T`'s extra
individualized points (the "localisation", seal-handoff §6 insight 7). The honest semantic match is
`StablyRecoverable S₀ := ∀ T ⊇ S₀, CellsAreOrbits T` — recovery is *stable* above `S₀`. This is exactly what
separability monotonicity yields (more individualization keeps a separable scheme separable), so it is the
right Phase-2 target; and it is **non-vacuous** (it is cells = orbits, false for high `s(C)`), not orbit-level
coverage. -/

/-- **A finset is reachable from a sub-finset by a `foldl`-insert over some list.** `S₀.toList`-style helper:
for any `S U`, some list inserts `U`'s elements into `S`. Used to materialize the shallow set `S₀` and the
terminal base as `foldl`-insert sequences, the shape `SchemeRecoveredByDepth` demands. -/
theorem exists_foldl_insert_eq {n : Nat} (S U : Finset (Fin n)) :
    ∃ l : List (Fin n), l.foldl (fun s b => insert b s) S = S ∪ U := by
  classical
  induction U using Finset.induction with
  | empty => exact ⟨[], by simp⟩
  | @insert a U' _ ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ [a], ?_⟩
    rw [List.foldl_append, hl]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Finset.union_insert]

/-- **Stable recovery above a set** — the semantic self-detection target. `S₀` is a set above which
1-WL recovers the orbits: at *every* `T ⊇ S₀`, the `warmRefine` cells coincide with the `Aut_T`-orbits
(`CellsAreOrbits`). Non-vacuous (cells = orbits is false for high `s(C)`); the honest match to
`SchemeRecoveredByDepth`'s per-`T` deep clause, with the localisation made explicit (recovery is *stable*,
not just present at `S₀`). -/
def StablyRecoverable {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (S₀ : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), S₀ ⊆ T → CellsAreOrbits adj P T

/-- **The root group covers every orbit along any base sequence** — `CoversOrbitsAlong` is satisfied by
`gens = ↑(StabilizerAt … ∅)` (all `P`-preserving automorphisms). This is the (genuinely true, here
non-load-bearing) *orbit-level* coverage: an orbit-mate at `S` is realized by the residual automorphism
itself, which lies in `gensAt … S`. The non-vacuous content of recovery is the *visible* deep clause, not
this. -/
theorem coversOrbitsAlong_stabilizerAtEmpty {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (bs : List (Fin n)) (S : Finset (Fin n)) :
    CoversOrbitsAlong adj P (↑(StabilizerAt adj P ∅)) bs S := by
  induction bs generalizing S with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨fun w how => ?_, ih _⟩
    obtain ⟨π, hres, hπ⟩ := orbitPartition_iff_residualAut.mp how
    exact ⟨π, Subgroup.subset_closure
      ⟨mem_stabilizerAt_empty.mpr ⟨hres.1, hres.2.1⟩, mem_stabilizerAt.mpr hres⟩, hπ⟩

/-- **The semantic recovery bridge: `StablyRecoverable ⟹ SchemeRecoveredByDepth`.** From stable recovery above
a bounded set `S₀` (`|S₀| ≤ bound`), the scheme is recovered by depth `bound`. Witness: `gens` = all residual
automorphisms at `∅`; shallow `bs₁` materializes `S₀` (orbit coverage by `coversOrbitsAlong_stabilizerAtEmpty`);
the deep clause at each `T ⊇ S₀` reads a visible realizer off `CellsAreOrbits T` (same cell ⟹ same orbit ⟹ a
residual automorphism `π` carrying the pair, `π ∈ StabilizerAt ∅` since it is a `P`-preserving aut); the base
comes from `exists_isBase_saturated`. This converts the seal's harvest-witness recovery into the *semantic*
object Phase 2 attacks. -/
theorem schemeRecoveredByDepth_of_stablyRecoverable {n : Nat} (S : SchurianScheme n)
    {S₀ : Finset (Fin n)} {bound : Nat} (hcard : S₀.card ≤ bound)
    (hstab : StablyRecoverable (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) S₀) :
    SchemeRecoveredByDepth n S bound := by
  classical
  set adj := schemeAdj S.toAssociationScheme with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  obtain ⟨l₁, hl₁⟩ := exists_foldl_insert_eq (∅ : Finset (Fin n)) S₀
  rw [Finset.empty_union] at hl₁
  obtain ⟨k, _, hsub, hbase⟩ := exists_isBase_saturated adj P S₀
  set Tb := (movedStep adj P)^[k] S₀ with hTb
  obtain ⟨l₂, hl₂⟩ := exists_foldl_insert_eq S₀ (Tb \ S₀)
  rw [Finset.union_sdiff_of_subset hsub] at hl₂
  refine ⟨(↑(StabilizerAt adj P ∅) : Set (Equiv.Perm (Fin n))), l₁, l₂,
    fun g hg => hg, ?_, coversOrbitsAlong_stabilizerAtEmpty adj P l₁ ∅, ?_, ?_⟩
  · rw [hl₁]; exact hcard
  · intro T hT b w hcell
    rw [hl₁] at hT
    obtain ⟨π, hres, hπ⟩ := orbitPartition_iff_residualAut.mp (hstab T hT b w hcell)
    exact ⟨π, mem_stabilizerAt_empty.mpr ⟨hres.1, hres.2.1⟩, hres, hπ⟩
  · rw [hl₁, hl₂]; exact hbase

/-- **The semantic self-detection proposition** — `SelfDetectsAtDepth` restated on `StablyRecoverable`. A
schurian residual *self-detects stably at depth `bound`* when, *if primitive and small*, it recovers stably
above some bounded set (`∃ S₀, |S₀| ≤ bound ∧ StablyRecoverable S₀`). This is the cleanest semantic form of the
self-detection lemma — the object the affine module-theory argument (Phase 2) produces and the catalogue probe
measures (cells = orbits above `base + O(1)` individualizations). -/
def SelfDetectsStably {n : Nat} (S : SchurianScheme n) (IsLarge : Nat → Prop) (bound : Nat) : Prop :=
  S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
    ∃ S₀ : Finset (Fin n), S₀.card ≤ bound ∧
      StablyRecoverable (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) S₀

/-! ### Phase 2, M2 reduction — discreteness ⟹ stable recovery (general; the crux simplification)

The research crux (M2: `irreducible G₀ ⟹ StablyRecoverable bounded`) reduces — **for any schurian scheme,
not just affine** — to a single refinement-only condition: *individualizing a bounded set warm-refines to a
**discrete** colouring* (separates all vertices). This is the cleanest form of the self-detection target, and
it unifies the seal's open content with the existing cascade-to-discreteness machinery (CFI
`theorem_1_HOR_cfi_oddDeg`, `isBase_of_discrete_warmRefine`) and the empirical probes (which measure greedy
depth-to-discreteness). It also separates the two budget terms cleanly: discretization depth = base(G)
[group-theoretic, bounded: a spanning set gives trivial stabilizer] + `s(C)` [the WL-dimension stickiness — the
open term]. **Faithful, not lossy:** at the primitive floor, `StablyRecoverable S₀` forces `CellsAreOrbits` at
a base above `S₀` where orbits are trivial, hence discreteness there — so the two are equivalent for the crux,
but `Discrete` is a single monotone refinement condition. -/

/-- **Discreteness ⟹ stable recovery (general).** If individualizing `S₀` warm-refines to a `Discrete`
colouring, then `StablyRecoverable adj P S₀` holds. Discreteness propagates to every `T ⊇ S₀`
(`individualizedColouring_refines` + `warmRefine_refines_initial`: a finer initial colouring stays discrete),
and `Discrete ⟹ CellsAreOrbits` is `cellsAreOrbits_of_discrete`. Reduces the multi-base recovery crux to a
pure "reaches singletons at bounded depth" statement. Non-vacuous: `Discrete` is false for any scheme with a
nontrivial residual symmetry above `S₀`. -/
theorem stablyRecoverable_of_discrete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S₀ : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S₀))) :
    StablyRecoverable adj P S₀ := by
  intro T hsub
  apply cellsAreOrbits_of_discrete
  intro v w hvw
  exact hd v w (warmRefine_refines_initial (individualizedColouring_refines hsub) v w hvw)

/-- **The crux, reduced to bounded discretization.** If a primitive small schurian residual individualizes a
bounded set to discreteness, it self-detects stably. So `SelfDetectsStably` — the seal's sole open content —
follows from *"primitive small ⟹ ∃ bounded `S₀` with `warmRefine`-from-`S₀` discrete"*, a refinement-only
(orbit-free) statement. This is the M2 target the affine module argument (and any Phase-2 family) now produces;
the catalogue/affine probes measure exactly this discretization depth. -/
theorem selfDetectsStably_of_discretizes {n : Nat} (S : SchurianScheme n) (IsLarge : Nat → Prop)
    (bound : Nat)
    (h : S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
        ∃ S₀ : Finset (Fin n), S₀.card ≤ bound ∧
          Discrete (warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
            (individualizedColouring n S₀))) :
    SelfDetectsStably S IsLarge bound := by
  intro hps
  obtain ⟨S₀, hcard, hd⟩ := h hps
  exact ⟨S₀, hcard, stablyRecoverable_of_discrete hd⟩

/-! ### Phase 2, M2-B — the depth-1 discreteness producer (the joint-profile separation tool)

`stablyRecoverable_of_discrete` reduced the crux to `Discrete (warmRefine from S₀)`. This block gives a
*concrete, finite, checkable* sufficient condition for that discreteness — **the depth-1 joint profile
`(relOfPair t ·)_{t ∈ T}` separates all vertices** — together with the multi-base reduction that makes it
work. The mechanism: `warmRefine` cells from base set `T` **refine** the joint-`T`-profile partition (the
multi-base generalization of `relOfPair_eq_of_warmRefine_singleton`), and — the clean part — that
generalization *reduces to the single-base A1 lemma* via `warmRefine_refines_initial` (warmRefine-from-`T`
refines warmRefine-from-`{t}` for each `t ∈ T`), with no fresh signature argument. So if the joint profile is
injective, cells are singletons. **Scope (honest):** this is the **depth-1** producer — it covers the
depth-1-separating sub-class (most primitive schemes in the catalogue/affine probes), the base case of the
iterated argument. The iterated (cyclotomic / `s(C) ≥ 2`, depth base+O(1)) extension is the remaining open
content. The affine difference-form (`affineScheme`) is the `G₀`-orbit-of-difference reading. -/

/-- Each individualized point `t ∈ T` carries a colour unique to it under `individualizedColouring n T`
(the `Finset`-set analogue of `individualizedColouring_singleton_sep`). -/
theorem individualizedColouring_mem_sep {n : Nat} {T : Finset (Fin n)} {t : Fin n} (ht : t ∈ T) :
    ∀ u : Fin n, u ≠ t → individualizedColouring n T u ≠ individualizedColouring n T t := by
  intro u hut
  have htval : individualizedColouring n T t = t.val + 1 := by
    simp [individualizedColouring, ht]
  rw [htval]
  by_cases hu : u ∈ T
  · have : individualizedColouring n T u = u.val + 1 := by simp [individualizedColouring, hu]
    rw [this]
    intro h
    exact hut (Fin.val_injective (by omega))
  · have : individualizedColouring n T u = 0 := by simp [individualizedColouring, hu]
    rw [this]; omega

/-- **The depth-1 discreteness producer (general).** If the joint profile `(relOfPair t ·)_{t ∈ T}` is
injective — `∀ u u', (∀ t ∈ T, relOfPair t u = relOfPair t u') → u = u'` — then `warmRefine (schemeAdj S)`
from `T` is `Discrete`. Cells refine the joint profile: a same-cell pair off `T` agrees on each `relOfPair t ·`
(via `warmRefine_refines_initial` to the single base `{t}` + `relOfPair_eq_of_warmRefine_singleton`), and a
pair meeting `T` collapses by singleton preservation. Feeds `stablyRecoverable_of_discrete`. -/
theorem discrete_of_jointProfileSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (hsep : ∀ u u' : Fin n, (∀ t ∈ T, S.relOfPair t u = S.relOfPair t u') → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  classical
  have hsingle : ∀ t ∈ T, ∀ x : Fin n,
      warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) x
        = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) t → x = t := by
    intro t ht x hx
    by_contra hxt
    exact iterate_refineStep_preserves_singleton (schemeAdj S) (fun _ _ => POE.unknown) t n
      (individualizedColouring n T) (individualizedColouring_mem_sep ht) x hxt hx
  intro u u' hcell
  by_cases hu : u ∈ T
  · exact (hsingle u hu u' hcell.symm).symm
  · by_cases hu' : u' ∈ T
    · exact hsingle u' hu' u hcell
    · apply hsep
      intro t ht
      have htu : u ≠ t := fun h => hu (h ▸ ht)
      have htu' : u' ≠ t := fun h => hu' (h ▸ ht)
      have href : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n {t}) u
          = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n {t}) u' :=
        warmRefine_refines_initial
          (individualizedColouring_refines (Finset.singleton_subset_iff.mpr ht)) u u' hcell
      exact relOfPair_eq_of_warmRefine_singleton S htu htu' href

/-- **The depth-1 separability predicate (`s(C) = 1`) — a NAMED SPECIAL CASE of the open self-detection, not
the whole thing.** A scheme is *depth-1 separable at depth `bound`* when some base set `T` of size `≤ bound`
has an **injective depth-1 joint profile**: `(relOfPair t ·)_{t∈T}` separates all vertices. This is *strictly
stronger* than what `SelfDetectsStably` needs (it demands separation after a *single* refinement round from
`T`, i.e. `s(C) = 1`), so it is a **sufficient condition** covering the separable / depth-1-recoverable
primitives (most of the catalogue/affine probe's primitives), **not** the `s(C) ≥ 2` cases.

> **⚠️ THIS IS NOT THE CLOSED CRUX — where the engine slots in.** The genuinely open self-detection content is
> the `s(C) ≥ 2` regime (cyclotomic, recovering only at depth `base + O(1)` via *iterated* joint-profile
> separation). The intended next step is a **`selfDetectsStably_of_boundedDepthSeparable`** sitting *beside*
> `selfDetectsStably_of_depthOneSeparable` below, keyed on a weaker *bounded-depth* (iterated) separation
> predicate, produced by a `schemeAdj`-level iterated-profile engine (the analogue of the
> `isolationStep`/`EdgeGenerates` closure machinery, which today exists only for the `J`-binarized graph). That
> engine — not this predicate — is the open infrastructure. See `docs/chain-descent-self-detection-plan.md` §9.3
> (M2-B) for the build plan.

> **Bound non-vacuity (the `recoverableByDepth_univ` hinge).** `DepthOneSeparable S n` is *trivially true*
> (`T = univ`: for `t = u`, `relOfPair u u = 0 = relOfPair u u'` forces `u' = u`). So all content lives in the
> **small bound** (`base + 0`); the predicate is only meaningful at `bound ≪ n`, exactly like `RecoverableByDepth`. -/
def DepthOneSeparable {n : Nat} (S : AssociationScheme n) (bound : Nat) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ bound ∧
    ∀ u u' : Fin n, (∀ t ∈ T, S.relOfPair t u = S.relOfPair t u') → u = u'

/-- **Depth-1 separability ⟹ self-detection (the slot).** A primitive small residual that is depth-1 separable
self-detects stably. This is the depth-1 (`s(C) = 1`) route into `SelfDetectsStably`; the open engine will add a
sibling `…_of_boundedDepthSeparable` for `s(C) ≥ 2`, **not** replace the seal. Via
`discrete_of_jointProfileSeparates` (the joint profile separates ⟹ `warmRefine` discrete) +
`selfDetectsStably_of_discretizes`. -/
theorem selfDetectsStably_of_depthOneSeparable {n : Nat} (S : SchurianScheme n) (IsLarge : Nat → Prop)
    (bound : Nat)
    (h : S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
        DepthOneSeparable S.toAssociationScheme bound) :
    SelfDetectsStably S IsLarge bound := by
  apply selfDetectsStably_of_discretizes
  intro hps
  obtain ⟨T, hcard, hsep⟩ := h hps
  exact ⟨T, hcard, discrete_of_jointProfileSeparates S.toAssociationScheme hsep⟩

/-- **The seal capstone, depth-graded (G1a).** `reachesRigidOrCameron_viaRecovery` with the rigid side widened
from per-level `SchemeRecovered` to `SchemeRecoveredByDepth … bound`: every rank-≥3 schurian scheme residual is
*recovered by bounded depth* or is a Cameron section. Each non-Cameron branch may now discharge via a
depth-graded harvest (CFI at `tw`, Shrikhande at 2), where the per-level capstone required depth-1 visibility.
The carried content is the same `s(C)` leak (G2) plus the localisation (the shallow ∅→S₀ coverage inside
`SchemeRecoveredByDepth`); subsumes `reachesRigidOrCameron_viaRecovery` via
`schemeRecoveredByDepth_of_schemeRecovered`. -/
theorem reachesRigidOrCameron_viaDepthRecovery {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : ¬ IsLargeSchemeViaAut IsLarge n S → SchemeRecoveredByDepth n S bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive → SchemeRecoveredByDepth n S bound) :
    SchemeRecoveredByDepth n S bound ∨ IsCameronScheme n S :=
  reachesRigidOrCameron (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := fun m S => SchemeRecoveredByDepth m S bound)
    hClassify (fun _ _ h => h) S hne hrank hCascade hImprim

/-- **The depth-recovery seal capstone, primitive-floor form (self-detection-ready).** Identical to
`reachesRigidOrCameron_viaDepthRecovery` but the cascade obligation is sharpened to carry `IsPrimitive`:
`hCascade : IsPrimitive ∧ ¬ IsLargeSchemeViaAut → SchemeRecoveredByDepth`. So `hCascade` is *exactly* the
self-detection lemma (a primitive, small residual recovers at bounded depth), and the imprimitive branch
stays on the landed block recovery. Wires `reachesRigidOrCameron'`. -/
theorem reachesRigidOrCameron_viaDepthRecovery' {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
        SchemeRecoveredByDepth n S bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive → SchemeRecoveredByDepth n S bound) :
    SchemeRecoveredByDepth n S bound ∨ IsCameronScheme n S :=
  reachesRigidOrCameron' (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := fun m S => SchemeRecoveredByDepth m S bound)
    hClassify (fun _ _ h => h) S hne hrank hCascade hImprim

/-- **The self-detection proposition** — the single open content of the seal's cascade branch, named. A
schurian scheme residual **self-detects at depth `bound`** when, *if it is primitive and small*
(`¬ IsLargeSchemeViaAut`), it recovers at bounded depth (`SchemeRecoveredByDepth … bound`). This is the
primitive-floor `hCascade` of `reachesRigidOrCameron_viaDepthRecovery'`, isolated as a predicate: the seal
closes (modulo the cited classification + the landed imprimitive block recovery) exactly when this holds.
Non-vacuous: `SchemeRecoveredByDepth` is keyed on visible (refinement-computable) realizers + a bounded
shallow phase, *false* for a high-`s(C)` non-recovering scheme (seal-handoff §3). The conjecture that this
holds for all primitive small residuals (at `bound = base + O(1)`) is the self-detection lemma; the catalogue
falsifier (`CatalogueSchemeProbe.cs`) tests its emptiness empirically. -/
def SelfDetectsAtDepth {n : Nat} (S : SchurianScheme n) (IsLarge : Nat → Prop) (bound : Nat) : Prop :=
  S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
    SchemeRecoveredByDepth n S bound

/-- **The seal, reduced to self-detection.** Given the cited classification (G3), the **self-detection**
proposition for the primitive floor (`SelfDetectsAtDepth`, the cascade branch), and the landed **imprimitive
block recovery** (`hImprim`, G2-A), every rank-≥3 schurian scheme residual is `SchemeRecoveredByDepth ∨
Cameron`. This is the seal with its *entire* open content concentrated into the single hypothesis
`SelfDetectsAtDepth` — the self-detection lemma — with `IsPrimitive` honestly carried into the cascade branch.
Proving `SelfDetectsAtDepth` for all primitive small residuals makes the seal unconditional modulo only G3. -/
theorem reachesRigidOrCameron_viaSelfDetection {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hSelfDetect : SelfDetectsAtDepth S IsLarge bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive → SchemeRecoveredByDepth n S bound) :
    SchemeRecoveredByDepth n S bound ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaDepthRecovery' hClassify S hne hrank hSelfDetect hImprim

/-- **Semantic self-detection ⟹ the seal's self-detection obligation.** `SelfDetectsStably ⟹ SelfDetectsAtDepth`,
via `schemeRecoveredByDepth_of_stablyRecoverable`. So the seal's entire open content can be discharged from the
clean *semantic* recovery predicate (cells = orbits above a bounded set), which is what Phase 2 attacks. -/
theorem selfDetectsAtDepth_of_selfDetectsStably {n : Nat} {S : SchurianScheme n}
    {IsLarge : Nat → Prop} {bound : Nat} (h : SelfDetectsStably S IsLarge bound) :
    SelfDetectsAtDepth S IsLarge bound := by
  intro hps
  obtain ⟨S₀, hcard, hstab⟩ := h hps
  exact schemeRecoveredByDepth_of_stablyRecoverable S hcard hstab

/-- **The seal, reduced to SEMANTIC self-detection (Increment 2 capstone).** The seal with its entire open
content concentrated into `SelfDetectsStably` — *primitive small residuals recover stably above a bounded set*
(cells = orbits above `base + O(1)`). This is the form the affine module-theory argument (Phase 2 §5.1)
produces and the catalogue probe measures: the crux is now a statement about `CellsAreOrbits` (separability),
not the harvest-witness `SchemeRecoveredByDepth`. Imprimitive branch on landed block recovery; modulo only the
cited G3. -/
theorem reachesRigidOrCameron_viaStableRecovery {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hSelfDetect : SelfDetectsStably S IsLarge bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive → SchemeRecoveredByDepth n S bound) :
    SchemeRecoveredByDepth n S bound ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaSelfDetection hClassify S hne hrank
    (selfDetectsAtDepth_of_selfDetectsStably hSelfDetect) hImprim

/-! ### The scheme-seal wiring — the imprimitive branch folded into the visible block decomposition

The seal capstones above carry the imprimitive branch as an opaque `hImprim : ¬IsPrimitive → ReachesRigid`. This
section **folds it into the (now fully visible) block decomposition**: an imprimitive scheme has a non-trivial block
system `β_I` (`exists_nontrivial_closedSubset_of_not_isPrimitive`), and `reachesRigid_of_blockVisibleDecomposition`
reproduces the group from refinement-computable quotient (`hreach_of_quotientVisibleRealizers`) + fiber
(`hfiber_of_fiberVisibleRealizers`) recovery on `β_I`. So the imprimitive branch's "rigid" target becomes
`SchemeBlockRecovered` — block-visible recovery — which is *earned* (group reproduced), not opaque.

**Non-vacuity (the key check).** `SchemeBlockRecovered` keys `β` on a genuine `ClosedSubset` block system, so a
**primitive** scheme has only the *trivial* closed subsets (`{0}` ⟹ `β` = singletons ⟹ the quotient clause is full
visible recovery; `univ` ⟹ `β` = one block ⟹ the fiber clause is full visible recovery). Either way it collapses to
full recovery, which is **false for a non-recovering primitive scheme (G2-B)** — so the predicate is genuinely false
there, not vacuously true. For imprimitive schemes the non-trivial `β_I` lets it hold via genuine block recovery
(quotient + fiber on the smaller constituents). It subsumes leg A (`SchemeRecovered`) as the `β` = singletons
(`I = {0}`) case. The residual carried content collapses to `hCascade` (the small-primitive branch = **G2-B**, the
irreducible leak) + the cited classification (G3). -/

/-- **Block-visible recovery — the imprimitive branch's earned rigid predicate.** `S` is *block-recovered* when, for
some `ClosedSubset I` block system `β_I v := {y | schemeEquiv I v y}`, there is a harvested `gens` (path-fixing) and
a base `bs` with **refinement-computable** quotient coverage (every same-`warmRefine`-cell pair has a `gens`-realizer
landing `b` in the *block* of `w`) and fiber coverage (every same-cell *same-block* pair has an exact `gens`-realizer).
Non-vacuous: keying `β` on a `ClosedSubset` forces a *primitive* scheme to trivial `β` = full recovery, false on the
G2-B leak (see section note). The imprimitive seal leg's rigid target, *earned* via
`reachesRigid_of_blockVisibleDecomposition`. -/
def SchemeBlockRecovered : ∀ (m : Nat), SchurianScheme m → Prop :=
  fun m S => ∃ (I : Finset (Fin (S.rank + 1))) (gens : Set (Equiv.Perm (Fin m)))
      (bs : List (Fin m)),
    S.toAssociationScheme.ClosedSubset I ∧
    (∀ g ∈ gens, g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
    (∀ T : Finset (Fin m), ∀ b w : Fin m,
        warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) b
            = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) w →
        ∃ σ, σ ∈ gens
          ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T σ
          ∧ {y | S.toAssociationScheme.schemeEquiv I (σ b) y}
              = {y | S.toAssociationScheme.schemeEquiv I w y}) ∧
    (∀ T : Finset (Fin m), ∀ u w : Fin m,
        {y | S.toAssociationScheme.schemeEquiv I u y} = {y | S.toAssociationScheme.schemeEquiv I w y} →
        warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) u
            = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
              (individualizedColouring m T) w →
        ∃ g, g ∈ gens
          ∧ ResidualAut (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T g ∧ g u = w) ∧
    IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
      (bs.foldl (fun s b => insert b s) ∅)

/-- **Block-visible recovery ⟹ the group is reproduced (earned).** From `SchemeBlockRecovered`, the harvested `gens`
generate exactly `SchemeAutGroup S`, via `reachesRigid_of_blockVisibleDecomposition` on the block system
`β_I = fun v => {y | schemeEquiv I v y}` (quotient + fiber, both visible) + the `schemeAdj` bridge
(`gensAt_empty_eq` + `stabilizerAt_schemeAdj_empty_eq`). The imprimitive analogue of
`schemeAutGroup_eq_closure_of_recovered`: the content earned from refinement-computable block recovery, no
sub-scheme materialized. -/
theorem schemeAutGroup_eq_closure_of_blockRecovered {n : Nat} {S : SchurianScheme n}
    (h : SchemeBlockRecovered n S) :
    ∃ gens : Set (Equiv.Perm (Fin n)),
      Subgroup.closure gens = S.toAssociationScheme.SchemeAutGroup := by
  obtain ⟨I, gens, bs, _hcl, hsound, hqvis, hfvis, hbase⟩ := h
  refine ⟨gens, ?_⟩
  have hr := reachesRigid_of_blockVisibleDecomposition
    (β := fun v => {y | S.toAssociationScheme.schemeEquiv I v y}) bs ∅ hqvis hfvis hbase
  rw [gensAt_empty_eq hsound] at hr
  exact hr.trans (stabilizerAt_schemeAdj_empty_eq S)

/-- **The seal capstone with the imprimitive branch folded into block recovery (the scheme-seal wiring).** Widens
`reachesRigidOrCameron_viaRecoveryOrAbelian` so the rigid side is `SchemeBlockRecovered ∨ AbelianConsumed`: every
rank-≥3 schurian scheme residual is **block-recovered or hidden-abelian-consumed or Cameron**. The imprimitive branch
no longer carries an opaque "imprimitive ⟹ recovered" — its target is now `SchemeBlockRecovered`, *earned* from the
fully-visible block decomposition (`reachesRigid_of_blockVisibleDecomposition`), so the carried content for it is the
refinement-computable quotient + fiber recovery on the block system (non-vacuous, recurses to the smaller
constituents). The **sole irreducible carried content** is then `hCascade` — the small-**primitive** branch =
**G2-B** (the open `s(C)` leak: primitive non-abelian non-recovering, uncitable per the deep-research pass) — plus the
cited classification (G3). This is the honest end-state: a conditional seal `modulo {G3 + G2-B}`. -/
theorem reachesRigidOrCameron_viaBlockRecovery {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hCascade : ¬ IsLargeSchemeViaAut IsLarge n S → SchemeBlockRecovered n S ∨ AbelianConsumed n S)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive → SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    (SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ IsCameronScheme n S :=
  reachesRigidOrCameron (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := fun m S => SchemeBlockRecovered m S ∨ AbelianConsumed m S)
    hClassify (fun _ _ h => h) S hne hrank hCascade hImprim

/-- **THE FUSED SEAL — the single headline capstone.** Combines the *best* predicate for each branch into one
statement, fusing `reachesRigidOrCameron_viaStableRecovery` (which reduced the cascade branch to the semantic
crux but carried the imprimitive branch opaquely) with `reachesRigidOrCameron_viaBlockRecovery` (which earned the
imprimitive branch but keyed the cascade branch on block recovery, not self-detection). Every rank-≥3 schurian
scheme residual is

  `((SchemeBlockRecovered ∨ AbelianConsumed) ∨ SchemeRecoveredByDepth bound) ∨ IsCameronScheme`,

with each non-Cameron branch discharged through its **strongest landed/earned form**:
* **primitive floor** (the cascade branch, `IsPrimitive ∧ ¬IsLarge`): reduced to the **semantic** crux
  `SelfDetectsStably` via `selfDetectsAtDepth_of_selfDetectsStably` → `SchemeRecoveredByDepth`. This is the
  genuinely-irreducible **G2-B** core (small primitive non-abelian non-recovering, uncitable), now keyed on
  `CellsAreOrbits`-separability — the object Phase 2 (the affine module argument) produces and the catalogue
  probe measures.
* **imprimitive branch** (`¬IsPrimitive`): the carried `hImprim`, on the *earned* `SchemeBlockRecovered`
  (block-visible quotient + fiber recovery) ∨ `AbelianConsumed` (leg B, hidden-abelian circulants). Reduces via
  the imprimitivity block tower (≤ log₂ n layers) to the same primitive floor.
* **Cameron** (leg C): the cited Babai/Sun–Wilmes classification `hClassify` (G3).

**Honest accounting (do not overclaim).** The theorem carries **two** inputs: `hSelfDetect` (the crux = G2-B)
and `hImprim` (landed/earned predicates, tower-reducible to the same floor), plus cited G3. The value is
*concentration*: a single object in which the open content is the semantic self-detection proposition, every
other branch rests on a landed or earned predicate, and the conditional seal `modulo {G3 + self-detection}` is
one statement rather than two partial capstones. It subsumes `reachesRigidOrCameron_viaStableRecovery` (the
`SchemeRecoveredByDepth` disjunct) and `reachesRigidOrCameron_viaBlockRecovery` (the
`SchemeBlockRecovered ∨ AbelianConsumed` disjunct). Wires the primitivity-carrying `reachesRigidOrCameron'`. -/
theorem reachesRigidOrCameron_viaFusedSeal {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hSelfDetect : SelfDetectsStably S IsLarge bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S :=
  reachesRigidOrCameron' (NonCascade := IsLargeSchemeViaAut IsLarge)
    (ReachesRigid := fun m S' =>
      (SchemeBlockRecovered m S' ∨ AbelianConsumed m S') ∨ SchemeRecoveredByDepth m S' bound)
    hClassify (fun _ _ h => h) S hne hrank
    (fun h => Or.inr (selfDetectsAtDepth_of_selfDetectsStably hSelfDetect h))
    (fun h => Or.inl (hImprim h))

/-- **The seal closed for the depth-1-separable (`s(C) = 1`) slice — A CONDITIONAL CAPSTONE, NOT THE CLOSED
SEAL.** Specializes the fused seal by discharging its self-detection input via depth-1 separability
(`selfDetectsStably_of_depthOneSeparable`). It **still carries** three hypotheses — the cited classification
`hClassify` (G3), the imprimitive block recovery `hImprim`, and **`hDepthOne`** (depth-1 separability) — so it
is manifestly conditional.

> **⚠️ SCOPE — this closes the seal ONLY for the depth-1-separable class.** `hDepthOne` is *false* for `s(C) ≥ 2`
> residuals (cyclotomic and friends, which recover only at depth `base + O(1)` via iterated separation). Closing
> those is the open self-detection content; the engine slots in beside `selfDetectsStably_of_depthOneSeparable`
> as a bounded-depth (iterated) producer of `SelfDetectsStably`, after which a sibling
> `reachesRigidOrCameron_viaBoundedDepthSeparable` would carry the weaker hypothesis. Do **not** read this as
> "the seal is closed for primitives." -/
theorem reachesRigidOrCameron_viaDepthOneSeparable {n : Nat} {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    (hDepthOne : S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
        DepthOneSeparable S.toAssociationScheme bound)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaFusedSeal hClassify S hne hrank
    (selfDetectsStably_of_depthOneSeparable S IsLarge bound hDepthOne) hImprim

/-! ### §13b — the two-round (depth-2) separation engine on `schemeAdj` (E1)

`relOfPair_eq_of_warmRefine_singleton` (§13a) is the **depth-1** separation primitive: a `warmRefine`
cell refines the depth-1 `relOfPair` profile, and from a *single* base that already recovers
(`cellsAreOrbits_schemeAdj_singleton`). For the `s(C) ≥ 2` regime (cyclotomic and friends) one round is
insufficient — the depth-1 *joint* profile of a small base is a coset twin — and from a single base depth-2
counts collapse to intersection numbers (`AssociationScheme.intersectionCount_via_w`), adding nothing. The
genuine content is therefore inherently **multi-base, two-round**: this subsection lands the reusable
two-round count primitive, the `schemeAdj` analogue of the intersection-number separation
(`IntersectionSeparates`/`depth2Det`). It generalises the single-base depth-`k` count machinery
(`iter_succ_count_eq` &c. in `Scheme.lean`, keyed on `individualizedColouring n {v}`) to an arbitrary base
**set** `T`, keyed on the public `signature_eq_card_eq`. It is the brick the affine-cyclic bound proof (and
any future primitive-floor slice) consumes; the conversion from the one-round colour grouping to the joint
`(relOfPair t ·)_{t∈T}` profile is the consumer's job (`relOfPair_eq_of_warmRefine_singleton`, depth-1). -/

/-- **Two-round count separation (the depth-2 primitive, E1).** For `w, u` in the same
`warmRefine (schemeAdj S)`-cell after individualizing a base set `T`, the **depth-2 count profile**
coincides: for every one-round colour `c` (`refineStep` of the individualised colouring) and every relation
`b`, the number of `z ≠ w` whose one-round colour is `c` and `relOfPair w z = b` equals the corresponding
count for `u`. Mechanism: peel `warmRefine = refineStep^[n]` to `refineStep^[2]` (`warmRefine_eq_iter_eq`),
read off `signature`-equality at the one-round colouring (`refineStep_iff`), and apply the count bridge
(`signature_eq_card_eq`). The one-round colour `c` refines the joint `(relOfPair t ·)_{t∈T}` profile
(depth-1, §13a), so grouping by `c` is finer than grouping by the relations-to-`T` — that conversion is the
consumer's job. -/
theorem twoRoundCount_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (c : Nat) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  by_cases hn : 2 ≤ n
  · -- peel `warmRefine = refineStep^[n]` to `refineStep^[2]`, read `signature` at `refineStep χ`
    have h2 : ((refineStep adj P)^[2]) χ w = ((refineStep adj P)^[2]) χ u :=
      warmRefine_eq_iter_eq adj P χ 2 hn h
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one] at h2
    have hsig : signature adj P (refineStep adj P χ) w = signature adj P (refineStep adj P χ) u :=
      ((refineStep_iff adj P (refineStep adj P χ) w u).mp h2).2
    have hcard := signature_eq_card_eq adj P (refineStep adj P χ) hsig (c, b.val, POE.unknown)
    -- the two filter predicates coincide (P is always `unknown`; `adj` reads `relOfPair`)
    have hpred : ∀ x : Fin n, ∀ z : Fin n,
        (z ≠ x ∧ refineStep adj P χ z = c ∧ S.relOfPair x z = b)
          ↔ (z ≠ x ∧ (c, b.val, POE.unknown) = (refineStep adj P χ z, adj.adj x z, P x z)) := by
      intro x z
      refine and_congr_right (fun _ => ?_)
      have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
      have hPval : P x z = POE.unknown := rfl
      rw [hadjval, hPval, Prod.mk.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hcz, hbz⟩; exact ⟨hcz.symm, by rw [hbz], rfl⟩
      · rintro ⟨hc, hb, -⟩; exact ⟨hc.symm, (Fin.val_injective hb).symm⟩
    rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
    exact hcard
  · -- `n ≤ 1`: `Fin n` is subsingleton, `w = u`, the two filters coincide
    have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    rw [Subsingleton.elim w u]

/-- **The depth-2 discreteness producer (E1).** If the depth-2 count profile — for every one-round colour
`c` and relation `b`, the number of `z` at one-round colour `c` with `relOfPair · z = b` — separates all
vertices, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. The depth-2 analogue of
`discrete_of_jointProfileSeparates` (which keys on the *depth-1* joint profile, insufficient for `s(C) ≥ 2`):
same-cell vertices share the depth-2 profile (`twoRoundCount_eq_of_warmRefine`), so an injective profile
forces singletons. Composes with `stablyRecoverable_of_discrete` → `selfDetectsStably_of_discretizes`, so a
bounded base `T` with a separating depth-2 profile closes the seal on that family. This is the producer the
affine-cyclic (`s(C) ≥ 2`) bound proof discharges (exhibit such a `T` of size `base + O(1)`). -/
theorem discrete_of_twoRoundProfileSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (hsep : ∀ u u' : Fin n,
        (∀ (c : Nat) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
            S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
            S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun c b => twoRoundCount_eq_of_warmRefine S hcell c b)

/-- **Lemma A — the one-round colour determines the relation to each base point (the colour→relation
bridge).** If `z, z'` share their one-round colour `refineStep (schemeAdj S) … (individualizedColouring n T)`,
then for every `t ∈ T`, `relOfPair t z = relOfPair t z'`. So the one-round colour *refines* the joint profile
`(relOfPair t ·)_{t∈T}` — the missing link to re-group the depth-2 counts of
`twoRoundCount_eq_of_warmRefine` by relation rather than by the opaque colour. Mirrors
`relOfPair_eq_of_warmRefine_singleton`'s isolation argument, but at **one** `refineStep` round and a base
**set** `T`: the individualized `t ∈ T` carries a unique colour (`individualizedColouring_mem_sep`), so its
signature tuple is isolated, forcing `adj z t = adj z' t` i.e. `relOfPair z t = relOfPair z' t`. -/
theorem relOfPair_eq_of_refineStep_base {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {t : Fin n} (ht : t ∈ T) {z z' : Fin n}
    (h : refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z
       = refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z') :
    S.relOfPair t z = S.relOfPair t z' := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  have hcol : individualizedColouring n T z = individualizedColouring n T z' :=
    ((refineStep_iff adj P (individualizedColouring n T) z z').mp h).1
  have hsig : signature adj P (individualizedColouring n T) z
            = signature adj P (individualizedColouring n T) z' :=
    ((refineStep_iff adj P (individualizedColouring n T) z z').mp h).2
  have hχt : individualizedColouring n T t = t.val + 1 := by simp [individualizedColouring, ht]
  have hχ_eq_t : ∀ x : Fin n, individualizedColouring n T x = t.val + 1 → x = t := by
    intro x hx
    by_contra hxt
    exact (individualizedColouring_mem_sep ht x hxt) (hx.trans hχt.symm)
  by_cases hzt : z = t
  · have hz' : z' = t := hχ_eq_t z' (by rw [← hcol, hzt, hχt])
    rw [hzt, hz']
  · by_cases hz't : z' = t
    · exact absurd (hχ_eq_t z (by rw [hcol, hz't, hχt])) hzt
    · have hcard := signature_eq_card_eq adj P (individualizedColouring n T) hsig
        (individualizedColouring n T t, adj.adj z t, P z t)
      have hFz : (Finset.univ.filter (fun u' : Fin n => u' ≠ z ∧
          (individualizedColouring n T t, adj.adj z t, P z t)
            = (individualizedColouring n T u', adj.adj z u', P z u'))) = {t} := by
        apply Finset.ext; intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩; exact hχ_eq_t x ((congrArg Prod.fst heq).symm.trans hχt)
        · rintro rfl; exact ⟨Ne.symm hzt, rfl⟩
      rw [hFz, Finset.card_singleton] at hcard
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (hcard ▸ Nat.one_pos)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, hxeq⟩ := hx
      have hxt : x = t := hχ_eq_t x ((congrArg Prod.fst hxeq).symm.trans hχt)
      have hval : adj.adj z t = adj.adj z' t := by
        have hv := congrArg (fun p : Nat × Nat × POE => p.2.1) hxeq
        rwa [hxt] at hv
      have hrel : S.relOfPair z t = S.relOfPair z' t := Fin.val_injective hval
      rw [S.relOfPair_symm t z, S.relOfPair_symm t z']; exact hrel

/-- **Two-round count, aggregate (countP) form (E1).** The predicate-indexed generalization of
`twoRoundCount_eq_of_warmRefine`: for `w, u` in the same `warmRefine`-from-`T` cell, every count of `z`
whose one-round colour satisfies a predicate `q` and whose relation to the base point is `b` agrees between
`w` and `u`. Same peel-and-count proof but via the aggregate `signature_eq_countP_eq`. This lets the colour
grouping be re-expressed by *any* colour predicate — the vehicle for the colour→relation conversion. -/
theorem twoRoundCountP_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (q : Nat → Prop) [DecidablePred q] (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z) ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z) ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  by_cases hn : 2 ≤ n
  · have h2 : ((refineStep adj P)^[2]) χ w = ((refineStep adj P)^[2]) χ u :=
      warmRefine_eq_iter_eq adj P χ 2 hn h
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one] at h2
    have hsig : signature adj P (refineStep adj P χ) w = signature adj P (refineStep adj P χ) u :=
      ((refineStep_iff adj P (refineStep adj P χ) w u).mp h2).2
    have hcard := signature_eq_countP_eq adj P (refineStep adj P χ) hsig
      (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
    have hpred : ∀ x : Fin n, ∀ z : Fin n,
        (z ≠ x ∧ q (refineStep adj P χ z) ∧ S.relOfPair x z = b)
          ↔ (z ≠ x ∧ (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
                (refineStep adj P χ z, adj.adj x z, P x z)) := by
      intro x z
      refine and_congr_right (fun _ => ?_)
      show (q (refineStep adj P χ z) ∧ S.relOfPair x z = b)
        ↔ (q (refineStep adj P χ z) ∧ adj.adj x z = b.val)
      have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
      rw [hadjval]
      exact and_congr_right (fun _ => Fin.ext_iff)
    rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
    exact hcard
  · have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    rw [Subsingleton.elim w u]

/-- **Two-round count, joint-relation form (E1 — the colour→relation conversion, the payoff).** Re-groups
`twoRoundCount` by the **joint relation profile** `(relOfPair t z)_{t∈T}` instead of the opaque one-round
colour: for `w, u` in the same `warmRefine`-from-`T` cell, every count of `z` whose relations to all base
points match a target profile `ρ` and whose relation `relOfPair · z = b` agrees between `w` and `u`. Combines
`twoRoundCountP_eq_of_warmRefine` (aggregate) with `relOfPair_eq_of_refineStep_base` (Lemma A: the one-round
colour determines the joint profile), so the colour predicate `q c := ∃ z₀, colour z₀ = c ∧ profile z₀ = ρ`
reads exactly as the profile condition. **This is the relation-indexed depth-2 count the Frobenius / affine
separability argument consumes** — the object `relOfPair`/`G₀`-orbit counting lives in, not opaque colours. -/
theorem twoRoundProfileCount_eq {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card := by
  classical
  set q : Nat → Prop := fun c => ∃ z₀ : Fin n,
    refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z₀ = c
      ∧ ∀ t ∈ T, S.relOfPair t z₀ = ρ t with hq_def
  have hq : ∀ z : Fin n,
      q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
        ↔ ∀ t ∈ T, S.relOfPair t z = ρ t := by
    intro z
    constructor
    · rintro ⟨z₀, hz₀, hprof⟩ t ht
      exact (relOfPair_eq_of_refineStep_base S ht hz₀).symm.trans (hprof t ht)
    · intro hprof; exact ⟨z, rfl, hprof⟩
  rw [show (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
            ∧ S.relOfPair w z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z]),
    show (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
            ∧ S.relOfPair u z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z])]
  exact twoRoundCountP_eq_of_warmRefine S h q b

/-- **The relation-indexed depth-2 discreteness producer (E1 — the conversion complete).** If the joint
relation-profile counts separate all vertices — for every target profile `ρ` and relation `b`, equal counts
of `z` matching `(relOfPair t z = ρ t)_{t∈T}` together with `relOfPair · z = b` force the two vertices equal
— then `warmRefine (schemeAdj S)` from `T` is `Discrete`. The relation-form analogue of
`discrete_of_twoRoundProfileSeparates` (which keyed on the opaque one-round colour), via
`twoRoundProfileCount_eq`. **This is the producer the Frobenius / affine `s(C)` bound discharges**: exhibit a
bounded `T` whose joint relation-profile counts separate (the Galois-breaking base), then this gives
discreteness, feeding `stablyRecoverable_of_discrete` → `selfDetectsStably_of_discretizes` →
`reachesRigidOrCameron_viaAffineIrreducible`. On `affineScheme`, the `relOfPair`/profile conditions are
`G₀`-orbit-of-difference conditions (`affineScheme_relOfPair_eq_iff`/`orbMk_affine_eq_iff`), so the consumer
runs the Frobenius counting natively without a bespoke affine producer. -/
theorem discrete_of_twoRoundRelationSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (hsep : ∀ u u' : Fin n,
        (∀ (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun ρ b => twoRoundProfileCount_eq S hcell ρ b)

/-! ### Phase 2, M0.3 — the affine instance `V ⋊ G₀` over `F_p^d`

The concrete beachhead family: the orbital scheme of the affine group `V ⋊ G₀` acting on `V = F_p^d`,
built by instantiating the general `orbitalScheme` (M0) at the subgroup of `Perm (Fin (p^d))` generated
by the affine permutations `x ↦ g₀ x + t` (`g₀ ∈ G₀`, `t ∈ V`), transported along `V ≃ Fin (p^d)`.

**Generalization note (the reusable shape).** The construction uses only: a *regular abelian* group of
translations (giving transitivity) and a point-stabilizer `G₀` *closed under negation* (giving the
symmetric/generous-transitivity hypothesis — `LinearEquiv.neg ∈ G₀`). Nothing here is special to
`F_p^d` beyond `V` being a finite module; the same shape models any **translation scheme** (`T ⋊ G₀`,
`T` regular abelian — the Schur-ring setting of M2). The linear structure of `V` only enters later, at
M1 (block ⟺ `G₀`-invariant subspace) and M2 (irreducible `G₀` ⟹ recovery). -/

section AffineScheme

variable {p d : ℕ} [Fact p.Prime]

/-- `card (F_p^d) = p^d`. -/
private theorem affV_card : Fintype.card (Fin d → ZMod p) = p ^ d := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The transport `F_p^d ≃ Fin (p^d)` (the scheme lives on `Fin (p^d)`). -/
noncomputable def affineE : (Fin d → ZMod p) ≃ Fin (p ^ d) :=
  Fintype.equivFinOfCardEq affV_card

/-- The affine permutation `x ↦ g₀ x + t` of `V = F_p^d`. -/
def affineEquivV (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (t : Fin d → ZMod p) :
    Equiv.Perm (Fin d → ZMod p) where
  toFun := fun x => g₀ x + t
  invFun := fun y => g₀.symm (y - t)
  left_inv := fun x => by simp
  right_inv := fun y => by simp

/-- The affine permutation transported to `Perm (Fin (p^d))`. -/
noncomputable def affinePermFin (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) : Equiv.Perm (Fin (p ^ d)) :=
  affineE.permCongr (affineEquivV g₀ t)

@[simp] theorem affinePermFin_apply (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) (i : Fin (p ^ d)) :
    affinePermFin g₀ t i = affineE (g₀ (affineE.symm i) + t) := by
  simp only [affinePermFin, Equiv.permCongr_apply, affineEquivV, Equiv.coe_fn_mk]

/-- The identity is the trivial affine perm. -/
theorem affinePermFin_one :
    affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (0 : Fin d → ZMod p) = 1 := by
  ext i; simp [affinePermFin_apply, LinearEquiv.coe_one]

/-- **Affine perms compose to affine perms** (`x ↦ g₀x+t` ∘ `x ↦ h₀x+s` = `x ↦ (g₀h₀)x + (g₀s+t)`). -/
theorem affinePermFin_mul (g₀ h₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t s : Fin d → ZMod p) :
    affinePermFin g₀ t * affinePermFin h₀ s = affinePermFin (g₀ * h₀) (g₀ s + t) := by
  ext i
  simp only [Equiv.Perm.mul_apply, affinePermFin_apply, Equiv.symm_apply_apply,
    LinearEquiv.mul_apply, map_add]
  congr 1; abel

/-- The inverse of an affine perm is affine. -/
theorem affinePermFin_inv (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) :
    (affinePermFin g₀ t)⁻¹ = affinePermFin g₀⁻¹ (-(g₀⁻¹ t)) := by
  have h : affinePermFin g₀⁻¹ (-(g₀⁻¹ t)) * affinePermFin g₀ t = 1 := by
    rw [affinePermFin_mul, inv_mul_cancel, add_neg_cancel, affinePermFin_one]
  exact inv_eq_of_mul_eq_one_left h

variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- The affine permutations whose linear part lies in `G₀` — the generating set of `V ⋊ G₀`. -/
def affineGenSet : Set (Equiv.Perm (Fin (p ^ d))) :=
  { σ | ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p), g₀ ∈ G₀ ∧ ∃ t, σ = affinePermFin g₀ t }

/-- **The affine group `V ⋊ G₀`** as a subgroup of `Perm (Fin (p^d))`. Defined as the carrier set of
affine perms (closed under product/inverse/identity by `affinePermFin_mul`/`_inv`/`_one`), so membership
is *transparently* "is an affine perm with linear part in `G₀`" — what the orbital characterization (M1.0b)
needs. -/
noncomputable def affineG : Subgroup (Equiv.Perm (Fin (p ^ d))) where
  carrier := affineGenSet G₀
  mul_mem' := by
    rintro a b ⟨g₀, hg₀, t, rfl⟩ ⟨h₀, hh₀, s, rfl⟩
    exact ⟨g₀ * h₀, mul_mem hg₀ hh₀, g₀ s + t, affinePermFin_mul g₀ h₀ t s⟩
  one_mem' := ⟨1, one_mem _, 0, affinePermFin_one.symm⟩
  inv_mem' := by
    rintro a ⟨g₀, hg₀, t, rfl⟩
    exact ⟨g₀⁻¹, inv_mem hg₀, -(g₀⁻¹ t), affinePermFin_inv g₀ t⟩

/-- **Membership in `affineG` is being an affine perm with linear part in `G₀`** (the transparent carrier). -/
theorem mem_affineG_iff {σ : Equiv.Perm (Fin (p ^ d))} :
    σ ∈ affineG G₀ ↔ ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p),
      g₀ ∈ G₀ ∧ ∃ t, σ = affinePermFin g₀ t :=
  Iff.rfl

/-- A translation lies in `affineG` (linear part `1 ∈ G₀`). -/
theorem affinePermFin_one_mem (t : Fin d → ZMod p) :
    affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) t ∈ affineG G₀ :=
  ⟨1, one_mem _, t, rfl⟩

/-- **Transitivity** — translations act transitively on `F_p^d`. -/
theorem affineG_isPretransitive : MulAction.IsPretransitive (affineG G₀) (Fin (p ^ d)) := by
  refine ⟨fun i j => ?_⟩
  refine ⟨⟨affinePermFin 1 (affineE.symm j - affineE.symm i), affinePermFin_one_mem G₀ _⟩, ?_⟩
  show affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
      (affineE.symm j - affineE.symm i) i = j
  rw [affinePermFin_apply]
  have : (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (affineE.symm i)
      + (affineE.symm j - affineE.symm i) = affineE.symm j := by
    rw [LinearEquiv.coe_one, id_eq]; abel
  rw [this, Equiv.apply_symm_apply]

/-- **Generous transitivity** — with `-1 ∈ G₀`, the orbital of `(x,y)` equals that of `(y,x)` (the
affine map `u ↦ -u + (x+y)` swaps them), so the orbital scheme is symmetric. -/
theorem affineG_generous (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (x y : Fin (p ^ d)) :
    (orbMk x y : Orbital (affineG G₀)) = orbMk y x := by
  rw [orbMk_eq_iff]
  refine ⟨⟨affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y),
      ⟨_, hneg, _, rfl⟩⟩, ?_, ?_⟩
  · show affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y) y = x
    rw [affinePermFin_apply]
    have : (LinearEquiv.neg (ZMod p)) (affineE.symm y) + (affineE.symm x + affineE.symm y)
        = affineE.symm x := by
      simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq]; abel
    rw [this, Equiv.apply_symm_apply]
  · show affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y) x = y
    rw [affinePermFin_apply]
    have : (LinearEquiv.neg (ZMod p)) (affineE.symm x) + (affineE.symm x + affineE.symm y)
        = affineE.symm y := by
      simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq]; abel
    rw [this, Equiv.apply_symm_apply]

/-- **The affine scheme `V ⋊ G₀` over `F_p^d`** (Phase 2, M0.3) — the concrete beachhead family.
The orbital scheme of the affine group acting on `Fin (p^d)`: relations are the `G₀`-orbits on
differences, `relOfPair x y` = the orbit of `y − x`. A `SchurianScheme (p^d)`, pluggable into
`SelfDetectsStably` and the seal. The hypothesis `-1 ∈ G₀` makes the scheme symmetric (generous
transitivity). **Next:** M1 (`IsPrimitive` ⟺ `G₀` irreducible), M2 (irreducible ⟹ recovers). -/
noncomputable def affineScheme (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : SchurianScheme (p ^ d) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Nonempty (Fin (p ^ d)) := ⟨⟨0, Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne p))⟩⟩
  orbitalScheme (affineG G₀) (affineG_isPretransitive G₀) (affineG_generous G₀ hneg)

/-! #### M1.0b — the orbital ⟺ `G₀`-orbit-of-difference characterization (the Schur-ring statement)

This is the affine scheme's defining structure made precise: **two pairs lie in the same orbital iff their
difference vectors are `G₀`-related**. It is exactly the "translation scheme = orbit Schur ring `A(G₀)`"
identity — relations of `affineScheme` ↔ `G₀`-orbits on `V` (differences). It is the bridge M1's
block ⟺ invariant-subspace argument runs on. -/

/-- **Orbital ⟺ `G₀`-orbit of the difference.** `(x,y)` and `(x',y')` are in the same orbital of
`affineG G₀` iff some `g₀ ∈ G₀` carries the difference `e⁻¹y' − e⁻¹x'` to `e⁻¹y − e⁻¹x`. -/
theorem orbMk_affine_eq_iff {x y x' y' : Fin (p ^ d)} :
    (orbMk x y : Orbital (affineG G₀)) = orbMk x' y' ↔
      ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p), g₀ ∈ G₀ ∧
        g₀ (affineE.symm y' - affineE.symm x') = affineE.symm y - affineE.symm x := by
  rw [orbMk_eq_iff]
  constructor
  · rintro ⟨a, hax, hay⟩
    obtain ⟨g₀, hg₀, t, ha⟩ := a.2
    refine ⟨g₀, hg₀, ?_⟩
    rw [ha, affinePermFin_apply] at hax hay
    have hx : g₀ (affineE.symm x') + t = affineE.symm x := by
      have := congrArg affineE.symm hax; rwa [Equiv.symm_apply_apply] at this
    have hy : g₀ (affineE.symm y') + t = affineE.symm y := by
      have := congrArg affineE.symm hay; rwa [Equiv.symm_apply_apply] at this
    rw [map_sub, ← hx, ← hy]; abel
  · rintro ⟨g₀, hg₀, hg⟩
    refine ⟨⟨affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')), ⟨g₀, hg₀, _, rfl⟩⟩, ?_, ?_⟩
    · show affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')) x' = x
      rw [affinePermFin_apply]
      have : g₀ (affineE.symm x') + (affineE.symm x - g₀ (affineE.symm x')) = affineE.symm x := by abel
      rw [this, Equiv.apply_symm_apply]
    · show affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')) y' = y
      rw [affinePermFin_apply]
      have hg2 : g₀ (affineE.symm y') - g₀ (affineE.symm x') = affineE.symm y - affineE.symm x := by
        rw [← map_sub]; exact hg
      have : g₀ (affineE.symm y') + (affineE.symm x - g₀ (affineE.symm x')) = affineE.symm y := by
        rw [show g₀ (affineE.symm y') + (affineE.symm x - g₀ (affineE.symm x'))
              = (g₀ (affineE.symm y') - g₀ (affineE.symm x')) + affineE.symm x from by abel, hg2]
        abel
      rw [this, Equiv.apply_symm_apply]

/-! ### Phase 2, M1.1/M1.2 — primitive ⟹ `G₀` irreducible (the block ⟺ invariant-subspace bridge)

The seal's cascade branch hands you `IsPrimitive (affineScheme)`; M2 (recovery) needs `G₀` irreducible.
This block is the bridge — and it is the **concrete rehearsal of the §5.3 general crux template** ("a block
is a sub-structure; primitivity forbids it"): here the *block* is a `ClosedSubset I`, the *sub-structure* is
a `G₀`-invariant `Submodule`, and the proof builds one from the other. The general crux swaps `Submodule` ↔
fusion / `ClosedSubset` and "invariant subspace" ↔ "block system"; do the affine one first. The direction
that matters is `¬irreducible → ¬IsPrimitive` (contrapositive of what M3 consumes). -/

/-- `Fin (p^d)` is nonempty (`p^d ≥ 1` since `p` is prime). Needed for the orbital indexing/diagonal facts
used below outside the `affineScheme` definition. -/
private instance instNonemptyAffV : Nonempty (Fin (p ^ d)) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  ⟨⟨0, Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne p))⟩⟩

/-- **M1.1a (rel characterization).** A pair `(x,y)` lies in relation `i` of `affineScheme` iff its orbital
is the one indexed by `i`. Unfolds the orbital-scheme `rel` field (a `decide` of orbital equality). -/
theorem affineScheme_rel_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {i : Fin ((affineScheme G₀ hneg).rank + 1)} {x y : Fin (p ^ d)} :
    (affineScheme G₀ hneg).rel i x y = true ↔ orbitalIdx (affineG G₀) i = orbMk x y := by
  simp only [affineScheme, orbitalScheme, orbitalAssocScheme, decide_eq_true_eq]

/-- `relOfPair` for `affineScheme` is the index of the pair's orbital. -/
theorem affineScheme_relOfPair (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (x y : Fin (p ^ d)) :
    (affineScheme G₀ hneg).relOfPair x y = (orbitalIdx (affineG G₀)).symm (orbMk x y) := by
  have h : (affineScheme G₀ hneg).rel ((orbitalIdx (affineG G₀)).symm (orbMk x y)) x y = true := by
    rw [affineScheme_rel_iff]; exact Equiv.apply_symm_apply _ _
  exact ((affineScheme G₀ hneg).relOfPair_unique h).symm

/-- **M1.1a (relOfPair characterization).** Two pairs have the same relation iff they have the same orbital.
The `relOfPair`-level form of `orbMk_affine_eq_iff`, used to transport difference-membership across a
relation. -/
theorem affineScheme_relOfPair_eq_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {x y x' y' : Fin (p ^ d)} :
    (affineScheme G₀ hneg).relOfPair x y = (affineScheme G₀ hneg).relOfPair x' y' ↔
      (orbMk x y : Orbital (affineG G₀)) = orbMk x' y' := by
  rw [affineScheme_relOfPair, affineScheme_relOfPair]
  exact (orbitalIdx (affineG G₀)).symm.injective.eq_iff

/-- **M1.1b — `G₀` acts irreducibly** (self-contained, no `IsSimpleModule`): the only `G₀`-invariant
subspaces are `⊥` and `⊤`. The hypothesis M2's recovery argument consumes; primitivity of `affineScheme`
delivers it (M1.2). -/
def G₀Irreducible : Prop :=
  ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
    (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

/-- The **difference of a relation**: the difference `y₀ − x₀` of `i`'s chosen representative pair
`(x₀,y₀)`. Well-defined as a `G₀`-orbit (different representatives give `G₀`-translates, so membership in a
`G₀`-invariant subspace is rep-independent — `affineRelDiff_mem_iff`). -/
noncomputable def affineRelDiff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (i : Fin ((affineScheme G₀ hneg).rank + 1)) : Fin d → ZMod p :=
  affineE.symm (orbitalIdx (affineG G₀) i).out.2 - affineE.symm (orbitalIdx (affineG G₀) i).out.1

/-- The diagonal relation `R_0` has difference `0` (its representative pair is `(v,v)`). -/
theorem affineRelDiff_zero (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) :
    affineRelDiff G₀ hneg 0 = 0 := by
  -- The representative pair of the diagonal relation `R₀` is `(v, v)`, so its difference is `0`.
  -- Work at the diagonal index `(0 : Fin ((affineScheme ...).rank + 1))` throughout (`rel_zero_iff_eq`
  -- lives at this rank type, avoiding the `orbitalRank` vs `affineScheme.rank` ascription mismatch).
  have hr : (affineScheme G₀ hneg).rel 0
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1))).out.1
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1))).out.2 = true := by
    rw [affineScheme_rel_iff]
    exact (orbMk_out (affineG G₀)
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1)))).symm
  have heq := ((affineScheme G₀ hneg).rel_zero_iff_eq _ _).mp hr
  unfold affineRelDiff
  rw [← heq, sub_self]

/-- **Difference-membership is constant along a relation.** If `(x,y) ∈ R_i` then `affineRelDiff i ∈ W`
iff `(e⁻¹y − e⁻¹x) ∈ W`, for any `G₀`-invariant `W`. This is where invariance does the work: any two pairs
of `R_i` differ by a `G₀`-translate (`orbMk_affine_eq_iff`), so a `G₀`-invariant subspace cannot tell them
apart. The key well-definedness lemma for the `ClosedSubset` construction. -/
theorem affineRelDiff_mem_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {W : Submodule (ZMod p) (Fin d → ZMod p)}
    (hWinv : ∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W)
    {i : Fin ((affineScheme G₀ hneg).rank + 1)} {x y : Fin (p ^ d)}
    (hrel : (affineScheme G₀ hneg).rel i x y = true) :
    affineRelDiff G₀ hneg i ∈ W ↔ affineE.symm y - affineE.symm x ∈ W := by
  have hidx : orbitalIdx (affineG G₀) i = orbMk x y := (affineScheme_rel_iff G₀ hneg).mp hrel
  have hout : (orbMk (orbitalIdx (affineG G₀) i).out.1 (orbitalIdx (affineG G₀) i).out.2
      : Orbital (affineG G₀)) = orbMk x y := by rw [orbMk_out, hidx]
  obtain ⟨g, hg₀, hgeq⟩ := (orbMk_affine_eq_iff G₀).mp hout
  -- `hgeq : g (e⁻¹y − e⁻¹x) = e⁻¹ out.2 − e⁻¹ out.1`, which is `affineRelDiff i` by definition.
  have hgeq' : g (affineE.symm y - affineE.symm x) = affineRelDiff G₀ hneg i := hgeq
  have hgg : (g⁻¹ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (affineRelDiff G₀ hneg i)
      = affineE.symm y - affineE.symm x := by
    rw [← hgeq', ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq]
  constructor
  · intro hmem
    rw [← hgg]
    exact hWinv _ (inv_mem hg₀) _ hmem
  · intro hmem
    rw [← hgeq']
    exact hWinv _ hg₀ _ hmem

/-- **M1.2 — primitive ⟹ `G₀` irreducible.** The bridge M3 consumes, by contrapositive: from a proper
`G₀`-invariant subspace `W`, build the closed subset `I := {i | affineRelDiff i ∈ W}` — a genuine block
system, contradicting primitivity. `0 ∈ I` (diagonal diff `0 ∈ W`); closure follows because a composable
triple's differences add (`exists_composable_of_intersectionNumber` + `W.add_mem`); `I ≠ {0}` from a
nonzero `w ∈ W`; `I ≠ univ` from a `v ∉ W`. **This is the §5.3 template instantiated** (`Submodule` for the
sub-structure, `ClosedSubset` for the block). -/
theorem isPrimitive_affineScheme_imp_irreducible (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (hprim : (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive) :
    G₀Irreducible G₀ := by
  intro W hWinv
  by_contra hcon
  push_neg at hcon
  obtain ⟨hW0, hWT⟩ := hcon
  classical
  set I : Finset (Fin ((affineScheme G₀ hneg).rank + 1)) :=
    Finset.univ.filter (fun i => affineRelDiff G₀ hneg i ∈ W) with hIdef
  have hmemI : ∀ i, i ∈ I ↔ affineRelDiff G₀ hneg i ∈ W := by
    intro i; rw [hIdef, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
  -- `I` is a closed subset (a block system).
  have hcl : (affineScheme G₀ hneg).toAssociationScheme.ClosedSubset I := by
    refine ⟨?_, ?_⟩
    · rw [hmemI, affineRelDiff_zero]; exact W.zero_mem
    · intro i hi j hj k hk
      have hkne : ∃ x z, (affineScheme G₀ hneg).rel k x z = true :=
        ⟨_, _, (affineScheme_rel_iff G₀ hneg).mpr
          (orbMk_out (affineG G₀) (orbitalIdx (affineG G₀) k)).symm⟩
      obtain ⟨x, y, z, hxy, hyz, hxz⟩ :=
        (affineScheme G₀ hneg).toAssociationScheme.exists_composable_of_intersectionNumber hkne hk
      have hi' : affineE.symm y - affineE.symm x ∈ W :=
        (affineRelDiff_mem_iff G₀ hneg hWinv hxy).mp ((hmemI i).mp hi)
      have hj' : affineE.symm z - affineE.symm y ∈ W :=
        (affineRelDiff_mem_iff G₀ hneg hWinv hyz).mp ((hmemI j).mp hj)
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hxz,
        show affineE.symm z - affineE.symm x
          = (affineE.symm y - affineE.symm x) + (affineE.symm z - affineE.symm y) from by abel]
      exact W.add_mem hi' hj'
  -- `I ≠ {0}`: a nonzero `w ∈ W` gives a nondiagonal relation in `I`.
  have hIne0 : I ≠ {0} := by
    obtain ⟨w, hwW, hwne⟩ := (Submodule.ne_bot_iff W).mp hW0
    have hrel : (affineScheme G₀ hneg).rel
        ((affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w)) (affineE 0) (affineE w) = true :=
      (affineScheme G₀ hneg).rel_relOfPair _ _
    have hdiff : affineE.symm (affineE w) - affineE.symm (affineE (0 : Fin d → ZMod p)) = w := by
      simp only [Equiv.symm_apply_apply, sub_zero]
    have hi₀I : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w) ∈ I := by
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hrel, hdiff]; exact hwW
    have hi₀ne : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w) ≠ 0 := by
      intro hzero
      rw [(affineScheme G₀ hneg).relOfPair_eq_zero_iff] at hzero
      exact hwne (affineE.injective hzero).symm
    intro hI0
    rw [hI0, Finset.mem_singleton] at hi₀I
    exact hi₀ne hi₀I
  -- `I ≠ univ`: a `v ∉ W` gives a relation outside `I`.
  have hInu : I ≠ Finset.univ := by
    have hexv : ∃ v, v ∉ W := by
      by_contra h
      push_neg at h
      exact hWT (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hvnotW⟩ := hexv
    have hrel : (affineScheme G₀ hneg).rel
        ((affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v)) (affineE 0) (affineE v) = true :=
      (affineScheme G₀ hneg).rel_relOfPair _ _
    have hdiff : affineE.symm (affineE v) - affineE.symm (affineE (0 : Fin d → ZMod p)) = v := by
      simp only [Equiv.symm_apply_apply, sub_zero]
    have hi₁notI : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∉ I := by
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hrel, hdiff]; exact hvnotW
    intro hIu
    rw [hIu] at hi₁notI
    exact hi₁notI (Finset.mem_univ _)
  rcases hprim I hcl with h | h
  · exact hIne0 h
  · exact hInu h

/-- **M2-B, affine depth-1 discreteness (the `G₀`-orbit-of-difference form).** Specializes
`discrete_of_jointProfileSeparates` to `affineScheme`: if individualizing `T` makes the `G₀`-orbits of the
differences `(u − t)_{t ∈ T}` jointly separate `V`, then `warmRefine` from `T` is `Discrete`. Concretely the
**depth-1 affine separability** condition — `∀ u u'`, if for every `t ∈ T` some `g₀ ∈ G₀` carries
`e⁻¹u′ − e⁻¹t` to `e⁻¹u − e⁻¹t` (same `G₀`-orbit of difference), then `u = u'`. This is the finite,
checkable target the affine probe measures at depth 1; combined with `stablyRecoverable_of_discrete` +
`selfDetectsStably_of_discretizes` it discharges the seal for any depth-1-separating primitive small affine
residual. The open remainder (cyclotomic / `s(C) ≥ 2`) is the *iterated* version of this same separation. -/
theorem discrete_affineScheme_of_jointSeparates (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {T : Finset (Fin (p ^ d))}
    (hsep : ∀ u u' : Fin (p ^ d),
      (∀ t ∈ T, ∃ g₀ ∈ G₀,
        g₀ (affineE.symm u' - affineE.symm t) = affineE.symm u - affineE.symm t) → u = u') :
    Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
      (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)) := by
  apply discrete_of_jointProfileSeparates
  intro u u' hjp
  refine hsep u u' (fun t ht => ?_)
  exact (orbMk_affine_eq_iff G₀).mp ((affineScheme_relOfPair_eq_iff G₀ hneg).mp (hjp t ht))

/-- **F2a — translation-invariance of the affine relation (the load-bearing depth-2 → coset bridge).**
`relOfPair t z` depends only on the difference `e⁻¹z − e⁻¹t`: it equals the relation of that difference
measured from the origin (`g₀ = 1` carries one orbital representative to the other). So the depth-2 profile
`(relOfPair t z)_{t ∈ T}` is exactly the **multi-coset membership** `(e⁻¹z − e⁻¹t ∈ C_·)_{t ∈ T}` — the
object the Frobenius `s(C)` count (F2b, self-detection-plan §11.8) lives in. -/
theorem affineScheme_relOfPair_translation (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (t z : Fin (p ^ d)) :
    (affineScheme G₀ hneg).relOfPair t z
      = (affineScheme G₀ hneg).relOfPair (affineE 0)
          (affineE (affineE.symm z - affineE.symm t)) := by
  rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff]
  refine ⟨1, one_mem _, ?_⟩
  simp only [Equiv.symm_apply_apply, sub_zero, LinearEquiv.coe_one, id_eq]

/-- **F2a — the depth-2 affine discreteness producer, difference (coset) form.** Specializes the general
depth-2 engine `discrete_of_twoRoundRelationSeparates` to `affineScheme`, with the relation conditions
rewritten — via `affineScheme_relOfPair_translation` — as **difference-relation** conditions: the depth-2
profile of `z` is `(relation of e⁻¹z − e⁻¹t from the origin)_{t ∈ T}` together with `(relation of
e⁻¹z − e⁻¹u)`. So if, for every difference-relation profile `ρ` and tail relation `b`, the counts of such
`z` agree between `u` and `u'` only when `u = u'`, then `warmRefine` from `T` is `Discrete`. This is the
**multi-coset-intersection injectivity** the Frobenius `s(C)` bound (F2b) discharges — the clean affine target
the probe `Probe_RoundsToDiscrete_Cyclotomic` measures. -/
theorem discrete_affineScheme_of_twoRoundDiffSeparates (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {T : Finset (Fin (p ^ d))}
    (hsep : ∀ u u' : Fin (p ^ d),
      (∀ (ρ : Fin (p ^ d) → Fin ((affineScheme G₀ hneg).rank + 1))
          (b : Fin ((affineScheme G₀ hneg).rank + 1)),
        (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u)) = b)).card
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u')) = b)).card) → u = u') :
    Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
      (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)) := by
  apply discrete_of_twoRoundRelationSeparates
  intro u u' hcounts
  refine hsep u u' (fun ρ b => ?_)
  have key : ∀ w : Fin (p ^ d),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair t z = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair w z = b))
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm w)) = b)) := by
    intro w
    apply Finset.filter_congr
    intro z _
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · exact forall₂_congr fun t _ => by rw [affineScheme_relOfPair_translation G₀ hneg t z]
    · rw [affineScheme_relOfPair_translation G₀ hneg w z]
  rw [← key u, ← key u']
  exact hcounts ρ b

/-- **E3 — the seal reduced to the affine irreducible-discreteness bound (the affine-cyclic slice).**
Specializes the fused seal `reachesRigidOrCameron_viaFusedSeal` to the affine model `affineScheme G₀ hneg`,
discharging its self-detection input through `selfDetectsStably_of_discretizes` and converting the seal's
`IsPrimitive` antecedent into `G₀Irreducible` via **M1.2** (`isPrimitive_affineScheme_imp_irreducible`). So
the affine slice's seal is reduced to a **single open hypothesis** `hbound`: *irreducible `G₀` (and small) ⟹
a bounded individualization warm-refines to a discrete colouring* — exactly the cyclotomic / Schur-ring
separability target (E2.4: the Frobenius/Galois `s(C)` bound for cyclic irreducible `G₀`). The "cyclotomic
family" needs **no new model**: it is `affineScheme` with cyclic `G₀`, and `hbound` is the only open content.

**⚠️ CONDITIONAL — not the closed seal.** It still carries `hClassify` (G3), `hImprim` (landed/earned,
tower-reducible to the primitive floor), and the **open** `hbound`. Closing `hbound` — even for cyclic `G₀`
— is uncited open `s(C)` mathematics (seal-handoff §6 insight 2). The engine that *discharges* `hbound` is
§13b (`twoRoundCount_eq_of_warmRefine` / `discrete_of_twoRoundProfileSeparates`) fed by the multi-base
Frobenius separation (the `O(d)` Γ-breaking base individualizing into a discrete colouring). Do **not** read
this as "the seal is closed for the affine/cyclotomic family." -/
theorem reachesRigidOrCameron_viaAffineIrreducible {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (hne : ∀ i : Fin ((affineScheme G₀ hneg).rank + 1),
        ∃ v w, (affineScheme G₀ hneg).rel i v w = true)
    (hrank : 2 ≤ (affineScheme G₀ hneg).rank)
    (hbound : G₀Irreducible G₀ ∧ ¬ IsLargeSchemeViaAut IsLarge (p ^ d) (affineScheme G₀ hneg) →
        ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
          Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
            (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)))
    (hImprim : ¬ (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
          ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg)) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
        ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme G₀ hneg) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme G₀ hneg) := by
  refine reachesRigidOrCameron_viaFusedSeal hClassify (affineScheme G₀ hneg) hne hrank ?_ hImprim
  apply selfDetectsStably_of_discretizes
  rintro ⟨hprim, hsmall⟩
  exact hbound ⟨isPrimitive_affineScheme_imp_irreducible G₀ hneg hprim, hsmall⟩

end AffineScheme

/-! ### Phase 2 / F0 — the cyclic (cyclotomic) affine instance

`affineScheme` instantiated at a **cyclic irreducible** `G₀ = ⟨σ⟩`, where `σ` is multiplication by a
generator of `F_qˣ` (`q = p^d`) transported to the coordinate space `F_p^d = Fin d → ZMod p` along a field
basis `efield : F_q ≃ₗ F_p^d`. This delivers the two model inputs the seal capstone
`reachesRigidOrCameron_viaAffineIrreducible` is stated against on the cyclic floor:
- `G0cyc_irreducible : G₀Irreducible (G0cyc hd)` — EARNED, via the multiplicative-orbit argument (a
  `mul·α`-invariant nonzero subspace contains a full `F_qˣ`-orbit = all nonzero elements ⟹ is `⊤`); no
  `IsSimpleModule` / `F_p[α]=F_q` algebra needed, just that `α` generates `F_qˣ`.
- `neg_mem_G0cyc : neg ∈ G0cyc hd` — the symmetry hypothesis `hneg` (`-1 = α^k` for some `k`, so
  `neg = σ^k`).
The Frobenius `s(C)` bound (F1/F2, self-detection-plan §11.8) targets the remaining `hbound` (discreteness)
on this instance. The two transport homs `mulUnitHom` (mult-by-unit) and `conjHom` (conjugation by `efield`)
make `σ^k` reduce to `α^k` for free (`MonoidHom.map_zpow`), which is what both deliverables turn on. -/

section CyclicAffine

variable {p d : ℕ} [Fact p.Prime]

/-- `GaloisField p d` is finite; equip it with a `Fintype` (no direct instance exists). -/
noncomputable local instance instFintypeGaloisField : Fintype (GaloisField p d) :=
  Fintype.ofFinite _

/-- The field basis isomorphism `F_q ≃ₗ F_p^d` (`q = p^d`), from `finrank = d`. -/
noncomputable def efield (hd : d ≠ 0) : GaloisField p d ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  ((Module.finBasis (ZMod p) (GaloisField p d)).reindex
    (finCongr (GaloisField.finrank p hd))).equivFun

/-- Multiplication-by-a-unit as an `F_p`-linear automorphism of `F_q` — a monoid hom from `F_qˣ`. The
engine for `σ` (mult by a multiplicative generator); being a monoid hom is what lets `σ^k` reduce to `α^k`. -/
noncomputable def mulUnitHom :
    (GaloisField p d)ˣ →* (GaloisField p d ≃ₗ[ZMod p] GaloisField p d) where
  toFun u := LinearEquiv.ofBijective (LinearMap.mulLeft (ZMod p) (u : GaloisField p d))
    ⟨fun x y h => mul_left_cancel₀ u.ne_zero (by simpa [LinearMap.mulLeft_apply] using h),
     fun y => ⟨(↑u⁻¹ : GaloisField p d) * y, by
        rw [LinearMap.mulLeft_apply, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ u.ne_zero]⟩⟩
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [LinearMap.mulLeft_apply, LinearEquiv.mul_apply, Units.val_mul]

@[simp] theorem mulUnitHom_apply (u : (GaloisField p d)ˣ) (x : GaloisField p d) :
    mulUnitHom u x = (u : GaloisField p d) * x := by
  simp [mulUnitHom]

/-- Conjugation by `efield`: a monoid hom `(F_q ≃ₗ F_q) →* (F_p^d ≃ₗ F_p^d)`. -/
noncomputable def conjHom (hd : d ≠ 0) :
    (GaloisField p d ≃ₗ[ZMod p] GaloisField p d) →*
      ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) where
  toFun e := (efield hd).symm.trans (e.trans (efield hd))
  map_one' := by ext u; simp
  map_mul' a b := by ext u; simp [LinearEquiv.mul_apply]

@[simp] theorem conjHom_apply (hd : d ≠ 0) (e : GaloisField p d ≃ₗ[ZMod p] GaloisField p d)
    (u : Fin d → ZMod p) : conjHom hd e u = efield hd (e ((efield hd).symm u)) := by
  simp [conjHom]

/-- A multiplicative generator of `F_qˣ` (cyclic). -/
noncomputable def fqGen : (GaloisField p d)ˣ :=
  (IsCyclic.exists_generator (α := (GaloisField p d)ˣ)).choose

theorem fqGen_spec (x : (GaloisField p d)ˣ) : x ∈ Subgroup.zpowers (fqGen (p := p) (d := d)) :=
  (IsCyclic.exists_generator (α := (GaloisField p d)ˣ)).choose_spec x

/-- `σ` — multiplication by `fqGen`, transported to the coordinate space; the generator of `G₀`. -/
noncomputable def sigmaCyc (hd : d ≠ 0) : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd (mulUnitHom (fqGen (p := p) (d := d)))

/-- The cyclic affine group `G₀ = ⟨σ⟩ ≤ GL(F_p^d)`. -/
noncomputable def G0cyc (hd : d ≠ 0) : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
  Subgroup.zpowers (sigmaCyc hd)

/-- `σ^k` acts as multiplication by `α^k` through the field iso — the load-bearing reduction
(`σ^k` ↦ `α^k` for free, since `σ = conjHom (mulUnitHom α)` and both are monoid homs). -/
theorem sigmaCyc_zpow_apply (hd : d ≠ 0) (k : ℤ) (u : Fin d → ZMod p) :
    (sigmaCyc hd ^ k) u
      = efield hd (((fqGen (p := p) (d := d) ^ k : (GaloisField p d)ˣ) : GaloisField p d)
          * (efield hd).symm u) := by
  have hpow : sigmaCyc hd ^ k = conjHom hd (mulUnitHom (fqGen (p := p) (d := d) ^ k)) := by
    rw [sigmaCyc, ← MonoidHom.map_zpow, ← MonoidHom.map_zpow]
  rw [hpow, conjHom_apply, mulUnitHom_apply]

/-- Every nonzero `z ∈ F_q` is a natural power of the generator `α` (the multiplicative-orbit fact). -/
theorem exists_npow_fqGen (z : GaloisField p d) (hz : z ≠ 0) :
    ∃ k : ℕ, ((fqGen (p := p) (d := d)) : GaloisField p d) ^ k = z := by
  have hmem : (Units.mk0 z hz) ∈ Submonoid.powers (fqGen (p := p) (d := d)) :=
    mem_powers_iff_mem_zpowers.2 (fqGen_spec _)
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have hv := congrArg (Units.val) hk
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at hv

/-- **`hneg` for the cyclic instance** — `neg ∈ G0cyc` (since `-1 = α^k`, `neg = σ^k`). -/
theorem neg_mem_G0cyc (hd : d ≠ 0) : LinearEquiv.neg (ZMod p) ∈ G0cyc hd := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (fqGen_spec (-1 : (GaloisField p d)ˣ))
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  ext u
  rw [sigmaCyc_zpow_apply, hk]
  have h1 : ((-1 : (GaloisField p d)ˣ) : GaloisField p d) = -1 := by simp
  rw [h1, neg_one_mul, map_neg, LinearEquiv.apply_symm_apply, LinearEquiv.neg_apply]

/-- **`G₀Irreducible` for the cyclic instance** — EARNED via the multiplicative-orbit argument:
a `σ`-invariant nonzero subspace `W` contains, for `0 ≠ w₀ ∈ W`, the full orbit `{α^k · w₀}`, which
(since `α` generates `F_qˣ`) is every nonzero element ⟹ `W = ⊤`. -/
theorem G0cyc_irreducible (hd : d ≠ 0) : G₀Irreducible (G0cyc (p := p) hd) := by
  intro W hWinv
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  refine Or.inr ?_
  have hσmem : sigmaCyc (p := p) hd ∈ G0cyc (p := p) hd := Subgroup.mem_zpowers _
  obtain ⟨w₀, hw₀W, hw₀0⟩ := (Submodule.ne_bot_iff W).1 hWbot
  set x₀ : GaloisField p d := (efield hd).symm w₀ with hx₀def
  have hx₀0 : x₀ ≠ 0 := by
    rw [hx₀def, ne_eq, LinearEquiv.map_eq_zero_iff]; exact hw₀0
  rw [eq_top_iff]
  intro v _
  by_cases hv0 : (efield hd).symm v = 0
  · have hvz : v = 0 := by
      have hcong := congrArg (efield hd) hv0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at hcong
    rw [hvz]; exact W.zero_mem
  · set y : GaloisField p d := (efield hd).symm v with hydef
    obtain ⟨k, hk⟩ := exists_npow_fqGen (y * x₀⁻¹) (mul_ne_zero hv0 (inv_ne_zero hx₀0))
    have hmemk : (sigmaCyc hd ^ (k : ℤ)) w₀ ∈ W :=
      hWinv _ (Subgroup.zpow_mem _ hσmem k) w₀ hw₀W
    have hval : (sigmaCyc hd ^ (k : ℤ)) w₀ = v := by
      rw [sigmaCyc_zpow_apply,
        show ((fqGen (p := p) (d := d) ^ (k : ℤ) : (GaloisField p d)ˣ) : GaloisField p d)
            = ((fqGen (p := p) (d := d)) : GaloisField p d) ^ k from by
          rw [zpow_natCast, Units.val_pow_eq_pow_val],
        hk, ← hx₀def, mul_assoc, inv_mul_cancel₀ hx₀0, mul_one, hydef,
        LinearEquiv.apply_symm_apply]
    rwa [hval] at hmemk

/-- The **cyclic affine scheme** — `affineScheme` at `G0cyc`. Irreducible (`G0cyc_irreducible`) and symmetric
(`neg_mem_G0cyc`). **⚠️ NOTE (2026-06-09): this is the rank-2 complete graph `K_{p^d}`** — `G0cyc` uses a
*full* multiplicative generator, so `⟨mul fqGen⟩` is transitive on `V ∖ {0}` (one nonzero orbit). It is the
degenerate *large* case (routed to Cameron), **not** the cyclotomic leak candidate. The genuine F2b target is
`G0pow β` for a **proper** `β = α^m` (see the "F2b target correction" subsection below); use
`G0pow_irreducible` there, not this. -/
noncomputable def cyclicAffineScheme (hd : d ≠ 0) : SchurianScheme (p ^ d) :=
  affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)

/-! #### F1 — the Frobenius structure (the `Ĝ ⊋ G` separability gap, made concrete)

The Frobenius `φ : x ↦ x^p` is `ZMod p`-**linear** (because `c^p = c` on the prime field), so it sits in
`GL(d,p)`, and it conjugates `σ` (mult by the generator `α`) to `σ^p` (`φ(α·x) = α^p·φ(x)`). Hence `φ`
**normalizes** `G0cyc = ⟨σ⟩` but generally is **not in it**: `⟨σ, φ⟩ = ΓL(1,q) ⊋ ⟨σ⟩`. That extra Galois
symmetry is an *algebraic* automorphism of the scheme the group does not realize — the `Ĝ ⊋ G` gap, and the
degeneracy a `Γ`-fixed base would suffer (F2). **General-theorem shadow:** this conjugation relation
`φσφ⁻¹ = σ^p` is exactly "an algebraic automorphism not in the group", which is what the `s(C)` leak is in
general — here it is finite-dimensional and explicit. -/

/-- Frobenius `x ↦ x^p` as a `ZMod p`-**linear** automorphism of `F_q` (linear since `c^p = c` on the prime
field, `ZMod.pow_card`). The algebraic automorphism witnessing the `Ĝ ⊋ G` gap. -/
noncomputable def frobLinear : GaloisField p d ≃ₗ[ZMod p] GaloisField p d where
  toFun := frobeniusEquiv (GaloisField p d) p
  map_add' := map_add _
  map_smul' c x := by
    show frobeniusEquiv (GaloisField p d) p (c • x)
        = (RingHom.id (ZMod p)) c • frobeniusEquiv (GaloisField p d) p x
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [frobeniusEquiv_def, ← map_pow, ZMod.pow_card]
  invFun := (frobeniusEquiv (GaloisField p d) p).symm
  left_inv := (frobeniusEquiv (GaloisField p d) p).left_inv
  right_inv := (frobeniusEquiv (GaloisField p d) p).right_inv

@[simp] theorem frobLinear_apply (x : GaloisField p d) :
    frobLinear (p := p) (d := d) x = x ^ p := frobeniusEquiv_def (GaloisField p d) p x

/-- **The twist relation** `φ(α·x) = α^p · φ(x)` — Frobenius is a ring hom, so it carries multiplication by
`α` to multiplication by `α^p`. The algebraic core of the gap. -/
theorem frobLinear_mul (α x : GaloisField p d) :
    frobLinear (α * x) = α ^ p * frobLinear x := by
  simp only [frobLinear_apply, mul_pow]

/-- `φ` carries `mul·α` to `(mul·α)^p` under conjugation, as an identity of linear automorphisms
(`φ ∘ (mul α) ∘ φ⁻¹ = (mul α)^p`). -/
theorem frobLinear_conj_mulUnit :
    frobLinear (p := p) (d := d) * mulUnitHom (fqGen) * (frobLinear)⁻¹
      = (mulUnitHom (fqGen (p := p) (d := d))) ^ p := by
  ext x
  have hinv : frobLinear (p := p) (d := d) ((frobLinear (p := p) (d := d))⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [← map_pow, mulUnitHom_apply, Units.val_pow_eq_pow_val, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, mulUnitHom_apply, frobLinear_mul, hinv]

/-- Frobenius transported to the coordinate space `F_p^d` — an element of `GL(d,p)` (the linear part of a
Galois twist of the affine group). -/
noncomputable def frobCoord (hd : d ≠ 0) : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd frobLinear

/-- **The normalizing relation** `frobCoord · σ · frobCoord⁻¹ = σ^p` — Frobenius conjugates the cyclic
generator to its `p`-th power. So `frobCoord` normalizes `G0cyc = ⟨σ⟩` but lies in it only when `φ ∈ ⟨σ⟩`;
in general `⟨σ, frobCoord⟩ = ΓL(1,q) ⊋ ⟨σ⟩` — the algebraic-automorphism gap (`Ĝ ⊋ G`) the cyclotomic
`s(C)` leak would exploit, here finite and explicit. -/
theorem frobCoord_conj_sigmaCyc (hd : d ≠ 0) :
    frobCoord (p := p) hd * sigmaCyc hd * (frobCoord hd)⁻¹ = sigmaCyc hd ^ p := by
  rw [frobCoord, sigmaCyc, ← map_inv, ← map_mul, ← map_mul, frobLinear_conj_mulUnit, map_pow]

/-! #### F2b frame — the cyclic separation crux as a single named proposition

This packages the entire open content of the affine-cyclic slice into ONE Lean proposition
(`CyclicAffineSeparates`) and wires it to the seal (`reachesRigidOrCameron_viaCyclicSeparation`). It does
**not** prove the crux — `CyclicAffineSeparates` is carried as a hypothesis, exactly the uncited open `s(C)`
counting (self-detection-plan §11.8 F2b). Its value is turning the prose conjecture into one falsifiable
statement about **multi-coset-intersection counts**, the object F1's Frobenius structure acts on (a `Γ`-fixed
base produces `φ`-twins; a Γ-breaking base is conjectured to separate — the de-risk probe
`Probe_RoundsToDiscrete_Cyclotomic` confirms this empirically at `|T| = O(d)`, depth 2). -/

/-- **The cyclic-affine separation crux (the single open proposition).** A bounded individualization set `T`
whose depth-2 **difference profile** is injective: for every difference-relation profile `ρ` and tail
relation `b`, the multi-coset-intersection counts of matching `z` separate every pair of vertices. This is
the Frobenius `s(C)` bound; `discrete_affineScheme_of_twoRoundDiffSeparates` consumes it to discharge
`hbound`. **Open** — the empirically-confirmed (probe) but uncited counting core. -/
def CyclicAffineSeparates (hd : d ≠ 0) (bound : Nat) : Prop :=
  ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
    ∀ u u' : Fin (p ^ d),
      (∀ (ρ : Fin (p ^ d) → Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1))
          (b : Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1)),
        (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
          (∀ t ∈ T, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u)) = b)).card
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
          (∀ t ∈ T, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u')) = b)).card) → u = u'

/-- **The seal on the cyclic-affine family, reduced to the single crux `CyclicAffineSeparates`.** Instantiates
`reachesRigidOrCameron_viaAffineIrreducible` at the cyclic `G₀ = G0cyc`, discharging `hbound` from
`CyclicAffineSeparates` via the F2a producer `discrete_affineScheme_of_twoRoundDiffSeparates`.

**⚠️ CONDITIONAL — NOT the closed seal.** It carries `hClassify` (G3, cited), `hne`/`hrank` (the scheme is a
genuine rank-≥2 association scheme — discharged per instance), `hImprim` (landed/earned, tower-reducible), and
the **open** `hsep : CyclicAffineSeparates` (the Frobenius `s(C)` counting, F2b — uncited). Closing the seal on
this family ⟺ proving `CyclicAffineSeparates`, which is open `s(C)` mathematics. -/
theorem reachesRigidOrCameron_viaCyclicSeparation (hd : d ≠ 0)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1),
        ∃ v w, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank)
    (hsep : CyclicAffineSeparates (p := p) hd bound)
    (hImprim : ¬ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)) := by
  refine reachesRigidOrCameron_viaAffineIrreducible (G₀ := G0cyc hd) hClassify (neg_mem_G0cyc hd)
    hne hrank ?_ hImprim
  rintro ⟨-, -⟩
  obtain ⟨T, hcard, hTsep⟩ := hsep
  exact ⟨T, hcard, discrete_affineScheme_of_twoRoundDiffSeparates (G0cyc hd) (neg_mem_G0cyc hd) hTsep⟩

/-! #### F2b target correction — proper cyclic subgroups (the genuine cyclotomic schemes)

**Gap (found 2026-06-09).** `G0cyc` uses a *full* multiplicative generator `fqGen`, so `⟨mul fqGen⟩` is
transitive on `V ∖ {0}` ⟹ `cyclicAffineScheme` is the **rank-2 complete graph `K_{p^d}`** — the *large* case
(`|Aut| = (p^d)!`, routed to Cameron), NOT the cyclotomic leak candidate (for which `CyclicAffineSeparates`
is in fact false: no bounded base discretizes `K_q`). The genuine F2b target is a **proper** cyclic subgroup
`G0pow β = ⟨mul β⟩` (`β = α^m`, e.g. the index-3 Clebsch family on `F_16`), `rank ≥ 3`, where irreducibility
comes from `β` **field-generating** `F_q` — NOT from the orbit being everything. `G0pow_irreducible` is the
§5.3 "invariant subspace ⟺ subfield" template: a `mul·β`-invariant subspace closed under `mul·β` is closed
under `mul·F_p[β] = mul·F_q`, hence `⊥` or `⊤`. F1's `Ĝ ⊋ G` Frobenius gap is the Galois action permuting
these (subfield-free) cosets. **Open:** proving separation (`CyclicAffineSeparates`-analogue) for `G0pow β`
is the uncited `s(C)` crux. -/

/-- `σ_β` — multiplication by an arbitrary unit `β`, transported to `F_p^d`. Generalizes `sigmaCyc`
(`= sigmaPow fqGen`). -/
noncomputable def sigmaPow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd (mulUnitHom β)

/-- The cyclic affine group `G₀ = ⟨mul β⟩` for an arbitrary unit `β` (the proper-subgroup / cyclotomic case
when `β = α^m`). Generalizes `G0cyc` (`= G0pow fqGen`). -/
noncomputable def G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
  Subgroup.zpowers (sigmaPow hd β)

/-- `σ_β^k` acts as multiplication by `β^k` through the field iso. Generalizes `sigmaCyc_zpow_apply`. -/
theorem sigmaPow_zpow_apply (hd : d ≠ 0) (β : (GaloisField p d)ˣ) (k : ℤ) (u : Fin d → ZMod p) :
    (sigmaPow hd β ^ k) u
      = efield hd (((β ^ k : (GaloisField p d)ˣ) : GaloisField p d) * (efield hd).symm u) := by
  have hpow : sigmaPow hd β ^ k = conjHom hd (mulUnitHom (β ^ k)) := by
    rw [sigmaPow, ← MonoidHom.map_zpow, ← MonoidHom.map_zpow]
  rw [hpow, conjHom_apply, mulUnitHom_apply]

/-- **`hneg` for the proper cyclic instance** — `neg ∈ G0pow β` when `-1 ∈ ⟨β⟩`. Generalizes `neg_mem_G0cyc`. -/
theorem neg_mem_G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) :
    LinearEquiv.neg (ZMod p) ∈ G0pow hd β := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hβneg
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  ext u
  rw [sigmaPow_zpow_apply, hk]
  have h1 : ((-1 : (GaloisField p d)ˣ) : GaloisField p d) = -1 := by simp
  rw [h1, neg_one_mul, map_neg, LinearEquiv.apply_symm_apply, LinearEquiv.neg_apply]

/-- **`G₀Irreducible (G0pow β)` via field-generation** (the §5.3 subfield template). If the `F_p`-span of the
powers of `β` is all of `F_q` (`β` field-generates), then `⟨mul β⟩` acts irreducibly: a `mul·β`-invariant
nonzero subspace `W` contains, for `0 ≠ w₀ ∈ W`, the image `f '' {β^k}` where `f : c ↦ efield (x₀ · c)`
(`x₀ = e⁻¹w₀`); since `span {β^k} = ⊤` and `f` is surjective, that image spans `⊤`, so `W = ⊤`. This is the
proper-subgroup irreducibility the orbit argument (`G0cyc_irreducible`) could not give — the genuine
cyclotomic case. -/
theorem G0pow_irreducible (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβspan : Submodule.span (ZMod p)
        (Set.range (fun k : ℕ => ((β : GaloisField p d)) ^ k)) = ⊤) :
    G₀Irreducible (G0pow hd β) := by
  intro W hWinv
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  refine Or.inr ?_
  obtain ⟨w₀, hw₀W, hw₀0⟩ := (Submodule.ne_bot_iff W).1 hWbot
  have hx₀0 : (efield hd).symm w₀ ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]; exact hw₀0
  set f : GaloisField p d →ₗ[ZMod p] (Fin d → ZMod p) :=
    (efield hd).toLinearMap ∘ₗ LinearMap.mulLeft (ZMod p) ((efield hd).symm w₀) with hfdef
  have hf_surj : Function.Surjective f := by
    intro z
    refine ⟨((efield hd).symm w₀)⁻¹ * (efield hd).symm z, ?_⟩
    simp only [hfdef, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
    rw [mul_inv_cancel_left₀ hx₀0, LinearEquiv.apply_symm_apply]
  have hfmem : ∀ y ∈ (f '' Set.range (fun k : ℕ => (β : GaloisField p d) ^ k)), y ∈ W := by
    rintro y ⟨c, ⟨k, rfl⟩, rfl⟩
    have hmem := hWinv (sigmaPow hd β ^ (k : ℤ))
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k) w₀ hw₀W
    rw [sigmaPow_zpow_apply, zpow_natCast, Units.val_pow_eq_pow_val] at hmem
    rw [hfdef]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
    rwa [mul_comm] at hmem
  rw [eq_top_iff]
  calc (⊤ : Submodule (ZMod p) (Fin d → ZMod p))
      = Submodule.map f ⊤ := by rw [Submodule.map_top, LinearMap.range_eq_top.2 hf_surj]
    _ = Submodule.map f (Submodule.span (ZMod p)
          (Set.range (fun k : ℕ => (β : GaloisField p d) ^ k))) := by rw [hβspan]
    _ = Submodule.span (ZMod p) (f '' Set.range (fun k : ℕ => (β : GaloisField p d) ^ k)) :=
        Submodule.map_span f _
    _ ≤ W := Submodule.span_le.2 hfmem

/-- **`G₀Irreducible (G0pow β)` from field-generation `Algebra.adjoin = ⊤`** (the clean hypothesis form). The
`F_p`-subalgebra generated by `β` is the span of its powers (`Algebra.adjoin_eq_span`), so `β` generating
`F_q` as an `F_p`-algebra is exactly `G0pow_irreducible`'s span hypothesis. This is the form a concrete witness
discharges (`β` a primitive/field-generating element). -/
theorem G0pow_irreducible_of_adjoin (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβ : Algebra.adjoin (ZMod p) {(β : GaloisField p d)} = ⊤) :
    G₀Irreducible (G0pow hd β) := by
  refine G0pow_irreducible hd β ?_
  have h1 := Algebra.adjoin_eq_span (ZMod p) ({(β : GaloisField p d)} : Set (GaloisField p d))
  rw [hβ, Algebra.top_toSubmodule] at h1
  rw [h1]
  congr 1
  ext x
  simp [Submonoid.mem_closure_singleton, Set.mem_range, eq_comm]

/-- **Field-generation from element order** (the finite-field core for cyclotomic witnesses). If `β ∈ F_qˣ`
has multiplicative order `r` and **no proper divisor** `e ∣ d` has `r ∣ p^e − 1`, then `β` generates `F_q`
as an `F_p`-algebra (`Algebra.adjoin = ⊤`). Proof: `K' := F_p⟮β⟯` is a subfield of size `p^e`
(`e := finrank ∣ d`) containing the order-`r` element `β`, so `β^(p^e) = β` ⟹ `r ∣ p^e − 1`; the hypothesis
forces `e = d`, hence `K' = ⊤`. Feeds `G0pow_irreducible_of_adjoin` for a concrete cyclotomic witness. -/
theorem adjoin_eq_top_of_orderOf (hd : d ≠ 0) (β : (GaloisField p d)ˣ) (r : ℕ)
    (hr : orderOf β = r)
    (hcop : ∀ e : ℕ, e ∣ d → e < d → ¬ r ∣ (p ^ e - 1)) :
    Algebra.adjoin (ZMod p) {(β : GaloisField p d)} = ⊤ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set K' : IntermediateField (ZMod p) (GaloisField p d) :=
    IntermediateField.adjoin (ZMod p) {(β : GaloisField p d)} with hK'def
  haveI : Fintype K' := Fintype.ofFinite _
  have hβmem : (β : GaloisField p d) ∈ K' := IntermediateField.mem_adjoin_simple_self _ _
  set e := Module.finrank (ZMod p) K' with hedef
  have hed : e ∣ d := by
    have h1 := IntermediateField.finrank_dvd_of_le_right (show K' ≤ ⊤ from le_top)
    rw [IntermediateField.finrank_top', GaloisField.finrank p hd] at h1
    exact h1
  have hcard : Fintype.card K' = p ^ e := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K'), ZMod.card, ← hedef]
  have hβ0 : (β : GaloisField p d) ≠ 0 := Units.ne_zero β
  have hpow : (β : GaloisField p d) ^ (p ^ e) = (β : GaloisField p d) := by
    have hb := FiniteField.pow_card (⟨(β : GaloisField p d), hβmem⟩ : K')
    rw [hcard] at hb
    have hb' := congrArg (fun x : K' => (x : GaloisField p d)) hb
    simpa using hb'
  have hpe1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hrdvd : r ∣ p ^ e - 1 := by
    rw [← hr, ← orderOf_units]
    apply orderOf_dvd_of_pow_eq_one
    have hmul : (β : GaloisField p d) * (β : GaloisField p d) ^ (p ^ e - 1)
        = (β : GaloisField p d) * 1 := by
      rw [mul_one, ← pow_succ', Nat.sub_add_cancel hpe1, hpow]
    exact mul_left_cancel₀ hβ0 hmul
  have hed2 : e = d :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hed)
      (Nat.not_lt.1 (fun h => hcop e hed h hrdvd))
  have hK'top : K' = ⊤ := by
    have hfr : Module.finrank (ZMod p) K' = Module.finrank (ZMod p) (GaloisField p d) := by
      rw [← hedef, hed2, GaloisField.finrank p hd]
    have h2 : K'.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hfr
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ K'.toSubmodule := by rw [h2]; exact Submodule.mem_top
    exact hx
  have hconv : K'.toSubalgebra = Algebra.adjoin (ZMod p) {(β : GaloisField p d)} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)
  rw [← hconv, hK'top, IntermediateField.top_toSubalgebra]

/-- The chosen generator `fqGen` has order `p^d − 1` (= `|F_qˣ|`), since it generates the cyclic unit group. -/
theorem orderOf_fqGen (hd : d ≠ 0) : orderOf (fqGen : (GaloisField p d)ˣ) = p ^ d - 1 := by
  haveI : DecidableEq (GaloisField p d) := Classical.decEq _
  rw [orderOf_eq_card_of_forall_mem_zpowers fqGen_spec, Nat.card_eq_fintype_card, Fintype.card_units]
  congr 1
  rw [← Nat.card_eq_fintype_card, GaloisField.card p d hd]

/-- **The cyclotomic witness family** — `G0pow (fqGen^m)` is irreducible whenever `β = fqGen^m` has order `r`
that field-generates (no proper divisor `e ∣ d` has `r ∣ p^e − 1`). Combines `G0pow_irreducible_of_adjoin`
with `adjoin_eq_top_of_orderOf`. For a *proper* `m` (so `⟨fqGen^m⟩ ⊊ F_qˣ`) this is the genuine rank-≥3
cyclotomic leak candidate (vs `G0cyc = G0pow fqGen` = rank-2 `K_q`). -/
theorem G0pow_pow_irreducible (hd : d ≠ 0) (m r : ℕ)
    (hr : orderOf ((fqGen : (GaloisField p d)ˣ) ^ m) = r)
    (hcop : ∀ e : ℕ, e ∣ d → e < d → ¬ r ∣ (p ^ e - 1)) :
    G₀Irreducible (G0pow hd ((fqGen : (GaloisField p d)ˣ) ^ m)) :=
  G0pow_irreducible_of_adjoin hd _ (adjoin_eq_top_of_orderOf hd _ r hr hcop)

/-! #### Separation obstruction — Frobenius is a configuration automorphism (the `Ĝ ⊋ G` gap, separation step 1)

The Frobenius permutation `frobPerm` of `V` (additive, the transported `frobCoord`) **preserves the scheme's
relation partition** (`relOfPair_frobPerm_hom`): it is an automorphism of the coherent configuration that the
group `V ⋊ G0pow β` does **not** realize. This is the concrete `Ĝ ⊋ G` separability gap — the obstruction the
`s(C)` leak would exploit — and the first step of the separation proof (a profile-twin can only be a Frobenius
image; a Γ-breaking base removes Frobenius symmetry; the remaining "all twins are Frobenius twins" is the open
crux, self-detection-plan §11.8). The mechanism: `frobCoord` **normalizes** `G0pow β`
(`frobCoord_conj_sigmaPow`: `frobCoord·σ·frobCoord⁻¹ = σ^p ∈ ⟨σ⟩`), and Frobenius is additive, so it carries
`G0pow β`-orbits of differences to `G0pow β`-orbits of differences. **General-theorem shadow:** "a normalizing
algebraic automorphism is a configuration automorphism," the exact shape of the general `s(C)` obstruction. -/

/-- `φ ∘ (mul β) ∘ φ⁻¹ = (mul β)^p` for an arbitrary unit `β` (generalizes `frobLinear_conj_mulUnit`). -/
theorem frobLinear_conj_mulUnit' (β : (GaloisField p d)ˣ) :
    frobLinear (p := p) (d := d) * mulUnitHom β * (frobLinear)⁻¹ = (mulUnitHom β) ^ p := by
  ext x
  have hinv : frobLinear (p := p) (d := d) ((frobLinear (p := p) (d := d))⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [← map_pow, mulUnitHom_apply, Units.val_pow_eq_pow_val, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, mulUnitHom_apply, frobLinear_mul, hinv]

/-- **`frobCoord` conjugates `σ_β` to `σ_β^p`** (generalizes `frobCoord_conj_sigmaCyc`) — so `frobCoord`
normalizes `G0pow β = ⟨σ_β⟩`. -/
theorem frobCoord_conj_sigmaPow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    frobCoord (p := p) hd * sigmaPow hd β * (frobCoord hd)⁻¹ = (sigmaPow hd β) ^ p := by
  rw [frobCoord, sigmaPow, ← map_inv, ← map_mul, ← map_mul, frobLinear_conj_mulUnit', map_pow]

/-- **`frobCoord` normalizes `G0pow β`** (forward inclusion): `g ∈ G0pow β ⟹ frobCoord·g·frobCoord⁻¹ ∈ G0pow β`.
From `frobCoord_conj_sigmaPow` (`σ ↦ σ^p`) and conjugation distributing over `zpow`. -/
theorem frobCoord_conj_mem_G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) {g}
    (hg : g ∈ G0pow hd β) : frobCoord hd * g * (frobCoord hd)⁻¹ ∈ G0pow hd β := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hconj : frobCoord hd * g * (frobCoord hd)⁻¹
      = (frobCoord hd * sigmaPow hd β * (frobCoord hd)⁻¹) ^ k := by
    rw [← hk, ← MulAut.conj_apply, ← MulAut.conj_apply, ← map_zpow]
  rw [hconj, frobCoord_conj_sigmaPow]
  exact Subgroup.zpow_mem _ (pow_mem (Subgroup.mem_zpowers _) p) k

/-- The **Frobenius permutation** of `V = F_p^d` — the additive automorphism `frobCoord` transported to
`Fin (p^d)` (linear part `frobCoord`, zero translation). -/
noncomputable def frobPerm (hd : d ≠ 0) : Equiv.Perm (Fin (p ^ d)) :=
  affinePermFin (frobCoord hd) 0

/-- The difference-coordinate of `frobPerm` is `frobCoord` of the coordinate (additive on differences). -/
theorem affineE_symm_frobPerm (hd : d ≠ 0) (x : Fin (p ^ d)) :
    affineE.symm (frobPerm hd x) = frobCoord hd (affineE.symm x) := by
  rw [frobPerm, affinePermFin_apply, add_zero, Equiv.symm_apply_apply]

/-- **The Frobenius permutation preserves the relation partition** (separation step 1, the configuration
automorphism). If `(x,y)` and `(x',y')` lie in the same relation, so do their `frobPerm`-images — because
`frobCoord` normalizes `G0pow β` and is additive. So `frobPerm` is an automorphism of the coherent
configuration not realized by `V ⋊ G0pow β` — the concrete `Ĝ ⊋ G` separability gap. -/
theorem relOfPair_frobPerm_hom (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd β) {x y x' y' : Fin (p ^ d)}
    (h : (affineScheme (G0pow hd β) hneg).relOfPair x y
        = (affineScheme (G0pow hd β) hneg).relOfPair x' y') :
    (affineScheme (G0pow hd β) hneg).relOfPair (frobPerm hd x) (frobPerm hd y)
      = (affineScheme (G0pow hd β) hneg).relOfPair (frobPerm hd x') (frobPerm hd y') := by
  rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff] at h ⊢
  obtain ⟨g₀, hg₀, hg⟩ := h
  refine ⟨frobCoord hd * g₀ * (frobCoord hd)⁻¹, frobCoord_conj_mem_G0pow hd β hg₀, ?_⟩
  have hinv : (frobCoord hd)⁻¹ (frobCoord hd (affineE.symm y' - affineE.symm x'))
      = affineE.symm y' - affineE.symm x' := by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [affineE_symm_frobPerm, affineE_symm_frobPerm, affineE_symm_frobPerm, affineE_symm_frobPerm,
    ← map_sub (frobCoord hd), ← map_sub (frobCoord hd), LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hinv, hg]

end CyclicAffine

/-! #### The concrete cyclotomic witness — `F₁₆`, the index-3 Clebsch family

`β = fqGen³` has multiplicative order `5` in `F₁₆ˣ` (order 15), so `⟨β⟩` is the **proper** index-3 subgroup
and `G0pow β` is a genuinely **primitive (rank ≥ 3), small, non-degenerate** affine scheme — the real F2b
leak candidate (NOT the rank-2 `K₁₆ = G0cyc`). Field-generation holds because `5 ∤ 2^e − 1` for the proper
divisors `e ∈ {1,2}` of `4` (so `β ∉ F₂, F₄`). This DEMONSTRATES the witness hypotheses are satisfiable —
the `G0pow`/`G0pow_irreducible` machinery is non-vacuous on a real cyclotomic scheme. (For `p = 2`,
symmetry `neg ∈ G0pow β` is free: `-1 = 1 ∈ ⟨β⟩`.) -/

/-- **The Clebsch witness is irreducible** (primitive). `β = fqGen³` (order 5) field-generates `F₁₆`. -/
theorem clebschWitness_irreducible :
    G₀Irreducible (G0pow (p := 2) (d := 4) (by norm_num) ((fqGen : (GaloisField 2 4)ˣ) ^ 3)) := by
  refine G0pow_pow_irreducible (by norm_num) 3 5 ?_ ?_
  · rw [orderOf_pow, orderOf_fqGen (by norm_num)]; decide
  · intro e he hlt; interval_cases e <;> revert he <;> decide

/-- Symmetry for the Clebsch witness — `neg ∈ G0pow β` (free in characteristic 2, `-1 = 1`). -/
theorem clebschWitness_neg_mem :
    LinearEquiv.neg (ZMod 2) ∈ G0pow (p := 2) (d := 4) (by norm_num) ((fqGen : (GaloisField 2 4)ˣ) ^ 3) := by
  refine neg_mem_G0pow (by norm_num) _ ?_
  have h : (-1 : (GaloisField 2 4)ˣ) = 1 := by
    rw [eq_comm, ← Units.val_inj]; simp [CharTwo.neg_eq]
  rw [h]; exact one_mem _

end ChainDescent
