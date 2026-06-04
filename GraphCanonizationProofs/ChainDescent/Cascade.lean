import ChainDescent
import ChainDescent.CascadeOracle
import ChainDescent.Group
import ChainDescent.Saturation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite

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

end ChainDescent
