import ChainDescent
import ChainDescent.CascadeOracle
import ChainDescent.Group
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-- **Soundness of the screen, modulo the D2 bridge.** If every non-trivial abelian residual the descent
reaches is recoverable (`hbridge` — the open `D2 ⟹ hwit` obligation, cascade-1b generalised), then
`Findable` implies the graph is `RecoverableByDepth`. The `recovered` case is free
(`Discrete ⟹ CellsAreOrbits`, `cellsAreOrbits_of_discrete`); the `step` case is the induction hypothesis
verbatim (`RecoverableByDepth` is a property of the whole graph, not of the node); the `abelian` case is
exactly where `hbridge` is consumed. A `Findable` derivation never using the `abelian` constructor (the
pure D1 leg) is therefore **unconditionally** recoverable — independently witnessed by
`recoverableByDepth_of_visiblyRecoverable`. -/
theorem recoverableByDepth_of_findable
    (hbridge : ∀ S : Finset (Fin n), ResidualAbelian adj P S → ¬ IsBase adj P S →
      ∃ b, RecoverableByDepth adj P b)
    {S : Finset (Fin n)} (h : Findable adj P S) :
    ∃ b, RecoverableByDepth adj P b := by
  induction h with
  | @recovered S hd => exact ⟨S.card, S, le_refl _, cellsAreOrbits_of_discrete hd⟩
  | @abelian S h1 h2 => exact hbridge S h1 h2
  | step _ _ ih => exact ih

end ChainDescent
