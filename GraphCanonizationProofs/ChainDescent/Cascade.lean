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

end ChainDescent
