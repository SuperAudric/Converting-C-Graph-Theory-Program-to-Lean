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

end ChainDescent
