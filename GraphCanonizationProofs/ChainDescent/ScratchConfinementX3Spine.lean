/-
# ScratchConfinementX3Spine.lean — the index-free single-vertex SpineChain (WIP, NOT in build.sh)

**Purpose (X3 step (i), the re-home).** `ScratchConfinementX3.lean` built the index-free descent as a raw
`descentColouring` fold with literal cross-graph transport (P1–P6). To make ①a/② transfer for free and keep the
runtime object *single*, the index-free descent should be a genuine `SpineChain` — not a parallel construction.

This module builds `oneStepSpineChain`: the `defaultSpineChain` analogue whose `IndivStep` at each level is the
**index-free single-vertex** `indivStepOne` (on the `pickOne` target) instead of the index-based `IndivStep.default`.

**Why it composes.**
  · `SpineChain`/`DescentTrace` are generic in the `IndivStep`; only `defaultTrace`/`defaultSpineChain` hardwire
    `IndivStep.default`. So swapping in `indivStepOne` is a legal chain.
  · `spine_branch_independent` ⟹ any two chains with the SAME `sel` share `D` + partition. So `oneStepSpineChain`
    (sel = `pickOne`, index-free) has the SAME `D`/leaf as `defaultSpineChain … pickOne` (index-BASED) — the
    partition is identical, only the colour *values* differ. Hence **termination transfers** from
    `defaultSpineChain_reaches_leaf` (via `pickOne`'s `TargetsNonsingletonCell`/`NonemptyOnNonDiscrete`, landed in
    `ScratchConfinementX3`), with NO re-proof of the growth argument.
  · The generic `CanonSound.canonForm_isLabelledAdj` (selector/seed-agnostic) then gives ①a on this chain, and its
    leaf colouring is index-free, so `canonForm` is the iso-invariant one the X3 transport lemmas talk about.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3

namespace ChainDescent.ConfinementX3Spine

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.CanonSound

variable {n : Nat}

/-! ## The index-free single-vertex IndivStep on the `pickOne` target -/

/-- **Index-free single-vertex `IndivStep` on `pickOne χ`.** When `pickOne χ = {r}` it is `indivStepOne r χ`
(the index-free `r ↦ 1`); when `pickOne χ = ∅` (discrete) it is the trivial `IndivStep.default χ ∅` (`= 2·χ`, also
index-free since no vertex is in `∅`). Either way it carries no `v.val`. -/
noncomputable def oneStepIndivStep (χ : Colouring n) : IndivStep χ (pickOne χ) := by
  unfold pickOne
  split
  · exact indivStepOne _ χ
  · exact IndivStep.default χ ∅

/-! ## The index-free chain (mirrors `defaultColouring`/`defaultD`/`defaultTrace`/`defaultSpineChain`) -/

/-- Index-free level-`k` colouring: individualize one `pickOne` vertex per level with `indivStepOne`. -/
noncomputable def oneStepColouring (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) :
    Nat → Colouring n
  | 0 => χι₀
  | k+1 =>
    let χι := oneStepColouring adj P₀ χι₀ k
    let π := warmRefine adj P₀ χι
    (oneStepIndivStep π).χ'

/-- Index-free level-`k` decision set: accumulate `pickOne` picks. -/
noncomputable def oneStepD (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) :
    Nat → Finset (Fin n)
  | 0 => ∅
  | k+1 =>
    let χι := oneStepColouring adj P₀ χι₀ k
    let π := warmRefine adj P₀ χι
    oneStepD adj P₀ χι₀ k ∪ pickOne π

/-- The concrete `DescentTrace` for the index-free construction (mirrors `defaultTrace`). -/
noncomputable def oneStepTrace (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) :
    (k : Nat) → DescentTrace adj P₀ χι₀ pickOne k
      (oneStepD adj P₀ χι₀ k) P₀ (oneStepColouring adj P₀ χι₀ k)
  | 0 => DescentTrace.zero
  | k+1 =>
    let prev := oneStepTrace adj P₀ χι₀ k
    let π := warmRefine adj P₀ (oneStepColouring adj P₀ χι₀ k)
    DescentTrace.succ prev (oneStepIndivStep π) P₀ (fun _ _ _ => rfl)

/-- **The index-free single-vertex spine chain.** Same shape as `defaultSpineChain` but index-free (`indivStepOne`)
and single-vertex (`sel = pickOne`). -/
noncomputable def oneStepSpineChain (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (k : Nat) :
    SpineChain adj P₀ χι₀ pickOne k where
  D := oneStepD adj P₀ χι₀ k
  P := P₀
  χι := oneStepColouring adj P₀ χι₀ k
  trace := oneStepTrace adj P₀ χι₀ k

/-! ## `pickOne` is partition-invariant, and termination transfers -/

/-- `pickOne` depends only on the partition (via `nonDiscreteSel`, which is partition-invariant, and `min'` of the
same set). So it is a legal spine selector for `spine_branch_independent`/`eq_default`. -/
theorem pickOne_partitionInvariant : PartitionInvariant (pickOne (n := n)) := by
  intro χ χ' h
  have hnd : nonDiscreteSel χ = nonDiscreteSel χ' := by
    ext v
    simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, huv⟩; exact ⟨u, hu, (h u v).mp huv⟩
    · rintro ⟨u, hu, huv⟩; exact ⟨u, hu, (h u v).mpr huv⟩
  unfold pickOne
  simp only [hnd]

/-- **Termination (X3 step (i)): the index-free descent reaches a leaf within `n` levels.** Transferred from
`defaultSpineChain_reaches_leaf` (same `sel = pickOne`, so `spine_branch_independent`/`eq_default` gives the SAME
partition ⟹ same `IsLeaf`), NO re-proof of the growth argument. -/
theorem oneStepSpineChain_reaches_leaf (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) :
    ∃ k ≤ n, (oneStepSpineChain adj P₀ χι₀ k).IsLeaf := by
  obtain ⟨k, hk, hleaf⟩ :=
    defaultSpineChain_reaches_leaf adj P₀ χι₀ pickOne_targets pickOne_nonempty
  refine ⟨k, hk, ?_⟩
  obtain ⟨_, hπ⟩ := SpineChain.eq_default pickOne_partitionInvariant (oneStepSpineChain adj P₀ χι₀ k)
  exact Discrete.of_samePartition hπ.symm hleaf

/-! ## ①a transfers for free (the payoff of SpineChain-ifying) -/

/-- `Nonempty (DirAssignment defaultP₀ …)` for the index-free chain — from `defaultP₀` antisymmetry, exactly as the
`canonForm` lex-min needs. -/
noncomputable instance oneStep_dirNonempty (adj : AdjMatrix n) (χι₀ : Colouring n) (k : Nat) :
    Nonempty (DirAssignment defaultP₀ (oneStepSpineChain adj defaultP₀ χι₀ k).D) :=
  ⟨DirAssignment.default defaultP₀_antisym⟩

/-- **①a on the index-free chain, for free.** The generic seed-agnostic `canonForm_isLabelledAdj` applies verbatim:
the index-free leaf `canonForm` is still a genuine relabelling `labelledAdj π adj`. Confirms the re-home costs nothing
for soundness — the whole point of building the index-free descent AS a `SpineChain` rather than a parallel object. -/
theorem oneStep_canonForm_isLabelledAdj (adj : AdjMatrix n) (χι₀ : Colouring n) (k : Nat)
    (isLeaf : (oneStepSpineChain adj defaultP₀ χι₀ k).IsLeaf) :
    ∃ π : Equiv.Perm (Fin n),
      canonForm (oneStepSpineChain adj defaultP₀ χι₀ k) isLeaf = labelledAdj π adj :=
  canonForm_isLabelledAdj _ _

end ChainDescent.ConfinementX3Spine
