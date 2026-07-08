/-
# ScratchConfinementP1.lean — the GRAPH SIDE of confinement-P1 (WIP, NOT in build.sh)

The confinement-P1 linchpin is **small-`Aut` residue ⟹ orbit-harvest ≤ `w` ⟹ does NOT flag** (route-c-plan §7c). The
*cost half* is on the spine (`ScratchCostModelSpine.not_flagsAt_of_base_le_spine`: `baseAt k ≤ baseMax n ⟹ flagsAt =
false`). This module supplies the **graph side**: the harvest base of a *small*-`Aut` node is `≤ baseMax n`.

The pure content is the classic **greedy base `≤ log₂|Aut|`** (`Cascade.exists_greedy_base_le_log`): a residual that is
small (`|Aut^P ∅| ≤ n`) has a base of length `≤ log₂|Aut| ≤ log₂ n = baseMax n`. Composed with the cost half, a
small-residual node provably does **not** flag — and the contrapositive is P1's largeness clause on the real descent:
**a Phase-1 flag ⟹ the node's residual `Aut` is large** (⟹ P2/P3 ⟹ primitive rank-3 / VT ⟹ assume-VT prune sound).

The two carried hypotheses of the spine assembly — the node's residual order `residualCard k` and the harvest-base
bound `baseAt k ≤ log₂(residualCard k)` — are the honest interface to the graph (the residue-at-node's `Aut`, and the
harvest algorithm's greedy-base property). Both are provided by `greedy_base_card_le_baseMax` at the object level.

Imports Cascade (`exists_greedy_base_le_log`) + the spine cost instance. Axiom target `[propext, Classical.choice,
Quot.sound]`. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.Cascade
import ChainDescent.ScratchCostModelSpine

namespace ChainDescent.ConfinementP1

open ChainDescent
open ChainDescent.CostModel.Oracle
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance

variable {n : Nat}

/-- **`baseMax` is `Nat.log 2`.** The oracle module defines `baseMax n = Nat.log2 n` (core-only purity); here it is
bridged to Mathlib's `Nat.log 2 n` (`Nat.log2_eq_log_two`) so the greedy-base bound composes. -/
theorem baseMax_eq_log_two (m : Nat) : baseMax m = Nat.log 2 m := by
  unfold baseMax; exact Nat.log2_eq_log_two

/-- **The graph side of P1 (pure content): a small-`Aut` node's greedy harvest base is `≤ baseMax n`.**
`exists_greedy_base_le_log` gives a base of length `≤ log₂|Aut^P ∅|`; if the residual order is small (`≤ n`), `log₂`
monotonicity + the `baseMax` bridge put that length `≤ baseMax n`. So a small-`Aut` node's harvest base fits the oracle
budget — the combinatorial half of confinement-P1. -/
theorem greedy_base_card_le_baseMax {adj : AdjMatrix n} {P : PMatrix n}
    (hsmall : Nat.card (StabilizerAt adj P ∅) ≤ n) :
    ∃ bs : List (Fin n),
      IsBase adj P (bs.foldl (fun s b => insert b s) ∅) ∧ bs.length ≤ baseMax n := by
  obtain ⟨bs, hbase, hlen⟩ := exists_greedy_base_le_log (adj := adj) (P := P)
  refine ⟨bs, hbase, ?_⟩
  calc bs.length ≤ Nat.log 2 (Nat.card (StabilizerAt adj P ∅)) := hlen
    _ ≤ Nat.log 2 n := Nat.log_mono_right hsmall
    _ = baseMax n := (baseMax_eq_log_two n).symm

/-- **P1 assembled on the real spine: a small-residual node does NOT flag.** Given (i) the harvest base at node `k`
is at most a greedy base of the node's residual (`baseAt k ≤ log₂(residualCard k)` — the harvest-algorithm property,
justified by `greedy_base_card_le_baseMax`) and (ii) the node's residual order is small (`residualCard k ≤ n`), the
node fits its budget and `flagsAt = false`. **Contrapositive = P1's largeness clause on the real descent: a Phase-1
flag ⟹ the node's residual `Aut` is large** — the confinement-P1 step the assume-VT prune rests on. -/
theorem not_flagsAt_of_smallAut_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt residualCard : Nat → Nat) (k : Nat)
    (hn : 1 ≤ n)
    (hbase : baseAt k ≤ Nat.log 2 (residualCard k))
    (hsmall : residualCard k ≤ n) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = false := by
  apply not_flagsAt_of_base_le_spine adj P₀ χι₀ sel baseAt k hn
  calc baseAt k ≤ Nat.log 2 (residualCard k) := hbase
    _ ≤ Nat.log 2 n := Nat.log_mono_right hsmall
    _ = baseMax n := (baseMax_eq_log_two n).symm

end ChainDescent.ConfinementP1
