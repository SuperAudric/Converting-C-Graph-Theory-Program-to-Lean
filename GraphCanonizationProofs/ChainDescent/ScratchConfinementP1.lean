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

/-- **`log₂ ≤ baseMax`.** The oracle threshold is `baseMax m = (Nat.log2 m)² = (Nat.log 2 m)²` (superlogarithmic,
the 2026-07-08 threshold decision), and `log₂ m ≤ (log₂ m)²` always (`Nat.le_self_pow`, `2 ≠ 0`). So a greedy base
of length `≤ log₂|Aut| ≤ log₂ n` still fits under `baseMax n` — the P1 graph-side survives the threshold raise
(it now needs only `≤`, not `=`). -/
theorem log_two_le_baseMax (m : Nat) : Nat.log 2 m ≤ baseMax m := by
  unfold baseMax
  rw [Nat.log2_eq_log_two]
  exact Nat.le_self_pow (by norm_num) _

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
    _ ≤ baseMax n := log_two_le_baseMax n

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
    _ ≤ baseMax n := log_two_le_baseMax n

/-! ## The residue-at-node concrete definitions — the last P1 seam

`flag_imp_large` (in `ScratchConfinement.lean`) carries the harvest base `baseAt` and the residual order
`residualCard` as *abstract* functions plus a greedy hypothesis `hgreedy`. This section gives them concrete
definitions on the real default spine and turns `hgreedy` into a theorem, so the confinement interface is fed by
the actual descent, not a guessed shape.

The level-`k` residue is `(adj, P₀)` with the spine's accumulated prefix `D_k = (defaultSpineChain … k).D`
individualized; its automorphism group is the pointed stabilizer `StabilizerAt adj P₀ D_k`, and a greedy base
*extending* `D_k` (from `exists_greedy_base_aux`, the pointed form of `exists_greedy_base_le_log`) has length
`≤ log₂ |StabilizerAt adj P₀ D_k|`. -/

/-- **The level-`k` residue's `Aut` order** — `|StabilizerAt adj P₀ D_k|`, the residual automorphism group after
the default spine individualizes its level-`k` prefix. This is the concrete `residualCard`: "`n < spineResidualCard
k`" is exactly "the node-`k` residue has large `Aut`" (the largeness clause P3 consumes). -/
noncomputable def spineResidualCard (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) : Nat :=
  Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
    (defaultSpineChain adj P₀ χι₀ sel k).D)

/-- **The level-`k` harvest base length** — how many extra individualizations a greedy base needs to discretize
the level-`k` residue (a base *extending* the prefix `D_k`), via `exists_greedy_base_aux`. This is the concrete
`baseAt` fed to `spineCappedCanonizerO`'s per-node harvest cost `oracleCost n (baseAt k) = n^(baseAt k)` (the
D7-declared model: harvest at base `b` explores ≤ `n^b` maps; any greedy base bounds it). Noncomputable (greedy
choice) — the cost model is a proof artifact; the executable track is separate. -/
noncomputable def spineBaseAt (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) : Nat :=
  (Classical.choose (exists_greedy_base_aux (adj := adj)
    (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
    (Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D))
    (defaultSpineChain adj P₀ χι₀ sel k).D le_rfl)).length

/-- **The greedy property, now a THEOREM (discharges the confinement interface's `hgreedy`).** On the concrete
spine functions the harvest base is at most `log₂` of the residual `Aut` — `spineBaseAt k ≤ log₂ (spineResidualCard
k)` — from `exists_greedy_base_aux`'s `2^|bs| ≤ |StabilizerAt … D_k|`. So `flag_imp_large`'s carried greedy
hypothesis holds by construction on the real descent; nothing is left abstract in P1's largeness half. -/
theorem spineBaseAt_le_log (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) :
    spineBaseAt adj P₀ χι₀ sel k ≤ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) := by
  have hspec := Classical.choose_spec (exists_greedy_base_aux (adj := adj)
    (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
    (Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D))
    (defaultSpineChain adj P₀ χι₀ sel k).D le_rfl)
  have h2 : 2 ^ spineBaseAt adj P₀ χι₀ sel k ≤ spineResidualCard adj P₀ χι₀ sel k := hspec.2
  exact Nat.le_log_of_pow_le (by norm_num) h2

end ChainDescent.ConfinementP1
