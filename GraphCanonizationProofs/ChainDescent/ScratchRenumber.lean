/-
# ScratchRenumber.lean — the renumbering refinement primitive (D7 option ii) (WIP, NOT in build.sh)

The executable Tier-B finding (`ScratchExecutable.lean`): `#eval`-ing the leaf labelling hangs because
`refineStep = Encodable.encode (sigKey …)` compounds colour bit-size across rounds (encode∘encode∘…), so the
output's `vertexRank` `<`-comparisons are over astronomically long bignums. The fix (D7 option ii, also the
honest bit-cost): **renumber each round's colours to `0..n-1`**, breaking the compounding.

**The primitive here.** `refineStepR adj P χ = vertexRankNat (refineStep adj P χ)` — one refinement round, then
compress the colours to their **rank** `0..n-1`. `vertexRankNat` (Spine.lean) is order-preserving and injective
on distinct colours, so this is the order-preserving compression the cost-model doc §4 named — and it is
**exactly** the C#'s `cells → 0..k-1`.

**Why it transfers the whole spine for free (the key).** `refineStepR` satisfies the *same* partition
characterisation as `refineStep` — `refineStepR_iff` (same refined colour ⟺ same old colour ∧ same signature) —
and the spine's proofs use only that (`refineStep_iff`). So `refineStepR` induces the SAME partition
(`samePartition_refineStepR`), and colours stay `< n` (`refineStepR_lt`). The remaining executable work
(warmRefineR + the `samePartition` bridge to reuse `defaultSpineChain_reaches_leaf`, then rewire `canonOutput`)
drops onto this primitive — a NEXT increment; this file lands the primitive + its correctness.

Axiom target `[propext, Classical.choice, Quot.sound]`. Imports the Mathlib spine. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.Spine

namespace ChainDescent.Renumber

open ChainDescent

variable {n : Nat}

/-! ## `vertexRankNat` compression is a partition congruence -/

/-- `vertexRankNat` is strictly monotone in the colour value (re-derives the `private`
`Colouring.vertexRank_strict_mono` at the `Nat` level). -/
theorem rankNat_strict_mono {ψ : Colouring n} {v w : Fin n} (hvw : ψ v < ψ w) :
    Colouring.vertexRankNat ψ v < Colouring.vertexRankNat ψ w := by
  unfold Colouring.vertexRankNat
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 hvw⟩
  · have hvf : v ∈ Finset.univ.filter (fun u => ψ u < ψ w) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hvw⟩
    have hnotv : v ∉ Finset.univ.filter (fun u => ψ u < ψ v) := by
      rw [Finset.mem_filter]; intro hh; exact lt_irrefl _ hh.2
    exact hnotv (hsub hvf)

/-- **`vertexRankNat` preserves the partition**: two vertices share a rank iff they share a colour. (`←` the
filters coincide; `→` by strict monotonicity in both directions.) This is why rank-compression is a canonical
renumbering — same fibres, and (by monotonicity) same order. -/
theorem vertexRankNat_eq_iff {ψ : Colouring n} {v w : Fin n} :
    Colouring.vertexRankNat ψ v = Colouring.vertexRankNat ψ w ↔ ψ v = ψ w := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (Nat.ne_of_lt (rankNat_strict_mono hlt))
    · exact absurd h.symm (Nat.ne_of_lt (rankNat_strict_mono hgt))
  · intro h
    unfold Colouring.vertexRankNat
    rw [h]

/-! ## The renumbering refinement step -/

/-- **One renumbered refinement round.** Refine (`refineStep`), then compress the colours to their rank
`0..n-1` (`vertexRankNat`). The colours never blow up (`refineStepR_lt`), so iterating it stays `#eval`-feasible. -/
def refineStepR (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) : Colouring n :=
  fun v => Colouring.vertexRankNat (refineStep adj P χ) v

/-- **Colours stay `< n`** — the whole point: no cross-round bit-size blowup. -/
theorem refineStepR_lt (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) (v : Fin n) :
    refineStepR adj P χ v < n :=
  (Colouring.vertexRank (refineStep adj P χ) v).isLt

/-- **`refineStepR` has the SAME partition characterisation as `refineStep`** (same refined colour ⟺ same old
colour ∧ same signature). Since the spine's proofs use only this (`refineStep_iff`), everything transfers. -/
theorem refineStepR_iff (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) (v w : Fin n) :
    refineStepR adj P χ v = refineStepR adj P χ w ↔
      χ v = χ w ∧ signature adj P χ v = signature adj P χ w := by
  show Colouring.vertexRankNat (refineStep adj P χ) v
      = Colouring.vertexRankNat (refineStep adj P χ) w ↔ _
  rw [vertexRankNat_eq_iff]
  exact refineStep_iff adj P χ v w

/-- **`refineStepR` induces the SAME partition as `refineStep`** — one renumbered round is partition-equal to one
plain round. The bridge that lets `warmRefineR` reuse the spine's leaf-existence / direction-independence
(a NEXT increment iterates this through the rounds via the standard `samePartition` machinery). -/
theorem samePartition_refineStepR (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    samePartition (refineStepR adj P χ) (refineStep adj P χ) :=
  fun _ _ => vertexRankNat_eq_iff

end ChainDescent.Renumber
