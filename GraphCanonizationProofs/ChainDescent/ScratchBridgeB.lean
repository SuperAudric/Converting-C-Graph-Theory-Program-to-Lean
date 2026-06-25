/-
# B1a wrapping (step i) — connect the observable `jointIsoCount` to the Lemma-A `fullcount`.

The bridge's per-pair distinctness (`ScratchBridge.pairCount_ne_of_chiSep`) consumes a closed form for the joint
isotropic count `Z_w(S) = jointIsoCount Q w S`. `ScratchBridgeA.levelset_count_collapse` gives the closed form for the
Lemma-A **fullcount** (the count *including* `y = 0`). This module bridges the two: the observable `jointIsoCount`
(which excludes `w = u`, i.e. `y = 0` after the shift) equals the fullcount minus the `y=0` correction.

`fullcount_w(S) = jointIsoCount Q w S + [∀ t∈S, Q(t̄−w̄) = 0]`,

by composing the landed `ScratchCrux.jointIsoCount_eq_restricted` (`jointIsoCount = restricted` count, `w ≠ 0`) with
`ScratchLemmaB.cone_count_zero_split` (`fullcount = restricted + correction`). The correction indicator is itself a
Gram condition (`Q(t̄−w̄)=0 ∀t`), bounded by `1` — it becomes a constant shift in the per-pair closed form.

Remaining B1a wrap (after this): at `|S|=2`, feed `fullcount` through `reduction_to_levelset_nondeg`
(→ level-set count, nondeg config Gram) → `levelset_count_collapse` (→ `qᵈ + χ(D)·K·(q[c=0]−1)`); then the
`D ↔ pairForm`/`det G₂` identification (`χ(D) = χ(I_w(t))`) and assemble the per-point closed form
`Z_w·q³ = qᵈ + χ(I_w)·K·(q[c=0]−1) − q³·corr` that `pairCount_ne_of_chiSep` consumes. NOT in build (scratch;
`lake env lean`, after `lake build ChainDescent.ScratchCrux ChainDescent.ScratchLemmaB`).
-/
import ChainDescent.ScratchCrux
import ChainDescent.ScratchLemmaB

namespace ChainDescent

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **B1a wrap (i) — `fullcount = jointIsoCount + (y=0 correction)`.** The Lemma-A fullcount over `V`
(`#{y : Q y = 0 ∧ ∀ t∈S, Q(y−(t̄−ū)) = 0}`, the `reduction_to_levelset_nondeg` entry point) equals the observable
`jointIsoCount Q u S` (the same count restricted to `y ≠ 0`) plus the correction `[∀ t∈S, Q(t̄−ū)=0]`. Pure compose of
`cone_count_zero_split` (full = restricted + corr) and `jointIsoCount_eq_restricted` (jointIsoCount = restricted). -/
theorem fullcount_eq_jointIsoCount_add_corr (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (S : Finset (Fin (p ^ d))) (u : Fin (p ^ d)) :
    (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ t ∈ S, Q (y - (affineE.symm t - affineE.symm u)) = 0)).card
      = jointIsoCount Q u S
        + (if ∀ t ∈ S, Q (affineE.symm t - affineE.symm u) = 0 then 1 else 0) := by
  rw [cone_count_zero_split Q S u, ← jointIsoCount_eq_restricted]

end ChainDescent

#print axioms ChainDescent.fullcount_eq_jointIsoCount_add_corr
