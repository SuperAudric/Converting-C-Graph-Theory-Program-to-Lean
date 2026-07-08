/-
# ScratchConfinementX3Recon.lean — W3: the reconciling automorphism (WIP, NOT in build.sh)

**Goal (W3).** Produce the reconciling `H`-automorphism `b` that `ScratchConfinementX3.ifCanon_iso_invariant_of_reconcile`
takes as `hrec : picksH = (picksG.map π).map b`. With the **equivariant** cell selector (`selCell`, W1) and confinement
now stated over the **descent's own colouring** (`SelectedCellIsOrbit`, colouring-generalized in W2), the two descents'
selected cells correspond cross-graph and only their within-cell reps differ — reconciled per level.

**The construction (verified on paper; the genuine remaining content).** For `H = π·G`, run both descents with the
`selCell`-driven single-vertex selector. Maintain the invariant
  `I(k) : b_k ∈ Aut(H) ∧ ∀ j < k, b_k (π (picksG_j)) = picksH_j`.
At level `k`, the transport invariant makes `H`'s selected cell the `(b_k∘π)`-image of `G`'s (via
`descentColouring_transport` (P4) + `selCell_transport` (W1)), so `(b_k∘π)(picksG_k)` and `picksH_k` lie in one cell
= one `Stab(oneStepD_H k)`-orbit (confinement `SelectedCellIsOrbit`). That orbit gives `a_k ∈ Stab(oneStepD_H k)` with
`a_k((b_k∘π)(picksG_k)) = picksH_k`; set `b_{k+1} = a_k ∘ b_k`. Since every later `a_j (j>k)` fixes `oneStepD_H j ∋
picksH_k`, the FINAL `b = b_K` satisfies `b(π(picksG_j)) = picksH_j` for ALL `j` — exactly `hrec`. (This is why a
single global `b` works, reviving the "same-order-only" `ifCanon_iso_invariant_of_reconcile`: the cells correspond by
construction, so the orders correspond and the per-level `a_k`'s compose into one `b`.)

**This file, step by step.**
  · **W3a (this commit): the `selCell`-driven pick list + its `descentColouring`.** `descentPicks` generates the
    single-vertex picks (min of `selCell` at each warm-refined level); `descentColouring_descentPicks_cons` shows it
    folds through `descentColouring` exactly, so the `ifCanon` machinery (stated on `descentColouring`) speaks about it.
  · W3b: the generated picks reach a discrete leaf in ≤ n steps (the direct termination for `selCell`, non-PI so not
    transferred via `eq_default`).
  · W3c: the reconciliation induction producing `b` + `hrec` (the algebraic core).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Sel
import ChainDescent.ScratchConfinementWitt

namespace ChainDescent.ConfinementX3Recon

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Sel
open ChainDescent.CanonSound

variable {n : Nat}

/-! ## W3a — the `selCell`-driven pick list

Each descent step warm-refines, then individualizes the minimum-index vertex of the minimum-value non-singleton cell
(`selCell`). `descentPicks adj P fuel χ` is the list of picks the descent makes from seed `χ` with `fuel` steps of
headroom; the descent stops early (empty tail) when the warm-refined colouring is discrete. The recursion mirrors
`descentColouring`'s fold exactly (`descentStep adj P r χ = indivStep1 r (warmRefine adj P χ)`). -/

/-- The `selCell`-driven pick list from seed `χ`, with `fuel` steps of headroom. -/
noncomputable def descentPicks (adj : AdjMatrix n) (P : PMatrix n) :
    Nat → Colouring n → List (Fin n)
  | 0, _ => []
  | fuel + 1, χ =>
    let π := warmRefine adj P χ
    if h : (selCell π).Nonempty then
      let r := (selCell π).min' h
      r :: descentPicks adj P fuel (indivStep1 r π)
    else []

@[simp] theorem descentPicks_zero (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    descentPicks adj P 0 χ = [] := rfl

/-- One unfolding of `descentPicks` at a non-discrete step: the pick is `min (selCell (warmRefine … χ))`, and the tail
is the descent from the individualized colouring. -/
theorem descentPicks_succ_of_nonempty (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : (selCell (warmRefine adj P χ)).Nonempty) :
    descentPicks adj P (fuel + 1) χ
      = (selCell (warmRefine adj P χ)).min' h
        :: descentPicks adj P fuel (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ)) := by
  simp only [descentPicks, dif_pos h]

/-- At a discrete step the descent stops (no further picks). -/
theorem descentPicks_succ_of_empty (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : ¬ (selCell (warmRefine adj P χ)).Nonempty) :
    descentPicks adj P (fuel + 1) χ = [] := by
  simp only [descentPicks, dif_neg h]

/-- **The generated picks fold through `descentColouring` exactly.** `descentColouring adj P χ (descentPicks … χ)` is
the colouring the `selCell`-descent reaches — so the `ifCanon` transport lemmas (stated on `descentColouring`) speak
about the actual `selCell`-driven descent. The `cons` step matches because `descentStep adj P r χ = indivStep1 r
(warmRefine adj P χ)`, exactly the `descentPicks` recursion body. -/
theorem descentColouring_descentPicks_succ (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : (selCell (warmRefine adj P χ)).Nonempty) :
    descentColouring adj P χ (descentPicks adj P (fuel + 1) χ)
      = descentColouring adj P (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ))
          (descentPicks adj P fuel (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ))) := by
  rw [descentPicks_succ_of_nonempty adj P fuel χ h]
  rfl

/-! ## W3c core — the single-step reconciliation extension (the algebraic crux)

The reconciliation carries `hrec : picksH = picksG.map (fun x => b (g x))` — a SINGLE global `b`. The dead-end record
declared this "same-order only": a fixed `b` cannot track cells consumed in different orders. The revival: with the
equivariant cell selector the cells DO correspond, and the per-level reconcilers compose into one `b` precisely because
each new reconciler `aₖ ∈ Stab(prefix)` **fixes every earlier pick**. This lemma is that step: extend a length-`k`
reconciliation by one level, composing `aₖ` on the left. The `psH.map aₖ = psH` step (from `aₖ` fixing `psH`
pointwise) is what makes the accumulation preserve all earlier correspondences — the crux the single-`b` shape needs. -/

/-- **★ W3c — single-step reconciliation extension.** Given a length-`k` reconciliation `psH = psG.map (bₖ∘g)`, a new
reconciler `aₖ` that fixes every earlier `H`-pick (`hfix`, delivered by `aₖ ∈ Stab(psH.toFinset)` = confinement's
orbit automorphism), and the level-`k` match `aₖ (bₖ (g rG)) = rH`, the composed `aₖ * bₖ` reconciles the extended
lists. Front-to-back accumulation of this lemma over the descent yields the global `b` for
`ifCanon_iso_invariant_of_reconcile`'s `hrec`. -/
theorem reconcile_extend {g bk ak : Equiv.Perm (Fin n)}
    {psG psH : List (Fin n)} {rG rH : Fin n}
    (hstep : psH = psG.map (fun x => bk (g x)))
    (hfix : ∀ p ∈ psH, ak p = p)
    (hrH : ak (bk (g rG)) = rH) :
    psH ++ [rH] = (psG ++ [rG]).map (fun x => (ak * bk) (g x)) := by
  rw [List.map_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · -- earlier picks: `aₖ` fixes each `bₖ (g x) ∈ psH`, so the map is unchanged.
    conv_lhs => rw [hstep]
    refine List.map_congr_left (fun x hx => ?_)
    have hmem : bk (g x) ∈ psH := by
      rw [hstep]; exact List.mem_map_of_mem hx
    simp only [Equiv.Perm.mul_apply]
    exact (hfix _ hmem).symm
  · -- the new level: `aₖ (bₖ (g rG)) = rH`.
    simp only [List.map_cons, List.map_nil, Equiv.Perm.mul_apply, hrH]

end ChainDescent.ConfinementX3Recon
