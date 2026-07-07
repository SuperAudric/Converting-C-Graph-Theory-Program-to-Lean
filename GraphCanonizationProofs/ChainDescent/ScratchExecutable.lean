/-
# ScratchExecutable.lean — the executable track (Tier A + Tier B) (WIP, NOT in build.sh)

Home for "raise the Lean canonizer to executable form" (docs/chain-descent-executable-track.md).

**Tier A (DONE):** the per-node-capped *descent* is computable (`Decidable (Discrete)` replaced the `Classical`
`done`), so `descentResult`/`descentCost` `#eval`. The descent — find the leaf, count the cost — runs.

**Tier B (this file):** the *single-leaf labelling* is now computable too.
  · `rankInv` — a computable inverse of `vertexRank` (finite `List.find?` search), replacing the noncomputable
    `Equiv.ofBijective` in `rankPerm`; `rankInv_spec` proves it inverts `vertexRank` on discrete colourings.
  · `canonAdjComp adj χ` — the leaf's canonical adjacency, computed via `rankInv`; `canonAdjComp_eq` proves it
    equals the noncomputable spec `labelledAdj (rankPerm χ h) adj`, so it is a genuine relabelling.
  · `canonOutput` — wires it to the descent's returned leaf (NO `Classical.choose`): `some (canonAdjComp at the
    leaf)` or `none`. Computable + `#eval`-able; `canonOutput_sound` = ①a on this runnable output.

Still deferred: the lex-min over σ (Tier C — exponential enumeration or, poly, the orbit-pruned form = the wall).
`canonOutput` emits the leaf's *single* labelling (a valid relabelling), not yet the iso-invariant canonical min.
-/
import ChainDescent.ScratchCanonFormCapped

namespace ChainDescent.Executable

open ChainDescent
open ChainDescent.CanonSound
open ChainDescent.CanonForm
open ChainDescent.CostModel
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance

variable {n : Nat}

/-! ## Concrete tiny graphs (for `#eval`) -/

/-- The triangle `K₃`. -/
def triangle : AdjMatrix 3 := ⟨fun i j => if i = j then 0 else 1⟩

/-- The path `0–1–2`. -/
def path3 : AdjMatrix 3 := ⟨fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
                                         ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 else 0⟩

/-! ## Tier B, Piece 1 — a computable rank-permutation inverse -/

/-- `vertexRank χ` is bijective on a discrete colouring — re-derived from the (public) `rankPerm` Equiv, since
the library's `vertexRank_bijective` is `private`. -/
theorem vertexRank_bij (χ : Colouring n) (h : Discrete χ) :
    Function.Bijective (Colouring.vertexRank χ) := by
  have he : ⇑(Colouring.rankPerm χ h) = Colouring.vertexRank χ :=
    funext (fun v => Colouring.rankPerm_apply χ h v)
  rw [← he]; exact (Colouring.rankPerm χ h).bijective

/-- **Computable rank inverse (total).** The vertex of rank `i` under `χ`, found by a finite `List.find?` search
over `Fin n` (default `i` if none — unreachable on a discrete `χ`). Replaces the noncomputable `Equiv.ofBijective`
inverse in `rankPerm`. Total (no discreteness arg) so `canonAdjComp`/`canonOutput` stay total. -/
def rankInv (χ : Colouring n) (i : Fin n) : Fin n :=
  ((List.finRange n).find? (fun v => Colouring.vertexRank χ v == i)).getD i

/-- **`rankInv` inverts `vertexRank`** on a discrete colouring: `vertexRank χ (rankInv χ i) = i`. -/
theorem rankInv_spec (χ : Colouring n) (h : Discrete χ) (i : Fin n) :
    Colouring.vertexRank χ (rankInv χ i) = i := by
  obtain ⟨w, hw⟩ := (vertexRank_bij χ h).surjective i
  have hpw : (Colouring.vertexRank χ w == i) = true := by rw [hw]; exact beq_self_eq_true i
  cases hfind : (List.finRange n).find? (fun v => Colouring.vertexRank χ v == i) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd hpw (hfind w (List.mem_finRange w))
  | some v =>
    have hpv := List.find?_some hfind
    have hrv : rankInv χ i = v := by unfold rankInv; rw [hfind]; rfl
    rw [hrv]
    exact eq_of_beq hpv

/-- `rankInv` equals the noncomputable `rankPerm`'s inverse (on discrete `χ`). -/
theorem rankInv_eq_symm (χ : Colouring n) (h : Discrete χ) (i : Fin n) :
    (Colouring.rankPerm χ h).symm i = rankInv χ i := by
  rw [Equiv.symm_apply_eq, Colouring.rankPerm_apply]
  exact (rankInv_spec χ h i).symm

/-! ## Tier B, Piece 2 — the computable leaf labelling -/

/-- **Computable leaf canonical adjacency (total).** Relabel `adj` by the rank order of the colouring `χ`, using
the computable `rankInv`. -/
def canonAdjComp (adj : AdjMatrix n) (χ : Colouring n) : Fin n → Fin n → Nat :=
  fun i j => adj.adj (rankInv χ i) (rankInv χ j)

/-- **`canonAdjComp` is the noncomputable spec.** On a discrete colouring it equals `labelledAdj (rankPerm χ h) adj`
— so it is a genuine relabelling of `adj` (①a at the value level, computably). -/
theorem canonAdjComp_eq {adj : AdjMatrix n} {χ : Colouring n} (h : Discrete χ) :
    canonAdjComp adj χ = labelledAdj (Colouring.rankPerm χ h) adj := by
  funext i j
  show adj.adj (rankInv χ i) (rankInv χ j)
      = adj.adj ((Colouring.rankPerm χ h).symm i) ((Colouring.rankPerm χ h).symm j)
  rw [rankInv_eq_symm χ h i, rankInv_eq_symm χ h j]

/-- The colouring at the level-`k` default leaf (the chain's partition). -/
def leafColouring (adj : AdjMatrix n) (k : Nat) : Colouring n :=
  (defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k).partition

/-- When the descent flags a leaf at level `k`, that leaf's colouring is discrete. -/
theorem leaf_discrete (adj : AdjMatrix n) (k : Nat) (hk : descentResult adj = some k) :
    Discrete (leafColouring adj k) := by
  have hrun : ((spineCappedCanonizer adj defaultP₀ defaultχι₀ nonDiscreteSel).run n 0).1 = some k := hk
  have hdone := CappedCanonizer.done_of_run_some
    (spineCappedCanonizer adj defaultP₀ defaultχι₀ nonDiscreteSel) n 0 k hrun
  exact of_decide_eq_true hdone

/-- **The computable single-leaf canonizer** — run the descent (Tier A) to its leaf, emit `some (canonAdjComp at
that leaf)`, or `none` on a flag. NO `Classical.choose`: the leaf level is the descent loop's own returned value.
`#eval`-able. Emits the leaf's single labelling (a relabelling), not yet the iso-invariant lex-min (Tier C). -/
def canonOutput (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  (descentResult adj).map (fun k => canonAdjComp adj (leafColouring adj k))

/-- **①a on the runnable output.** A `some cG` answer of `canonOutput` is a genuine relabelling of `adj`. -/
theorem canonOutput_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonOutput adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  unfold canonOutput at h
  cases hd : descentResult adj with
  | none => rw [hd] at h; simp at h
  | some k =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hdisc := leaf_discrete adj k hd
    exact ⟨Colouring.rankPerm (leafColouring adj k) hdisc, by rw [← h]; exact canonAdjComp_eq hdisc⟩

/-! ## `#eval` — the descent runs (Tier A). Tier B's labelling is computable + proven, but see the note below. -/

-- Tier A: the descent runs (fast).
#eval descentResult triangle          -- some 1
#eval descentCost triangle            -- 27

/-! ### ★ FINDING (Tier B) — the colour blowup makes `#eval canonOutput` INFEASIBLE, confirming D7 renumbering.

`canonOutput`/`canonAdjComp` are *computable and proven sound* (`canonOutput_sound`), but `#eval`-ing them on a
concrete graph hangs: the leaf colouring's `Nat` values are `Encodable.encode` iterated across refinement rounds
(the §4 colour blowup), so `vertexRank`'s `χ u < χ v` comparisons are over astronomically large `Nat`s. This is
the D7 fork made concrete from the executable side — a *practical* run needs the **renumbering `refineStep`**
(cells → `0..k-1` each round, order-preserving ⟹ `canonAdjComp` unchanged). The theory (computable + ①a-sound) is
complete; the runnable demo of the labelling is deferred behind renumbering. -/

end ChainDescent.Executable
