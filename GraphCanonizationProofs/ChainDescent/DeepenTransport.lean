import ChainDescent.DeepenSupply

/-!
# `C3b` tranche 2, part I — the deepening pipeline TRANSPORTS, except at the vertex pick

This file proves the unconditional half of `deepenSupply`'s ① story: **every stage of the deepening
pipeline is equivariant except the per-level vertex pick**, which isolates the whole ①c obligation to
exactly one line of `deepen` (`w :: _`).

## Why this is the right first increment

The route decision (remaining-work §1C C3 ii-c, 2026-07-20) is **(a)**: prove the emitted orbit
relation independent of the per-level selection rule. The crux of (a) is:

> `t` is a genuine automorphism, so it transports the canonical deepening from `r₁` to a valid
> deepening from `rⱼ`; **colours are preserved, so the cell-id sequence matches**, and the only gap
> is that replay picks a different member of the SAME cell.

The emphasised step is what this file proves, unconditionally — no hypothesis, no gate.
**`chooseIdK_transport` is the load-bearing one:** the chosen cell id is an *invariant* `Nat` (equal,
not conjugated), so the recorded id sequence is labelling-independent. That is what reduces the crux
to a statement about *which member of a fixed cell* is picked, rather than about the whole descent.

⚠ Lists here transport only **up to permutation** (`classOf` filters `List.finRange n` in index
order, which `σ` need not respect) — the `rails_perm_conj` lesson from `KernelTransport`. Membership,
length and `Nodup` are what the pipeline actually consumes, so those are the shapes proved.

**⚠⚠ HOW STRONG IS THE EVIDENCE, HONESTLY (measured 2026-07-20 — read before trusting it).**
The random-graph sweeps are **DEGENERATE and near-worthless**: at `n = 8` every generated graph has a
branch cell of size **0 or 2** (ZERO graphs with a cell ≥ 4). The reason is structural — **random
graphs are almost surely asymmetric**, so refinement discretizes them and an orbit-valued property has
nothing to bite on. So "400 random graphs, 302 firing" and "200 random graphs" mean much less than the
sample sizes suggest. **The real evidence is only the structured witnesses:** `G8` (cell 8, profile
`[2,2,2,2,4,4,4,4]` — the one RICH partially-firing case), `t3`/`wcyc9` `[3,3,3]`, `ut`
`[3,3,3,3,3,3]`, and `mp7` (cell 28 but fires TOTALLY, so it cannot falsify). That is ~4 useful
witnesses, one of them rich. **A proper search needs graphs WITH symmetry** — Cayley graphs, CFI/
multipede constructions, vertex-transitive families — not uniform random graphs.

## What is NOT here

The crux itself: `deepen` picks `w :: _`, the lowest-index member of the chosen sub-cell, and that
single choice does not transport. Everything else does. Evidence that the crux is nevertheless true
(no falsifier under two tie-break rules; 8 labellings × 4 partially-firing witnesses; 400 random
graphs of which 302 fire) is recorded in remaining-work §1C C3 (ii-c).
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Descend (transportColouring indivOne)

variable {n : Nat}

/-! ## 1. Pointwise transport -/

/-- The transported colouring agrees with the original after `σ`. -/
theorem transport_apply (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    transportColouring σ χ (σ v) = χ v := by
  show χ (σ.symm (σ v)) = χ v
  rw [Equiv.symm_apply_apply]

/-- …and at an arbitrary point, read through `σ.symm`. -/
theorem transport_apply' (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (u : Fin n) :
    transportColouring σ χ u = χ (σ.symm u) := rfl

/-! ## 2. Colour classes -/

theorem mem_classOf_iff (χ : Colouring n) (v u : Fin n) :
    u ∈ classOf χ v ↔ χ u = χ v := by
  unfold classOf
  simp [List.mem_filter, List.mem_finRange]

theorem classOf_nodup (χ : Colouring n) (v : Fin n) : (classOf χ v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange n)

/-- Membership in a colour class transports. -/
theorem mem_classOf_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v u : Fin n) :
    u ∈ classOf (transportColouring σ χ) (σ v) ↔ σ.symm u ∈ classOf χ v := by
  rw [mem_classOf_iff, mem_classOf_iff, transport_apply σ χ v, transport_apply' σ χ u]

/-- **The colour class transports up to permutation** (not equality — index order). -/
theorem classOf_perm_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    (classOf (transportColouring σ χ) (σ v)).Perm ((classOf χ v).map σ) := by
  apply (List.perm_ext_iff_of_nodup (classOf_nodup _ _)
    (List.Nodup.map σ.injective (classOf_nodup _ _))).mpr
  intro u
  rw [mem_classOf_transport σ χ v u, List.mem_map]
  constructor
  · intro h; exact ⟨σ.symm u, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- **Class SIZE is invariant** — this is what the gates read. -/
theorem classOf_length_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    (classOf (transportColouring σ χ) (σ v)).length = (classOf χ v).length := by
  rw [(classOf_perm_transport σ χ v).length_eq, List.length_map]

/-! ## 3. The coupled component -/

theorem mem_coupled_iff (χp χc : Colouring n) (v : Fin n) :
    v ∈ coupled χp χc ↔
      (((List.finRange n).filter (fun u => χp u == χp v)).map χc).dedup.length > 1 := by
  unfold coupled
  simp [List.mem_filter, List.mem_finRange]

/-- The parent-cell-of-`v` list transports up to permutation. -/
theorem parentCell_perm_transport (σ : Equiv.Perm (Fin n)) (χp : Colouring n) (v : Fin n) :
    ((List.finRange n).filter
        (fun u => transportColouring σ χp u == transportColouring σ χp (σ v))).Perm
      (((List.finRange n).filter (fun u => χp u == χp v)).map σ) := by
  apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))
    (List.Nodup.map σ.injective (List.Nodup.filter _ (List.nodup_finRange n)))).mpr
  intro u
  simp only [List.mem_filter, List.mem_finRange, true_and, beq_iff_eq, List.mem_map]
  rw [transport_apply σ χp v, transport_apply' σ χp u]
  constructor
  · intro h; exact ⟨σ.symm u, by simpa using h, by simp⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- **Membership in the coupled component transports.** -/
theorem mem_coupled_transport (σ : Equiv.Perm (Fin n)) (χp χc : Colouring n) (v : Fin n) :
    (σ v) ∈ coupled (transportColouring σ χp) (transportColouring σ χc) ↔ v ∈ coupled χp χc := by
  rw [mem_coupled_iff, mem_coupled_iff]
  have hmap :
      (((List.finRange n).filter
          (fun u => transportColouring σ χp u == transportColouring σ χp (σ v))).map
        (transportColouring σ χc)).Perm
      (((List.finRange n).filter (fun u => χp u == χp v)).map χc) := by
    have h1 := (parentCell_perm_transport σ χp v).map (transportColouring σ χc)
    refine h1.trans ?_
    rw [List.map_map]
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro x _
    show transportColouring σ χc (σ x) = χc x
    exact transport_apply σ χc x
  rw [hmap.dedup.length_eq]

/-! ## 4. The gates — invariant `Bool` and invariant `Nat` -/

/-- The all-singletons gate is invariant, given a coupled component transported up to `σ`. -/
theorem allSingletonsK_transport (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (K : List (Fin n)) :
    allSingletonsK (K.map σ) (transportColouring σ χc) = allSingletonsK K χc := by
  unfold allSingletonsK
  induction K with
  | nil => rfl
  | cons a K ih =>
      simp only [List.map_cons, List.all_cons, ih, classOf_length_transport σ χc a]

/-- **★ THE LOAD-BEARING LEMMA — the chosen cell id is an INVARIANT `Nat`.**
Not conjugated: *equal*. So the id sequence `deepen` records is labelling-independent, which is
exactly what reduces the route-(a) crux to "which member of a fixed cell does replay pick?". -/
theorem chooseIdK_transport (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (K : List (Fin n)) :
    chooseIdK (K.map σ) (transportColouring σ χc) = chooseIdK K χc := by
  unfold chooseIdK
  have key : ∀ (L : List (Fin n)) (acc : Option Nat),
      ((L.map σ).filter
          (fun v => decide ((classOf (transportColouring σ χc) v).length ≥ 2))).foldl
        (fun acc v => match acc with
          | none => some (transportColouring σ χc v)
          | some m => some (min m (transportColouring σ χc v))) acc
      = (L.filter (fun v => decide ((classOf χc v).length ≥ 2))).foldl
        (fun acc v => match acc with
          | none => some (χc v)
          | some m => some (min m (χc v))) acc := by
    intro L
    induction L with
    | nil => intro acc; rfl
    | cons a L ih =>
        intro acc
        have hp : (decide ((classOf (transportColouring σ χc) (σ a)).length ≥ 2))
            = decide ((classOf χc a).length ≥ 2) := by
          rw [classOf_length_transport σ χc a]
        simp only [List.map_cons, List.filter_cons, hp]
        by_cases h : decide ((classOf χc a).length ≥ 2) = true
        · simp only [h, if_true, List.foldl_cons, transport_apply σ χc a]
          exact ih _
        · simp only [Bool.not_eq_true] at h
          simp only [h, if_false]
          exact ih acc
  exact key K none

/-! ## 5. One deepening step -/

/-- **The individualize+refine step transports.** -/
theorem step_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)).col
      = transportColouring σ ((step adj χ v).col) := by
  unfold step
  rw [Refine.warmRefineVec_col_eq, Refine.warmRefineVec_col_eq,
      Descend.indivOne_transport σ χ v]
  exact Refine.refineEquivariant_encodeFree σ adj (indivOne χ v)

end Deepen
end ChainDescent
