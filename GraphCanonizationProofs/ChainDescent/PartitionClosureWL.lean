import ChainDescent.PartitionClosure
import ChainDescent.Refine

/-!
# FT1b — the 1-WL instance, and the NON-VACUITY gate (`docs/chain-descent-cao-propagation.md` §15.3)

`PartitionClosure.lean` proves the spine facts for **any** `IsRound`. That is worth nothing until
something is one. ⚠ Vacuity is this project's recurring failure mode, so the gate is discharged here,
against the **shipped** refiner rather than a model of it:

> **`isRound_refineRound`** — `Refine.refineRound adj`, the round the descent actually runs, is an
> `IsRound`. Both obligations come from `refineRound_eq_iff` + `sigKey_eq_iff`; the substantive one is
> **monotonicity**, which needs `signature_map_of_factor`: a coarser colouring's signature is the
> image of the finer one's under the factoring map, so signature equality survives coarsening.

And the payoff, which the project did not previously have in any form:

> **`warmRefineR_stable`** / **`refines_warmRefineR_of_stable`** — the shipped `Refine.warmRefineR` is
> **1-WL-stable**, and it is the **COARSEST** stable refinement of its input. Everything in the project
> up to now used `warmRefine`/`warmRefineR` only through *split-only* and *equivariance*; that it
> actually reaches a fixpoint, and which fixpoint, was never proved.

⟹ the spine facts (`closure_meet`, `closure_meet_comm`, `closure_defer`) transfer verbatim to the
shipped descent — `warmRefineR_eq_wl` is the bridge.

⚠ **Scope.** This is the `V = Fin n` instance only. FT2 supplies `V = Fin n × Fin n` (2-WL), where the
same file gives "the 2-WL closure" its first definition as a *function*.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace ChainDescent
namespace PartitionClosure

open ChainDescent.Refine (refineRound keyOf constP warmRefineR)

variable {n : Nat}

/-! ## 1. Signatures under a coarsening

The one genuinely new lemma. `Refines c d` factors as `d = g ∘ c` (`exists_factor`), and a signature is
a multiset whose *first* coordinate is the neighbour's colour — so the coarser signature is the `g`-image
of the finer one. Coarsening therefore cannot separate what the finer colouring merged. -/

/-- **A coarsening pushes signatures forward.** -/
theorem signature_map_of_factor (adj : AdjMatrix n) (P : PMatrix n) {c d : Colouring n}
    {g : Nat → Nat} (hg : ∀ x : Fin n, g (c x) = d x) (v : Fin n) :
    signature adj P d v = (signature adj P c v).map (fun t => (g t.1, t.2)) := by
  unfold signature
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun u _ => ?_)
  show (d u, adj.adj v u, P v u) = (g (c u), adj.adj v u, P v u)
  rw [hg u]

/-- **Equal signatures survive coarsening.** -/
theorem signature_eq_of_refines (adj : AdjMatrix n) (P : PMatrix n) {c d : Colouring n}
    (hcd : Refines c d) {v w : Fin n} (h : signature adj P c v = signature adj P c w) :
    signature adj P d v = signature adj P d w := by
  obtain ⟨g, hg⟩ := exists_factor hcd
  rw [signature_map_of_factor adj P hg v, signature_map_of_factor adj P hg w, h]

/-! ## 2. ★ THE NON-VACUITY GATE -/

/-- The round's partition, spelled out: equal rank ⟺ equal old colour ∧ equal signature. -/
theorem refineRound_eq_iff' (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    refineRound adj χ v = refineRound adj χ w ↔
      (χ v = χ w ∧ signature adj (constP n) χ v = signature adj (constP n) χ w) :=
  (Refine.refineRound_eq_iff adj χ v w).trans (sigKey_eq_iff adj (constP n) χ v w)

/-- **★★★ THE SHIPPED REFINER IS AN `IsRound`.** The non-vacuity gate for the whole of FT1.

`splits` is `Refine.refineRound_splits` verbatim. `mono` is the substantive half: a finer input gives
equal old colours **and** — by `signature_eq_of_refines` — equal signatures at the coarser colouring. -/
theorem isRound_refineRound (adj : AdjMatrix n) : IsRound (refineRound adj) where
  splits := fun χ x y h => Refine.refineRound_splits adj χ x y h
  mono := by
    intro c d hcd x y h
    obtain ⟨hcol, hsig⟩ := (refineRound_eq_iff' adj c x y).mp h
    exact (refineRound_eq_iff' adj d x y).mpr
      ⟨hcd x y hcol, signature_eq_of_refines adj (constP n) hcd hsig⟩

/-! ## 3. The bridge to the shipped warm refinement -/

/-- `wl` at the 1-WL round **is** `Refine.warmRefineR` — the iteration counts agree
(`Fintype.card (Fin n) = n`). -/
theorem warmRefineR_eq_wl (adj : AdjMatrix n) (χ : Colouring n) :
    warmRefineR adj χ = wl (refineRound adj) χ := by
  show (refineRound adj)^[n] χ = (refineRound adj)^[Fintype.card (Fin n)] χ
  rw [Fintype.card_fin]

/-- **★★ `warmRefineR` IS STABLE.** `n` rounds really do reach the 1-WL fixpoint — proved here for the
first time; the project previously used only *split-only* and *equivariance* of this object. -/
theorem warmRefineR_stable (adj : AdjMatrix n) (χ : Colouring n) :
    Stable (refineRound adj) (warmRefineR adj χ) := by
  simp only [warmRefineR_eq_wl]
  exact wl_stable (isRound_refineRound adj) χ

/-- **★★★ AND IT IS THE COARSEST ONE.** Any 1-WL-stable colouring refining `χ` refines
`warmRefineR adj χ` — the characterization that makes the warm partition canonical. -/
theorem refines_warmRefineR_of_stable (adj : AdjMatrix n) {s χ : Colouring n}
    (hs : Stable (refineRound adj) s) (h : Refines s χ) : Refines s (warmRefineR adj χ) := by
  simp only [warmRefineR_eq_wl]
  exact refines_wl_of_stable (isRound_refineRound adj) hs h

/-! ## 4. ★★★ The spine facts, at the shipped object

`ρ` is an arbitrary partition, so each of these covers individualizing a point, individualizing a set
pointwise, **and** splitting a cell off from everything but itself — see `PartitionClosure.Discretizes`
and `PartitionClosure.Splits`. -/

/-- **(K) at the shipped refiner** — *refining early changes nothing.* -/
theorem warmRefineR_meet (adj : AdjMatrix n) (χ ρ : Colouring n) :
    SamePart (warmRefineR adj (meet (warmRefineR adj χ) ρ)) (warmRefineR adj (meet χ ρ)) := by
  simp only [warmRefineR_eq_wl]
  exact closure_meet_meet (isRound_refineRound adj) χ ρ

/-- **★★★ ORDER-INDEPENDENCE AT THE SHIPPED REFINER.** Two individualization/split operations, with a
warm refinement between them, reach the same partition in either order. With `ρᵢ` singling out points
this is *"the cells depend only on the SET individualized"*; with either one a two-block partition it
is the same statement for a **cell split**; and it holds at **any** point of the descent. -/
theorem warmRefineR_meet_comm (adj : AdjMatrix n) (χ ρ₁ ρ₂ : Colouring n) :
    SamePart (warmRefineR adj (meet (warmRefineR adj (meet χ ρ₁)) ρ₂))
             (warmRefineR adj (meet (warmRefineR adj (meet χ ρ₂)) ρ₁)) := by
  simp only [warmRefineR_eq_wl]
  exact closure_meet_comm (isRound_refineRound adj) χ ρ₁ ρ₂

/-- The whole two-step sequence collapses to a single meet — no intermediate refinement is worth
anything beyond the final one. -/
theorem warmRefineR_collapse (adj : AdjMatrix n) (χ ρ₁ ρ₂ : Colouring n) :
    SamePart (warmRefineR adj (meet (warmRefineR adj (meet χ ρ₁)) ρ₂))
             (warmRefineR adj (meet (meet χ ρ₁) ρ₂)) := by
  simp only [warmRefineR_eq_wl]
  exact closure_collapse (isRound_refineRound adj) χ ρ₁ ρ₂

/-! ## 5. ⚠ Non-vacuity of the operation shapes

`Discretizes` and `Splits` are stated as specifications in `PartitionClosure`; at `V = Fin n` they are
**inhabited**, so the spine facts above are not statements about an empty class of `ρ`. -/

/-- Individualizing the points of `T`: distinct indices for `T`, one colour off it. -/
def ptsCol (T : Finset (Fin n)) : Colouring n := fun x => if x ∈ T then (x : Nat) + 1 else 0

theorem discretizes_ptsCol (T : Finset (Fin n)) : Discretizes (ptsCol T) T := by
  refine ⟨fun v hv u hu => ?_, fun x y hx hy => by simp [ptsCol, hx, hy]⟩
  simp only [ptsCol, if_pos hv]
  by_cases huT : u ∈ T
  · simp only [if_pos huT]
    exact fun he => hu (Fin.ext (by omega))
  · simp only [if_neg huT]
    omega

/-- Splitting `S` off from everything except itself — the "individualize a group" operation. -/
def blkCol (S : Finset (Fin n)) : Colouring n := fun x => if x ∈ S then 1 else 0

theorem splits_blkCol (S : Finset (Fin n)) : Splits (blkCol S) S :=
  ⟨fun x y hx hy => by simp [blkCol, hx, hy],
   fun x y hx hy => by simp [blkCol, hx, hy],
   fun x y hx hy => by simp [blkCol, hx, hy]⟩

/-- `indivOne` only splits — the left component of the meet. -/
theorem indivOne_refines (χ : Colouring n) (v : Fin n) : Refines (Descend.indivOne χ v) χ := by
  intro x y h
  unfold Descend.indivOne at h
  by_cases hx : x = v
  · by_cases hy : y = v
    · rw [hx, hy]
    · rw [if_pos hx, if_neg hy] at h; omega
  · by_cases hy : y = v
    · rw [if_neg hx, if_pos hy] at h; omega
    · rw [if_neg hx, if_neg hy] at h; omega

/-- ★ **The individualization the descent actually performs is a meet.** `Descend.indivOne χ v` — the
index-free `2·χ+1` parity trick — is the common refinement of `χ` with `ptsCol {v}`, so `indivOne` is
an instance of the `ρ` the spine facts quantify over, at **no** encoding cost. -/
theorem isMeet_indivOne (χ : Colouring n) (v : Fin n) :
    IsMeet (Descend.indivOne χ v) χ (ptsCol {v}) := by
  intro x y
  constructor
  · intro h
    refine ⟨indivOne_refines χ v x y h, ?_⟩
    have hiff : (x = v) ↔ (y = v) := by
      constructor
      · intro hx
        by_contra hy
        exact Descend.indivOne_singleton χ v y hy (by rw [← h, hx])
      · intro hy
        by_contra hx
        exact Descend.indivOne_singleton χ v x hx (by rw [h, hy])
    by_cases hx : x = v
    · have hy := hiff.mp hx
      simp [ptsCol, hx, hy]
    · have hy : y ≠ v := fun e => hx (hiff.mpr e)
      simp [ptsCol, hx, hy]
  · rintro ⟨hχ, hρ⟩
    by_cases hx : x = v
    · have hy : y = v := by
        by_contra hy
        simp [ptsCol, hx, hy] at hρ
      rw [hx, hy]
    · have hy : y ≠ v := by
        intro hy
        simp [ptsCol, hx, hy] at hρ
      exact (Descend.indivOne_refines_off χ v x y hx hy).mpr hχ

end PartitionClosure
end ChainDescent
