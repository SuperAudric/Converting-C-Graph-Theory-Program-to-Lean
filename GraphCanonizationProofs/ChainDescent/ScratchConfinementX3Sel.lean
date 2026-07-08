/-
# ScratchConfinementX3Sel.lean — W1: the equivariant cell selector (WIP, NOT in build.sh)

**Why this file.** The index-free descent (`ScratchConfinementX3Spine.oneStepSpineChain`) currently selects with
`pickOne` = the minimum-**index** non-singleton vertex. That selector does NOT give cross-graph cell correspondence:
for `H = π·G`, `pickOne`'s min-index vertex on `H` and the `π`-image of `G`'s can land in *different* cells, and no
automorphism reconciles picks from different cells. So `pickOne` cannot close ①b→ (the P3 note's "selector need not be
equivariant" is right only for the *within-graph* rep-swap, wrong for the cross-graph cell choice).

**The fix (W1).** Select the non-singleton cell whose **colour value** is minimal — an equivariant cell rule. The
index-free cut makes `warmRefine` transport *literally* (colour VALUES are preserved, not just the partition), so the
minimum non-singleton colour value is literally the same cross-graph and the selected **cell** is the exact `g`-image.
The rep *within* the cell (min index) still differs cross-graph — that difference is reconciled by confinement's
`SelectedCellIsOrbit` (W3), not by the selector.

**What W1 delivers:**
  · `selCell` — the minimum-value non-singleton cell — and its **cross-graph cell-transport** (`selCell_transport`):
    literal transport ⟹ `g u ∈ selCell χ₂ ↔ u ∈ selCell χ₁`. THE W1 CORE.
  · `selCellRep` — the single vertex the descent individualizes (min-index of `selCell`) — with the framework
    hypotheses `TargetsNonsingletonCell` / `NonemptyOnNonDiscrete` / `card ≤ 1`.
  · `selCellRep_both_in_target` — the W1→W3 handoff: cross-graph, `g (rep χ₁)` and `rep χ₂` lie in the SAME cell
    `selCell χ₂` (so confinement can reconcile them by an automorphism).

Termination is NOT `PartitionInvariant` (a value-based selector cannot be — `samePartition` colourings can put the
min value on different cells), so the `oneStepSpineChain_reaches_leaf` route through `SpineChain.eq_default` (which
needs PI) does not transfer. The growth argument (`defaultD_grows_if_not_leaf`) needs only `TargetsNonsingletonCell` +
`NonemptyOnNonDiscrete`, so termination is available by a DIRECT growth proof on the new-selector chain (W1-tail /
start of the re-instantiation) — provided/handled when the chain is re-instantiated with this selector.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3

namespace ChainDescent.ConfinementX3Sel

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.CanonSound

variable {n : Nat}

/-! ## The non-singleton colour values, and their literal cross-graph invariance -/

/-- The colour values that appear on a **non-singleton** cell of `χ` (a colour shared by ≥ 2 vertices). -/
def nonSingletonVals (χ : Colouring n) : Finset Nat :=
  (nonDiscreteSel χ).image χ

/-- Membership of `nonSingletonVals` in the clean "shared by two distinct vertices" form. -/
theorem mem_nonSingletonVals {χ : Colouring n} {c : Nat} :
    c ∈ nonSingletonVals χ ↔ ∃ v w : Fin n, v ≠ w ∧ χ v = c ∧ χ w = c := by
  simp only [nonSingletonVals, Finset.mem_image, nonDiscreteSel, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨u, hu, huv⟩, hvc⟩
    exact ⟨v, u, hu.symm, hvc, huv.trans hvc⟩
  · rintro ⟨v, w, hvw, hvc, hwc⟩
    exact ⟨v, ⟨w, hvw.symm, hwc.trans hvc.symm⟩, hvc⟩

/-- **The non-singleton colour values are literally invariant under a relabel.** If `χ₂` is the `g`-relabel of `χ₁`
(`∀ v, χ₂ (g v) = χ₁ v`), then `nonSingletonVals χ₂ = nonSingletonVals χ₁` — an equality of `Finset Nat`. This is
the crux the index-free cut buys: colour VALUES (not just the partition) transport, so the min-value cell is
well-defined cross-graph. -/
theorem nonSingletonVals_transport {g : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) : nonSingletonVals χ₂ = nonSingletonVals χ₁ := by
  ext c
  rw [mem_nonSingletonVals, mem_nonSingletonVals]
  constructor
  · rintro ⟨v, w, hvw, hvc, hwc⟩
    refine ⟨g.symm v, g.symm w, ?_, ?_, ?_⟩
    · exact fun h => hvw (g.symm.injective h)
    · rw [← hχ (g.symm v), Equiv.apply_symm_apply]; exact hvc
    · rw [← hχ (g.symm w), Equiv.apply_symm_apply]; exact hwc
  · rintro ⟨v, w, hvw, hvc, hwc⟩
    exact ⟨g v, g w, fun h => hvw (g.injective h), (hχ v).trans hvc, (hχ w).trans hwc⟩

/-! ## The selected (minimum-value non-singleton) cell -/

/-- The minimum non-singleton colour value of `χ` (junk `0` when `χ` is discrete). -/
noncomputable def minNSVal (χ : Colouring n) : Nat :=
  if h : (nonSingletonVals χ).Nonempty then (nonSingletonVals χ).min' h else 0

/-- **The selected cell** — the vertices of the minimum-value non-singleton cell (`∅` when discrete). -/
noncomputable def selCell (χ : Colouring n) : Finset (Fin n) :=
  if (nonSingletonVals χ).Nonempty then Finset.univ.filter (fun v => χ v = minNSVal χ) else ∅

/-- `minNSVal` is literally invariant under a relabel (from `nonSingletonVals_transport`). -/
theorem minNSVal_transport {g : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) : minNSVal χ₂ = minNSVal χ₁ := by
  simp only [minNSVal, nonSingletonVals_transport hχ]

/-- **★ W1 CORE — cross-graph cell transport.** For a relabel `g` (`χ₂` the `g`-relabel of `χ₁`), the selected cell
of `χ₂` is the exact `g`-image of that of `χ₁`: `g u ∈ selCell χ₂ ↔ u ∈ selCell χ₁`. Both the non-emptiness test
and the min value are literally invariant, and `χ₂ (g u) = χ₁ u`. -/
theorem selCell_transport {g : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (u : Fin n) :
    (g u ∈ selCell χ₂) ↔ (u ∈ selCell χ₁) := by
  simp only [selCell, nonSingletonVals_transport hχ]
  by_cases h : (nonSingletonVals χ₁).Nonempty
  · simp only [if_pos h, Finset.mem_filter, Finset.mem_univ, true_and, minNSVal_transport hχ, hχ u]
  · simp [if_neg h]

/-- `selCell` is non-empty exactly when `χ` is not discrete. Forward: a non-empty `selCell` witnesses a shared
colour. Backward: non-discrete ⟹ some non-singleton value ⟹ its cell is non-empty. -/
theorem selCell_nonempty_iff (χ : Colouring n) : (selCell χ).Nonempty ↔ ¬ Discrete χ := by
  constructor
  · rintro ⟨v, hv⟩
    simp only [selCell] at hv
    split at hv
    · rename_i h
      -- minNSVal is a member, so shared by two distinct vertices ⟹ not discrete
      have hmem : minNSVal χ ∈ nonSingletonVals χ := by
        simp only [minNSVal, dif_pos h]; exact (nonSingletonVals χ).min'_mem h
      obtain ⟨a, b, hab, hac, hbc⟩ := mem_nonSingletonVals.mp hmem
      intro hdisc; exact hab (hdisc a b (hac.trans hbc.symm))
    · exact absurd hv (Finset.notMem_empty v)
  · intro hnd
    have hne : (nonDiscreteSel χ).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (nonDiscreteSel_nonempty χ hnd)
    have hvals : (nonSingletonVals χ).Nonempty := hne.image χ
    have hmem : minNSVal χ ∈ nonSingletonVals χ := by
      simp only [minNSVal, dif_pos hvals]; exact (nonSingletonVals χ).min'_mem hvals
    obtain ⟨a, b, hab, hac, _⟩ := mem_nonSingletonVals.mp hmem
    refine ⟨a, ?_⟩
    simp only [selCell, if_pos hvals, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hac

/-- Every vertex of `selCell χ` lies in a non-singleton cell of `χ` (it shares its colour `minNSVal χ` with
another vertex). -/
theorem selCell_targets {χ : Colouring n} {v : Fin n} (hv : v ∈ selCell χ) :
    ∃ u, u ≠ v ∧ χ u = χ v := by
  simp only [selCell] at hv
  split at hv
  · rename_i h
    rw [Finset.mem_filter] at hv
    have hmem : minNSVal χ ∈ nonSingletonVals χ := by
      simp only [minNSVal, dif_pos h]; exact (nonSingletonVals χ).min'_mem h
    obtain ⟨a, b, hab, hac, hbc⟩ := mem_nonSingletonVals.mp hmem
    -- v has colour minNSVal; at least one of a,b differs from v.
    by_cases hva : a = v
    · exact ⟨b, by rw [hva] at hab; exact fun h => hab h.symm, by rw [hbc, ← hac, hva]⟩
    · exact ⟨a, hva, by rw [hac, ← hv.2]⟩
  · exact absurd hv (Finset.notMem_empty v)

/-! ## The single-vertex rep the descent individualizes -/

/-- **The descent selector** — the minimum-index vertex of the selected cell (a singleton, or `∅` when discrete).
This is what `oneStepSpineChain` individualizes one level at a time. Its *cell* is equivariant (`selCell_transport`);
its *rep* is not — the rep is reconciled by confinement (W3). -/
noncomputable def selCellRep (χ : Colouring n) : Finset (Fin n) :=
  if h : (selCell χ).Nonempty then {(selCell χ).min' h} else ∅

/-- `selCellRep` only ever picks a vertex in a non-singleton cell (framework hypothesis). -/
theorem selCellRep_targets : TargetsNonsingletonCell (selCellRep (n := n)) := by
  intro χ v hv
  simp only [selCellRep] at hv
  split at hv
  · rename_i h
    rw [Finset.mem_singleton] at hv; subst hv
    exact selCell_targets ((selCell χ).min'_mem h)
  · exact absurd hv (Finset.notMem_empty v)

/-- `selCellRep` is non-empty whenever `χ` is not discrete (framework hypothesis). -/
theorem selCellRep_nonempty : NonemptyOnNonDiscrete (selCellRep (n := n)) := by
  intro χ hχ
  have h : (selCell χ).Nonempty := (selCell_nonempty_iff χ).mpr hχ
  simp only [selCellRep, dif_pos h]
  exact Finset.singleton_ne_empty _

/-- `selCellRep` picks at most one vertex. -/
theorem selCellRep_card_le_one (χ : Colouring n) : (selCellRep χ).card ≤ 1 := by
  simp only [selCellRep]; split
  · simp
  · simp

/-- The rep is a member of the selected cell (when non-discrete). -/
theorem selCellRep_mem_selCell {χ : Colouring n} (h : (selCell χ).Nonempty) :
    ∀ v ∈ selCellRep χ, v ∈ selCell χ := by
  intro v hv
  simp only [selCellRep, dif_pos h, Finset.mem_singleton] at hv
  subst hv; exact (selCell χ).min'_mem h

/-! ## W1 → W3 handoff: the two competing reps land in the SAME target cell -/

/-- **★ W1→W3 handoff.** Cross-graph (`χ₂` the `g`-relabel of `χ₁`, both non-discrete), the `g`-image of `χ₁`'s rep
and `χ₂`'s own rep both lie in `selCell χ₂` — the same cell. So confinement's `SelectedCellIsOrbit` on `χ₂`'s
selected cell supplies the automorphism reconciling them (W3). The reps themselves need not coincide; only their
common cell matters. -/
theorem selCellRep_both_in_target {g : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) (h₁ : ¬ Discrete χ₁) (h₂ : ¬ Discrete χ₂)
    {v₁ v₂ : Fin n} (hv₁ : v₁ ∈ selCellRep χ₁) (hv₂ : v₂ ∈ selCellRep χ₂) :
    g v₁ ∈ selCell χ₂ ∧ v₂ ∈ selCell χ₂ := by
  have hc₁ : (selCell χ₁).Nonempty := (selCell_nonempty_iff χ₁).mpr h₁
  have hc₂ : (selCell χ₂).Nonempty := (selCell_nonempty_iff χ₂).mpr h₂
  refine ⟨?_, selCellRep_mem_selCell hc₂ v₂ hv₂⟩
  exact (selCell_transport hχ v₁).mpr (selCellRep_mem_selCell hc₁ v₁ hv₁)

end ChainDescent.ConfinementX3Sel
