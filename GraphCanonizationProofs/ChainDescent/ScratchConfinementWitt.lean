/-
# ScratchConfinementWitt.lean — the Witt step: `PrimRank3Classical ⟹ FrameSelectorTransitive` (WIP, NOT in build.sh)

**Context (route-c-plan §7c, the P3→P4 Witt bridge).** The confinement assembly's `hWitt` obligation is
`PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel S` — "a Cameron/classical residue's residual group is
transitive on the selected cell at every prefix." The §7c DECISION carries Witt as a **scoped citation**
(`Publication.lean witt_flag_transitivity`, Artin *Geometric Algebra*). This module gives that citation a concrete,
faithful shape and proves the genuine reduction around it.

**The factoring — a real reduction + one clean citation (mirrors P3's pattern):**
  · **`WittCellTransitive`** (HERE) — the honest citation shape: at every prefix `T ⊇ S₀` the residual group is
    **transitive on the selected (isotropic-point) cell** (any two cell vertices are `Stab(T)`-orbit-equivalent).
    This is Witt's theorem for the forms-graph residue (`O(Q)` transitive on isometric isotropic points fixing an
    isotropic frame `T`). It is **distinct** from the conclusion `FrameSelectorTransitive` (the ∃-representative-
    covering form), so the citation is not the conclusion in disguise.
  · **`frameSelectorTransitive_of_wittCellTransitive`** (HERE, PROVED) — the reduction: cell-transitivity ⟹ the
    ∃-representative-covering form P4 consumes. Non-trivial (a nonempty/empty cell case split): if the cell is
    nonempty pick any cell element as the frame origin `r` and cell-transitivity covers it; if empty, any vertex
    works vacuously. This is the provable content the Witt step adds.
  · **The carried citation** `hCitation : PrimRank3Classical k → WittCellTransitive adj P₀ sel S` = Liebeck
    (Cameron ⟹ classical forms) + Witt (classical forms ⟹ cell-transitive). This is the concrete referent for
    `Publication.witt_flag_transitivity`.

**Deliverable:** `confinement_selectedCellIsOrbit_spine_witt` — the confinement lemma on the real spine carrying
**only named external results**: `hClassify` (G3 at `confinementLargeScheme`), the model `M` (= D0 non-schurian
flag), primitivity `hprim` (= `hImprim`), and `hCitation` (Witt + Liebeck). Everything else — P1, P2, P3's
composition, the strong-threshold largeness (discharged), the Witt reduction, P4's producer — is proved.

Imports `ScratchConfinementP3`. Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in
`build.sh`.
-/
import ChainDescent.ScratchConfinementP3

namespace ChainDescent.ConfinementWitt

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.ConfinementP3
open ChainDescent.Confinement
open ChainDescent.NodeCountBridge
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **Witt cell-transitivity (the honest citation shape).** At every prefix `T ⊇ S₀`, the residual group is
transitive on the selected cell: any two cell vertices are `Stab(T)`-orbit-equivalent (`OrbitPartition`). This is
Witt's theorem for the forms-graph residue — `O(Q)` acts transitively on the isometric isotropic points after
fixing an isotropic frame `T`. Deliberately **distinct** from `FrameSelectorTransitive` (the ∃-frame-origin form);
the reduction below derives that from this. -/
def WittCellTransitive (adj : AdjMatrix n) (P₀ : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S₀ : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), S₀ ⊆ T →
    ∀ v w, v ∈ sel (χsel T) →
      w ∈ sel (χsel T) →
      OrbitPartition adj P₀ T v w

/-- **The Witt reduction (PROVED): cell-transitivity ⟹ `FrameSelectorTransitive`.** Per prefix `T`, produce a
frame origin `r` whose `Stab(T)`-orbit covers the selected cell. If the cell is nonempty, take `r` to be any cell
element — cell-transitivity gives `OrbitPartition r w` for every cell `w`. If it is empty, any vertex `r` works
(the covering condition is vacuous). Needs `Nonempty (Fin n)` for the empty-cell fallback. This is the genuine
group-action content the Witt step contributes on top of the citation. -/
theorem frameSelectorTransitive_of_wittCellTransitive [Nonempty (Fin n)]
    {adj : AdjMatrix n} {P₀ : PMatrix n} {sel : Colouring n → Finset (Fin n)}
    {χsel : Finset (Fin n) → Colouring n} {S₀ : Finset (Fin n)}
    (h : WittCellTransitive adj P₀ sel χsel S₀) :
    FrameSelectorTransitive adj P₀ sel χsel S₀ := by
  intro T hT
  by_cases hne : (sel (χsel T)).Nonempty
  · obtain ⟨r, hr⟩ := hne
    exact ⟨r, fun w hw => h T hT r w hr hw⟩
  · obtain ⟨r⟩ := ‹Nonempty (Fin n)›
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨r, fun w hw => ?_⟩
    rw [hne] at hw
    simp at hw

/-! ## The confinement lemma carrying ONLY named external results

`confinement_selectedCellIsOrbit_spine_P3_discharged` (P3, largeness bridge already discharged) needs `hWitt :
PrimRank3Classical k → FrameSelectorTransitive`. Supplying it via the Witt reduction leaves only the four named
citations. -/

/-- **★ Confinement on the real spine, reduced to named citations only.** A Phase-1 flag at node `k` ⟹ the target
cell at prefix `S` is one `Stab(S)`-orbit, carrying **only**: `hClassify` (G3 at the super-poly
`confinementLargeScheme`), the residue-scheme model `M` (the `SchurianScheme` gap = D0 non-schurian flag),
primitivity `hprim` (= `hImprim`), and `hCitation` (Witt + Liebeck = `Publication.witt_flag_transitivity`).
Everything else — P1 (super-poly threshold), P2 (deferral), P3's seal composition, the discharged largeness bridge,
the Witt reduction, P4's producer — is **proved** axiom-clean. This is the whole non-rigid confinement lemma
reduced to its trusted base. -/
theorem confinement_selectedCellIsOrbit_spine_witt (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hCitation : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact confinement_selectedCellIsOrbit_spine_P3_discharged adj P₀ χι₀ sel χsel S k hn hClassify M hprim
    (fun h => frameSelectorTransitive_of_wittCellTransitive (hCitation h)) hflag

end ChainDescent.ConfinementWitt
