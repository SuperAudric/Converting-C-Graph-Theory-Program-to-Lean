/-
# ScratchConfinementCellModel.lean — Option A: the FAITHFUL residue scheme on the SELECTED CELL (WIP, NOT in build.sh)

**Why the cell, not the complement (the corrected object).** `PrimitiveCCClassification` (`Scheme.lean:4026`) classifies
a **transitive** `SchurianScheme` (`IsPreprimitive` on `Fin m`). The residual group `StabilizerAt adj P T` is transitive
on a colour class (Witt / `FrameSelectorTransitive`) but NOT across the complement's several classes (Clebsch witness),
so the transitive object G3 classifies is the **selected cell** `C = sel (χsel T)`, not the whole complement. This file
models the residue on `C`.

**The one carried hypothesis (the plan, not a fallback).** `R := StabilizerAt adj P T` fixes `T` pointwise and, being
automorphisms of a colour-invariant colouring, fixes each colour class `C` SETWISE (`CellInvariant`, dischargeable from
warmRefine iso-invariance + `FixesPointwise T`). `R` acts on `C`; the count `|SchemeAutGroup(C-scheme)| = |R_C| = |R|/|K|`
(`K` = kernel of the cell action). The bridge to `spineResidualCard = |R|` needs `K = 1` (**`CellActionFaithful`**) — the
documented model-faithfulness gap, RELOCATED to one clean, family-dischargeable hypothesis: for the forms/Cameron family
it is TRUE and backed by `isotropic_span` (`NullstellensatzStructural.lean:166` — an isometry fixing the cell's spanning
isotropic points is the identity). We CARRY it; discharging per-family is downstream. If this route stalls, RE-CUT the
decomposition (the accepted fallback), never drop to an unfaithful model.

**Structure (mirrors `ScratchConfinementResidual`'s complement machinery with `x ∈ C`, `R` fixing `C` setwise):**
  · `CellInvariant` / `cellRestrict` / `cellRestrictHom` — restrict a residual automorphism to `Perm {x // x ∈ C}`.
  · `CellActionFaithful` — the carried `K = 1` hypothesis (faithfulness of the cell action).
  · `cellCard` / `cellEquivFin` / `cellGroupFin` — promote `{x // x ∈ C} ≃ Fin m` + transport the range.
  · `cellGroupFin_card` — **under faithfulness** `|cellGroupFin| = |StabilizerAt adj P T|` (= `spineResidualCard` when
    `T` is the spine base `D_k`).
  · `cellRange_pretransitive` / `cellGroupFin_pretransitive` — transitivity from a pairwise `htrans` (supplied by Witt).
  · `CellSchemeModel` + `cellSchemeModel_of_group` — the faithful model on `Fin (cellCard C)`.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementSchurianModel
import ChainDescent.ScratchConfinementP4
import ChainDescent.ScratchConfinementX3Sel

namespace ChainDescent.ConfinementCellModel

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementX3Sel

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}

/-- **The residual group fixes the cell setwise.** `R := StabilizerAt adj P T` consists of automorphisms of a
colour-invariant colouring, so each colour class `C` is mapped to itself: `x ∈ C ↔ g x ∈ C`. Carried as a predicate
(dischargeable from warmRefine iso-invariance + `FixesPointwise T`), it is the analogue of the complement's free
`residual_pred`. -/
def CellInvariant (adj : AdjMatrix n) (P : PMatrix n) (T C : Finset (Fin n)) : Prop :=
  ∀ (g : StabilizerAt adj P T) (x : Fin n), x ∈ C ↔ (g : Equiv.Perm (Fin n)) x ∈ C

/-- **Restrict a residual automorphism to the selected cell.** Since `g` preserves `C` setwise (`hinv`), `subtypePerm`
gives a permutation of `{x // x ∈ C}` — the residual group's action on the cell that carries the scheme. -/
def cellRestrict {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C) (g : StabilizerAt adj P T) :
    Equiv.Perm {x : Fin n // x ∈ C} :=
  (g : Equiv.Perm (Fin n)).subtypePerm (fun x => (hinv g x).symm)

@[simp] theorem cellRestrict_apply {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C)
    (g : StabilizerAt adj P T) (x : {x : Fin n // x ∈ C}) :
    (cellRestrict hinv g x : Fin n) = (g : Equiv.Perm (Fin n)) x := rfl

/-- **The cell restriction as a group homomorphism** `StabilizerAt adj P T →* Perm {x // x ∈ C}`. -/
def cellRestrictHom {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C) :
    StabilizerAt adj P T →* Equiv.Perm {x : Fin n // x ∈ C} where
  toFun := cellRestrict hinv
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

/-- **The carried faithfulness hypothesis (`K = 1`)** — the cell action is injective. NOT free (unlike the complement's
`residualRestrict_injective`): its kernel is the residual automorphisms fixing `C` pointwise while moving other cells.
TRUE for the forms/Cameron family (`isotropic_span`), carried here and discharged per-family downstream. -/
def CellActionFaithful {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C) : Prop :=
  Function.Injective (cellRestrictHom hinv)

/-! ## Discharging `CellInvariant` — colour-invariance (step (1), the last "should-be-free" input)

`CellInvariant` for the descent's selected cell `selCell χ` reduces to `χ` being `g`-invariant, via the W1 core
`selCell_transport`. For the canonical selection colouring `χ = warmRefine adj P (individualizedColouring n T)` (= the
confinement's `indivχ`), `g`-invariance is `warmRefine_invariant_of_isAut` composed with `individualizedColouring_invariant`
(`g ∈ StabilizerAt adj P T` is an automorphism fixing `T` pointwise). So `CellInvariant` is FULLY discharged — not carried
— for the standard cell selector. -/

/-- **The generic reduction:** `CellInvariant (selCell χ)` from `g`-invariance of `χ`. Direct from the W1 core
`selCell_transport` (with `χ₁ = χ₂ = χ`). -/
theorem cellInvariant_selCell_of_gInvariant {T : Finset (Fin n)} {χ : Colouring n}
    (hginv : ∀ (g : StabilizerAt adj P T) (v : Fin n), χ ((g : Equiv.Perm (Fin n)) v) = χ v) :
    CellInvariant adj P T (selCell χ) :=
  fun g x => (selCell_transport (fun v => hginv g v) x).symm

/-- **The canonical selection colouring is `g`-invariant** — `warmRefine adj P (individualizedColouring n T)` is fixed
by every `g ∈ StabilizerAt adj P T` (automorphism fixing `T` pointwise): `warmRefine_invariant_of_isAut` on the
`individualizedColouring_invariant` seed. -/
theorem stabilizerAt_indivWarmRefine_invariant {T : Finset (Fin n)}
    (g : StabilizerAt adj P T) (v : Fin n) :
    warmRefine adj P (individualizedColouring n T) ((g : Equiv.Perm (Fin n)) v)
      = warmRefine adj P (individualizedColouring n T) v :=
  warmRefine_invariant_of_isAut g.2.1 g.2.2.1
    (fun w => individualizedColouring_invariant g.2.2.2 w) v

/-- **★ `CellInvariant` DISCHARGED for the standard selector** — the selected cell of the canonical individualization
colouring is preserved setwise by the residual group, with NO carried hypothesis. This supplies `hinv` to the cell
model for `χsel T := warmRefine adj P (individualizedColouring n T)`. -/
theorem cellInvariant_selCell_indivWarmRefine (T : Finset (Fin n)) :
    CellInvariant adj P T (selCell (warmRefine adj P (individualizedColouring n T))) :=
  cellInvariant_selCell_of_gInvariant (fun g v => stabilizerAt_indivWarmRefine_invariant g v)

/-! ## Pretransitivity on the cell (from Witt) -/

/-- **Pretransitivity of the cell range** from a pairwise transitivity input (`htrans_cell`, supplied by
`FrameSelectorTransitive` / Witt via `OrbitPartition`). -/
theorem cellRange_pretransitive {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C)
    (htrans_cell : ∀ a b : {x : Fin n // x ∈ C}, ∃ g : StabilizerAt adj P T, cellRestrict hinv g a = b) :
    MulAction.IsPretransitive (cellRestrictHom hinv).range {x : Fin n // x ∈ C} := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := htrans_cell a b
  exact ⟨⟨cellRestrict hinv g, ⟨g, rfl⟩⟩, hg⟩

/-! ## Promote the cell to `Fin m` and transport + count bridge -/

/-- The cell vertex count (the residue scheme's vertex-set size). -/
noncomputable def cellCard (C : Finset (Fin n)) : Nat := Fintype.card {x : Fin n // x ∈ C}

/-- The cell `≃ Fin (cellCard C)`. -/
noncomputable def cellEquivFin (C : Finset (Fin n)) : {x : Fin n // x ∈ C} ≃ Fin (cellCard C) :=
  Fintype.equivFin _

/-- **The cell group, transported to `Perm (Fin (cellCard C))`** — the subgroup whose orbital scheme is the residual
`SchurianScheme (cellCard C)`. -/
noncomputable def cellGroupFin {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C) :
    Subgroup (Equiv.Perm (Fin (cellCard C))) :=
  (cellRestrictHom hinv).range.map (Equiv.permCongrHom (cellEquivFin C)).toMonoidHom

/-- **The count bridge, UNDER faithfulness.** With `CellActionFaithful` the cell action is injective, so
`|cellGroupFin| = |cellRestrictHom.range| = |StabilizerAt adj P T|`. When `T` is the spine base `D_k`, the RHS is
`spineResidualCard` — the reframed `hcard`. -/
theorem cellGroupFin_card {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C)
    (hf : CellActionFaithful hinv) :
    Nat.card (cellGroupFin hinv) = Nat.card (StabilizerAt adj P T) := by
  have hmap : Nat.card (cellGroupFin hinv) = Nat.card (cellRestrictHom hinv).range :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Equiv.permCongrHom (cellEquivFin C)).injective).symm.toEquiv
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv

/-- **Pretransitivity of the transported cell group on `Fin (cellCard C)`.** Direct transport of `cellRange_pretransitive`
along `cellEquivFin` (the `permCongr` conjugation), mirroring `residualGroupFin_pretransitive`. -/
theorem cellGroupFin_pretransitive {T C : Finset (Fin n)} (hinv : CellInvariant adj P T C)
    (htrans_cell : ∀ a b : {x : Fin n // x ∈ C}, ∃ g : StabilizerAt adj P T, cellRestrict hinv g a = b) :
    MulAction.IsPretransitive (cellGroupFin hinv) (Fin (cellCard C)) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := htrans_cell ((cellEquivFin C).symm a) ((cellEquivFin C).symm b)
  refine ⟨⟨(Equiv.permCongrHom (cellEquivFin C)) (cellRestrict hinv g),
    Subgroup.mem_map.2 ⟨cellRestrict hinv g, ⟨g, rfl⟩, rfl⟩⟩, ?_⟩
  change (cellEquivFin C) (cellRestrict hinv g ((cellEquivFin C).symm a)) = b
  rw [hg, Equiv.apply_symm_apply]

/-! ## The Witt bridge — `htrans_cell` is SUPPLIED by `FrameSelectorTransitive` (non-vacuity)

The cell-transitivity input is not an arbitrary assumption: it is exactly Witt's theorem as packaged by confinement-P4.
`FrameSelectorTransitive` gives, at base `T`, a frame origin `r` with `∀ w ∈ C, OrbitPartition adj P T r w` — i.e.
`∃ g ∈ StabilizerAt adj P T, g r = w`. For `a, b ∈ C` this yields `gₐ r = a`, `g_b r = b`, so `g_b gₐ⁻¹` maps `a` to
`b` (no need for `r ∈ C` — `a, b` are the endpoints, `r` the intermediary). -/

/-- **Witt supplies `htrans_cell`.** `FrameSelectorTransitive` at base `T ⊇ S₀` gives the pairwise cell transitivity the
cell model needs — so `cellSchemeModel_of_group`'s `htrans_cell` is discharged by the confinement's own Witt output, not
assumed. -/
theorem htrans_cell_of_frameSelectorTransitive
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    {S₀ T : Finset (Fin n)} (hsub : S₀ ⊆ T)
    (hFST : ChainDescent.ConfinementP4.FrameSelectorTransitive adj P sel χsel S₀)
    (hinv : CellInvariant adj P T (sel (χsel T))) :
    ∀ a b : {x : Fin n // x ∈ sel (χsel T)},
      ∃ g : StabilizerAt adj P T, cellRestrict hinv g a = b := by
  obtain ⟨r, hr⟩ := hFST T hsub
  intro a b
  obtain ⟨πa, hAa, hPa, hFa, hEa⟩ := hr a.1 a.2
  obtain ⟨πb, hAb, hPb, hFb, hEb⟩ := hr b.1 b.2
  refine ⟨⟨πb, hAb, hPb, hFb⟩ * ⟨πa, hAa, hPa, hFa⟩⁻¹, ?_⟩
  apply Subtype.ext
  rw [cellRestrict_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  show (πb * πa⁻¹) a.1 = b.1
  rw [Equiv.Perm.mul_apply]
  have hra : πa⁻¹ a.1 = r := by
    rw [← hEa, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [hra, hEb]

/-! ## The faithful cell scheme model -/

/-- **The FAITHFUL residue-scheme model, on the selected cell `Fin (cellCard C)`.** `Aut(S)` is (via 2-closure) the
cell action of the residual group, so G3's classification refers to the REAL residue cell — the honesty win over the
`Fin n` cardinality-only model. `hcard` ties to `spineResidualCard adj P₀ χι₀ sel k` (with `T` the spine `D_k`). -/
structure CellSchemeModel (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (C : Finset (Fin n)) where
  S : SchurianScheme (cellCard C)
  hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true
  hrank : 2 ≤ S.rank
  hcard : Nat.card S.toAssociationScheme.SchemeAutGroup = spineResidualCard adj P₀ χι₀ sel k

/-- **★ The faithful cell-model constructor.** From: the cell setwise-invariance `hinv`, the carried faithfulness
`hf : CellActionFaithful`, the Witt pairwise transitivity `htrans_cell`, generosity `hsymm`, rank ≥ 2, the scoped
2-closure citation `h2c`, and the base identification `hT : StabilizerAt adj P T = ` the spine's residual (so the count
= `spineResidualCard`), build the faithful `CellSchemeModel`. `S := orbitalScheme cellGroupFin` (schurian free), `hne`
free, `hcard := h2c ⬝ cellGroupFin_card ⬝ hT`. -/
noncomputable def cellSchemeModel_of_group
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (k : Nat)
    {T C : Finset (Fin n)} [Nonempty (Fin (cellCard C))]
    (hinv : CellInvariant adj P T C)
    (hf : CellActionFaithful hinv)
    (htrans_cell : ∀ a b : {x : Fin n // x ∈ C}, ∃ g : StabilizerAt adj P T, cellRestrict hinv g a = b)
    (hsymm : ∀ v w : Fin (cellCard C),
      (orbMk v w : Orbital (cellGroupFin hinv)) = orbMk w v)
    (hrank : 2 ≤ (orbitalScheme _ (cellGroupFin_pretransitive hinv htrans_cell) hsymm).rank)
    (h2c : (orbitalScheme _ (cellGroupFin_pretransitive hinv htrans_cell)
        hsymm).toAssociationScheme.SchemeAutGroup = cellGroupFin hinv)
    (hT : Nat.card (StabilizerAt adj P T) = spineResidualCard adj P₀ χι₀ sel k) :
    CellSchemeModel adj P₀ χι₀ sel k C where
  S := orbitalScheme _ (cellGroupFin_pretransitive hinv htrans_cell) hsymm
  hne := fun i => by
    refine ⟨(orbitalIdx _ i).out.1, (orbitalIdx _ i).out.2, ?_⟩
    show decide (orbitalIdx _ i = orbMk (orbitalIdx _ i).out.1 (orbitalIdx _ i).out.2) = true
    rw [orbMk_out, decide_eq_true_eq]
  hrank := hrank
  hcard := by rw [h2c, cellGroupFin_card hinv hf, hT]

end ChainDescent.ConfinementCellModel
