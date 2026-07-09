/-
# ScratchConfinementResidual.lean — the D_k-restriction: the residual action on the base complement (WIP, NOT in build.sh)

**The finding that reshapes this piece (precise version).** A `SchurianScheme n` has **vertex-transitive** `Aut`
(`Scheme.schemeAutGroup_isPretransitive`: the diagonal `R₀` is a single orbital, so any two vertices are connected by
a scheme automorphism). The current `ResidueSchemeModel.hcard` is only a **cardinality** equality
(`Nat.card SchemeAutGroup(M.S) = spineResidualCard k`), NOT a group equality — so the current `S : SchurianScheme n`
model is **inhabitable and non-vacuous even for `D_k ≠ ∅`** (pick any schurian scheme of the right order). It typechecks
and the ① showcase is green; nothing is broken. **The real problem is FAITHFULNESS, not inhabitability.** A model that
genuinely *classifies the residue* needs `Aut(M.S)` to actually **be** the residual action `StabilizerAt adj P D_k` (so
that G3 classifying `M.S` as Cameron says something about the residue, instead of that content being smuggled into the
carried `hWitt`). But `StabilizerAt adj P D_k` FIXES `D_k` pointwise while a schurian scheme's `Aut` is transitive on its
whole vertex set — so a **faithful** model genuinely **cannot** live on `Fin n` for `D_k ≠ ∅` (a scheme with `D_k` as
fixed points is not transitive, hence not schurian). It must live on the residual `{x // x ∉ D_k}`, where the residual
group actually acts.

**So the D_k-restriction = represent the residue on its OWN vertex set, the complement `{x // x ∉ D}`.** The residual
group `StabilizerAt adj P D` fixes `D` pointwise, hence acts on `Dᶜ`; that action is FAITHFUL (an element fixing `D`
and `Dᶜ` is the identity), so the residual group embeds in `Perm {x // x ∉ D}`. This file builds that faithful
embedding + its transport to `Fin m` + the count bridge.

**★★ CORRECTION (2026-07-09 cont., user-prompted transitivity check) — the SCHEME lives on the selected CELL, NOT the
whole complement.** The residual group is **transitive within a colour class but NOT across the complement's several
classes** (`FrameSelectorTransitive`, `ScratchConfinementP4:167`, is transitivity on `sel (χsel T)` — the selected
cell; its doc-comment: "for a Clebsch-type scheme the point-stabilizer is NOT transitive on the colour classes"). So
the complement `{x // x ∉ D}` is in general a UNION of cells = intransitive ⟹ it is NOT the vertex set of a single
`orbitalScheme` (`htrans_res` below — transitivity on ALL of `{x // x ∉ D}` — is FALSE in the multi-cell regime; the
constructor is only inhabitable when the complement is a single cell, an over-restriction analogous to the original
`D = ∅` one, just relocated). **The transitive object — the residue scheme G3 classifies — is the SELECTED CELL**,
where transitivity is Witt's theorem (`FrameSelectorTransitive`, delivered by confinement-P4) and PRIMITIVITY (the
confinement branch) makes block-transitivity = vertex-transitivity, so the block-vs-vertex concern is handled. The
faithful-embedding machinery here (`residualRestrict_injective`) gives faithfulness on the COMPLEMENT (free); on the
CELL the count `|cell-Aut| = spineResidualCard` instead needs the cell action FAITHFUL — the documented model-
faithfulness gap (kernel = elements fixing the cell but moving other cells), a CARRIED hypothesis, not free. **⟹ the
correct reframe is CELL-based: vertex set `sel (χsel T)`, transitivity from `FrameSelectorTransitive`, and a carried
cell-faithfulness/largeness. The whole-complement constructor below is faithful-but-intransitive — kept as substrate
(faithful embedding, count bridge, `permCongr` transport), NOT the final model. It RELOCATES the gap to cell-
faithfulness; it does not eliminate it.**

**State (2026-07-09, all axiom-clean, NOT in `build.sh`).**
  · **Foundation:** `residualRestrict` / `residualRestrictHom` (restrict a residual automorphism to `Perm {x // x ∉ D}`
    via `subtypePerm`; `residual_pred` = the predicate preservation) + `residualRestrict_injective` (faithfulness).
  · **Step 1:** `residualRange_pretransitive` — given residual transitivity (`htrans_res`, the VT/primitive-rank-3
    input), the range subgroup acts pretransitively on `{x // x ∉ D}`.
  · **Step 2 (setup + count bridge):** `residualCard` / `residualEquivFin` (promote `{x // x ∉ D} ≃ Fin m`),
    `residualGroupFin` (transport the range to `Perm (Fin m)` via `Equiv.permCongrHom`), and **`residualGroupFin_card`**
    (`|residualGroupFin| = |StabilizerAt adj P D|` = `spineResidualCard` — the reframed `hcard`, via faithfulness +
    the transport `MulEquiv`).

**REMAINING (the reframe = step 3, NOT done — flagged for the fresh reader):**
  1. `residualGroupFin` pretransitive on `Fin m` — transport `residualRange_pretransitive` along `residualEquivFin`
     (`MulAction.IsPretransitive` under an equivariant equiv; Mathlib plumbing).
  2. Generosity `hsymm` (`∀ v w, orbMk v w = orbMk w v` for `residualGroupFin`) — a genuine hypothesis (the residue's
     relations are symmetric; supplied per-family / carried).
  3. `orbitalScheme residualGroupFin (…pretransitive) (…generous) : SchurianScheme (residualCard D)` = the residual
     scheme `S`; feed `residualModel_of_orbitalGroup` (`ScratchConfinementSchurianModel`) with the 2-closure citation +
     `residualGroupFin_card`.
  4. **The structural reframe:** change `ResidueSchemeModel.S` from `SchurianScheme n` to `SchurianScheme (residualCard
     D)` (the residual), and rethread `ScratchConfinementP3` / `Witt` / `ConfinementCitations`
     (`ScratchConfinementX3Complete`). This is the reviewable change the user wants to scrutinize with steps 1–2 in hand.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementSchurianModel

namespace ChainDescent.ConfinementResidual

open ChainDescent
open ChainDescent.ConfinementP1

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}

/-- A residual automorphism preserves the base-complement predicate: `x ∉ D ↔ g x ∉ D`. Forward is
`FixesPointwise.complement`; backward is that `g` fixes `D` pointwise. -/
theorem residual_pred {D : Finset (Fin n)} (g : StabilizerAt adj P D) (x : Fin n) :
    x ∉ D ↔ (g : Equiv.Perm (Fin n)) x ∉ D := by
  have hfix : FixesPointwise (g : Equiv.Perm (Fin n)) D := g.2.2.2
  refine ⟨fun hx => hfix.complement hx, fun hgx hxD => hgx ?_⟩
  rw [hfix x hxD]; exact hxD

/-- **Restrict a residual automorphism to the base complement.** Since `g` fixes `D` pointwise it maps `Dᶜ` to `Dᶜ`
(`residual_pred`), so `subtypePerm` gives a permutation of `{x // x ∉ D}` — the residual group's action on the vertices
that actually carry structure. -/
def residualRestrict {D : Finset (Fin n)} (g : StabilizerAt adj P D) :
    Equiv.Perm {x : Fin n // x ∉ D} :=
  (g : Equiv.Perm (Fin n)).subtypePerm (fun x => (residual_pred g x).symm)

@[simp] theorem residualRestrict_apply {D : Finset (Fin n)} (g : StabilizerAt adj P D)
    (x : {x : Fin n // x ∉ D}) :
    (residualRestrict g x : Fin n) = (g : Equiv.Perm (Fin n)) x := rfl

/-- **The restriction is a group homomorphism** `StabilizerAt adj P D →* Perm {x // x ∉ D}`. -/
def residualRestrictHom {D : Finset (Fin n)} :
    StabilizerAt adj P D →* Equiv.Perm {x : Fin n // x ∉ D} where
  toFun := residualRestrict
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

/-- **The residual action is FAITHFUL** — the restriction is injective. An automorphism fixing `D` pointwise (given)
and acting as the identity on `Dᶜ` (from equal restrictions) is the identity everywhere. So `|StabilizerAt adj P D|`
equals the order of its image in `Perm {x // x ∉ D}` — the bridge that carries `hcard` to the residual scheme. -/
theorem residualRestrict_injective {D : Finset (Fin n)} :
    Function.Injective (residualRestrict (adj := adj) (P := P) (D := D)) := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ D
  · rw [(g₁.2.2.2 : FixesPointwise _ D) x hx, (g₂.2.2.2 : FixesPointwise _ D) x hx]
  · have hxeq : residualRestrict g₁ ⟨x, hx⟩ = residualRestrict g₂ ⟨x, hx⟩ := by rw [h]
    exact congrArg Subtype.val hxeq

theorem residualRestrictHom_injective {D : Finset (Fin n)} :
    Function.Injective (residualRestrictHom (adj := adj) (P := P) (D := D)) :=
  residualRestrict_injective

/-! ## Step 1 — the residual action is pretransitive on the complement (given residual transitivity)

For a confinement (node-4/Cameron) residue the residual group `StabilizerAt adj P D` is a primitive rank-3 group,
hence transitive on the complement `{x // x ∉ D}`. Packaged as the clean hypothesis `htrans_res` (any two complement
vertices are joined by a residual automorphism), step 1 promotes it to pretransitivity of the *range subgroup* acting
on the complement — the input `orbitalScheme` needs (after the Step-2 promotion to `Fin m`). -/

/-- **Step 1 — pretransitivity of the residual range on the complement.** Given that any two complement vertices are
joined by a residual automorphism (residual transitivity, the VT/primitive-rank-3 input), the image subgroup
`residualRestrictHom.range` acts pretransitively on `{x // x ∉ D}`. -/
theorem residualRange_pretransitive {D : Finset (Fin n)}
    (htrans_res : ∀ a b : {x : Fin n // x ∉ D}, ∃ g : StabilizerAt adj P D, residualRestrict g a = b) :
    MulAction.IsPretransitive (residualRestrictHom (adj := adj) (P := P) (D := D)).range
      {x : Fin n // x ∉ D} := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := htrans_res a b
  exact ⟨⟨residualRestrict g, ⟨g, rfl⟩⟩, hg⟩

/-! ## Step 2 (setup) — promote the complement to `Fin m` and transport the residual group

`orbitalScheme` lives on `Fin m` (`SchurianScheme m`), so the complement `{x // x ∉ D}` (a `Fintype` of card `m`) is
carried to `Fin m` by `Fintype.equivFin`, and the residual range is transported along it by `Equiv.permCongrHom` (a
`MulEquiv`). The **count bridge** `residualGroupFin_card` (`|residualGroupFin| = |StabilizerAt adj P D|`) is the crux
for the reframed `hcard`: it composes the faithful embedding (`residualRestrict_injective`) with the transport `MulEquiv`.
The remaining pieces for the full reframe (pretransitivity of `residualGroupFin` on `Fin m` via the equiv, generosity,
and the `orbitalScheme` instantiation → `SchurianScheme m`) are the reframe itself (step 3), documented in the header. -/

/-- The complement vertex count (the residual scheme's vertex set size). -/
noncomputable def residualCard (D : Finset (Fin n)) : Nat := Fintype.card {x : Fin n // x ∉ D}

/-- The complement `≃ Fin (residualCard D)` (the promotion of the residual to its own vertex set). -/
noncomputable def residualEquivFin (D : Finset (Fin n)) :
    {x : Fin n // x ∉ D} ≃ Fin (residualCard D) :=
  Fintype.equivFin _

/-- **The residual group, transported to `Perm (Fin (residualCard D))`** — the subgroup whose orbital scheme is the
reframed residual `SchurianScheme (residualCard D)`. -/
noncomputable def residualGroupFin {D : Finset (Fin n)} :
    Subgroup (Equiv.Perm (Fin (residualCard D))) :=
  (residualRestrictHom (adj := adj) (P := P) (D := D)).range.map
    (Equiv.permCongrHom (residualEquivFin D)).toMonoidHom

/-- **★ Step 2 — the count bridge (the reframed `hcard`).** The transported residual group has the SAME order as
`StabilizerAt adj P D` (= `spineResidualCard`): the transport is a `MulEquiv` (order-preserving) and the restriction is
injective (`residualRestrict_injective`), so `|residualGroupFin| = |range| = |StabilizerAt adj P D|`. This is exactly
the `hcard` the reframed (residual) `ResidueSchemeModel` needs, once `orbitalScheme(residualGroupFin)` is its `S`. -/
theorem residualGroupFin_card {D : Finset (Fin n)} :
    Nat.card (residualGroupFin (adj := adj) (P := P) (D := D)) = Nat.card (StabilizerAt adj P D) := by
  have hmap : Nat.card (residualGroupFin (adj := adj) (P := P) (D := D))
      = Nat.card (residualRestrictHom (adj := adj) (P := P) (D := D)).range :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Equiv.permCongrHom (residualEquivFin D)).injective).symm.toEquiv
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective residualRestrictHom_injective).symm.toEquiv

/-! ## Step 3 — the faithful residual scheme model on `Fin (residualCard D)` (additive reframe)

The reframed model presents the residue by a `SchurianScheme (residualCard D)` — on the base **complement**, where the
residual group `StabilizerAt adj P D` genuinely acts — with `Aut` FAITHFULLY that residual action (via the 2-closure
citation + the count bridge). This is what makes G3's Cameron-classification refer to the residue, instead of that
content being smuggled into the carried `hWitt`. It is built **additively**: the on-`Fin n` `ResidueSchemeModel`
(`ScratchConfinementP3`) and the green ① showcase are untouched; the follow-up rethread of P3/Witt/bundle onto this
type is a separate, reviewable step. -/

/-- **Step 1 (promoted to `Fin m`).** The transported residual group `residualGroupFin` acts pretransitively on
`Fin (residualCard D)`. Direct transport of `residualRange_pretransitive` along `residualEquivFin`: given `a b`, pull
back to the complement, obtain a residual `g` moving one to the other, and its `permCongr` image moves `a` to `b`. -/
theorem residualGroupFin_pretransitive {D : Finset (Fin n)}
    (htrans_res : ∀ a b : {x : Fin n // x ∉ D}, ∃ g : StabilizerAt adj P D, residualRestrict g a = b) :
    MulAction.IsPretransitive (residualGroupFin (adj := adj) (P := P) (D := D))
      (Fin (residualCard D)) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g, hg⟩ := htrans_res ((residualEquivFin D).symm a) ((residualEquivFin D).symm b)
  refine ⟨⟨(Equiv.permCongrHom (residualEquivFin D)) (residualRestrict g),
    Subgroup.mem_map.2 ⟨residualRestrict g, ⟨g, rfl⟩, rfl⟩⟩, ?_⟩
  change (residualEquivFin D) (residualRestrict g ((residualEquivFin D).symm a)) = b
  rw [hg, Equiv.apply_symm_apply]

/-- **The reframed, FAITHFUL residue-scheme model** — presented on the base complement `Fin (residualCard D_k)`,
`D_k` the level-`k` base prefix. Differs from `ResidueSchemeModel` only in the vertex set of `S`
(`residualCard D_k` vs `n`), which is exactly what lets `Aut(S)` be the residual action (a schurian scheme's `Aut` is
vertex-transitive, so on `Fin n` it could not fix `D_k`). -/
structure ResidualSchemeModel (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) where
  S : SchurianScheme (residualCard (defaultSpineChain adj P₀ χι₀ sel k).D)
  hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true
  hrank : 2 ≤ S.rank
  hcard : Nat.card S.toAssociationScheme.SchemeAutGroup = spineResidualCard adj P₀ χι₀ sel k

/-- **★ The reframed extraction constructor (faithful, on the residual vertex set).** Build `ResidualSchemeModel`
from: residual transitivity `htrans_res` (the VT / primitive-rank-3 input), generosity `hsymm`, rank ≥ 2, and the
scoped **2-closure citation** `h2c : SchemeAutGroup(orbitalScheme residualGroupFin) = residualGroupFin` (Skresanov
form; needs the residue primitive rank-3, i.e. the `hImprim`/primitivity item). `S := orbitalScheme residualGroupFin`
is schurian by construction; `hne` is free; and `hcard` composes `h2c` with the count bridge `residualGroupFin_card`
(`|residualGroupFin| = |StabilizerAt adj P_k D_k| = spineResidualCard k`) — so the residual order transfers with NO
extra hypothesis. This is the faithful counterpart of `residueModel_of_orbitalGroup`, valid for `D_k ≠ ∅`. -/
noncomputable def residualSchemeModel_of_group
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (k : Nat)
    [Nonempty (Fin (residualCard (defaultSpineChain adj P₀ χι₀ sel k).D))]
    (htrans_res : ∀ a b : {x : Fin n // x ∉ (defaultSpineChain adj P₀ χι₀ sel k).D},
      ∃ g : StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
        (defaultSpineChain adj P₀ χι₀ sel k).D, residualRestrict g a = b)
    (hsymm : ∀ v w : Fin (residualCard (defaultSpineChain adj P₀ χι₀ sel k).D),
      (orbMk v w : Orbital (residualGroupFin (adj := adj)
        (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
        (D := (defaultSpineChain adj P₀ χι₀ sel k).D))) = orbMk w v)
    (hrank : 2 ≤ (orbitalScheme _ (residualGroupFin_pretransitive
      (adj := adj) (P := (defaultSpineChain adj P₀ χι₀ sel k).P) htrans_res) hsymm).rank)
    (h2c : (orbitalScheme _ (residualGroupFin_pretransitive
        (adj := adj) (P := (defaultSpineChain adj P₀ χι₀ sel k).P) htrans_res)
        hsymm).toAssociationScheme.SchemeAutGroup
      = residualGroupFin (adj := adj) (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
        (D := (defaultSpineChain adj P₀ χι₀ sel k).D)) :
    ResidualSchemeModel adj P₀ χι₀ sel k where
  S := orbitalScheme _ (residualGroupFin_pretransitive
    (adj := adj) (P := (defaultSpineChain adj P₀ χι₀ sel k).P) htrans_res) hsymm
  hne := fun i => by
    refine ⟨(orbitalIdx _ i).out.1, (orbitalIdx _ i).out.2, ?_⟩
    show decide (orbitalIdx _ i = orbMk (orbitalIdx _ i).out.1 (orbitalIdx _ i).out.2) = true
    rw [orbMk_out, decide_eq_true_eq]
  hrank := hrank
  hcard := by rw [h2c]; exact residualGroupFin_card

end ChainDescent.ConfinementResidual
