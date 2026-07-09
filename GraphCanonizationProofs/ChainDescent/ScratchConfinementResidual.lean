/-
# ScratchConfinementResidual.lean — the D_k-restriction: the residual action on the base complement (WIP, NOT in build.sh)

**The finding that reshapes this piece.** A `SchurianScheme n` has **vertex-transitive** `Aut`
(`Scheme.schemeAutGroup_isPretransitive`: the diagonal `R₀` is a single orbital, so any two vertices are connected by
a scheme automorphism). Therefore the confinement model `M : ResidueSchemeModel` — whose `hcard` pins
`SchemeAutGroup(M.S) = StabilizerAt adj P D_k` and whose `hprim` demands `M.S` primitive (hence transitive) — is
**only inhabitable when `StabilizerAt adj P D_k` is transitive on `Fin n`**, i.e. when `D_k = ∅` (the stabilizer FIXES
`D_k` pointwise, so a transitive stabilizer forces `D_k = ∅`). For a general descent node (`D_k ≠ ∅`) the model
`SchurianScheme n` **cannot** carry the residual — the residual group acts on the complement `Dᶜ`, fixing `D_k`.

**So the D_k-restriction = represent the residue on its OWN vertex set, the complement `{x // x ∉ D}`.** The residual
group `StabilizerAt adj P D` fixes `D` pointwise, hence acts on `Dᶜ`; that action is FAITHFUL (an element fixing `D`
and `Dᶜ` is the identity), so the residual group embeds in `Perm {x // x ∉ D}`. Its orbital scheme on `{x // x ∉ D}`
is the residual `SchurianScheme` the (reframed) model needs — with the `hcard` count transferring via the faithful
embedding. This file builds that restriction.

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

end ChainDescent.ConfinementResidual
