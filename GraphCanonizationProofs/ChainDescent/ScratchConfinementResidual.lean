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

**This commit (the foundation):** `residualRestrict` (restrict a residual automorphism to `Perm {x // x ∉ D}` via
`subtypePerm`) as a `MonoidHom`, and `residualRestrict_injective` (faithfulness). These are the group-theory core the
residual scheme is built on, correct regardless of how the model reframe is finalized.

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

end ChainDescent.ConfinementResidual
