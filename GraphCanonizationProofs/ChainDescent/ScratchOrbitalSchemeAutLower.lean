/-
# ScratchOrbitalSchemeAutLower.lean — the free 2-closure LOWER direction (WIP, NOT in build.sh)

**What this proves + why it matters (the citation elimination).** The confinement's residue-scheme model carries
`hcard : |SchemeAutGroup(M.S)| = spineResidualCard` to transfer the flag's super-poly bound to G3's largeness input.
The `=` needs Skresanov's rank-3 2-closure (`AffineSchemeTwoClosed`, a citation). **But `confinementLargeScheme` is a
strict LOWER bound** (`2^baseMax n < |SchemeAutGroup|`), and `hcard` is used ONLY there — so a **lower bound**
`spineResidualCard ≤ |SchemeAutGroup(M.S)|` suffices, and *that* follows from the **free** direction
`G ≤ SchemeAutGroup(orbitalScheme G)` (a group preserves its own orbitals — `orbMk_smul`), needing **NO Skresanov
citation**. This eliminates the 2-closure citation from Seal-Phase-1 leg (b), per the no-carried-hypotheses discipline.

This file provides the two free-direction bricks; wiring them into a weakened `hcard_le` (dropping `h2c`) is the next step.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.Scheme

namespace ChainDescent

variable {n : Nat}

/-- **The free 2-closure direction: `G ≤ SchemeAutGroup(orbitalScheme G)`.** Every `g ∈ G` preserves every
`G`-orbital (`orbMk_smul`), so it is a scheme automorphism of the orbital scheme. This is the *general* version of
`affineG_le_schemeAutGroup` (`RouteCSeam.lean:151`), citation-free — the one direction of 2-closure that always holds. -/
theorem le_schemeAutGroup_orbitalScheme [Nonempty (Fin n)]
    (G : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive G (Fin n))
    (hsymm : ∀ v w : Fin n, (orbMk v w : Orbital G) = orbMk w v) :
    G ≤ (orbitalScheme G htrans hsymm).toAssociationScheme.SchemeAutGroup := by
  intro σ hσ
  show IsSchemeAut (orbitalScheme G htrans hsymm).toAssociationScheme σ
  intro ℓ a b
  show decide ((orbitalIdx G) ℓ = orbMk (σ a) (σ b))
    = decide ((orbitalIdx G) ℓ = orbMk a b)
  rw [orbMk_smul (⟨σ, hσ⟩ : G) a b]

/-- **The residual group order is a LOWER bound on the orbital-scheme Aut order** — the citation-free half of the
count bridge. `Nat.card` monotone along the free inclusion `G ≤ SchemeAutGroup(orbitalScheme G)`. -/
theorem card_le_schemeAutGroup_orbitalScheme [Nonempty (Fin n)]
    (G : Subgroup (Equiv.Perm (Fin n)))
    (htrans : MulAction.IsPretransitive G (Fin n))
    (hsymm : ∀ v w : Fin n, (orbMk v w : Orbital G) = orbMk w v) :
    Nat.card G ≤ Nat.card (orbitalScheme G htrans hsymm).toAssociationScheme.SchemeAutGroup :=
  Nat.card_le_card_of_injective
    (Subgroup.inclusion (le_schemeAutGroup_orbitalScheme G htrans hsymm))
    (Subgroup.inclusion_injective _)

end ChainDescent
