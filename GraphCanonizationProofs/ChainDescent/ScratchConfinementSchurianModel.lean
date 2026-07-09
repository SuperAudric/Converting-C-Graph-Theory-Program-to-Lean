/-
# ScratchConfinementSchurianModel.lean — the scheme-extraction constructor for `ResidueSchemeModel` (WIP, NOT in build.sh)

**What this resolves.** Confinement carries `M : ResidueSchemeModel adj P₀ χι₀ sel k` — a *faithful schurian scheme*
of the level-`k` residue (`ScratchConfinementP3`). This is a **modelling** obligation, NOT an `UnhandledResidue` flag:
Phase-1 recovers (assume-VT prune) and the residue it handles is node-4 = schurian + Cameron, so a faithful model
exists; the task is to *build* it.

**The Skresanov-form resolution (confirmed usable).** `affineScheme G₀ := orbitalScheme (affineG G₀)`
(`CascadeAffine.lean`) is a `SchurianScheme` **by construction**, and the carried Skresanov 2-closure citation
`AffineSchemeTwoClosed` (`RouteCSeam.lean`) gives `SchemeAutGroup(affineScheme G₀) = affineG G₀` — the scheme's
automorphism group is exactly the known classical group. Generalizing off the affine family: for ANY residual group
`G` the orbital scheme `orbitalScheme G` is schurian, and a 2-closure citation `SchemeAutGroup = G` pins its `Aut`.

**This file = the extraction constructor.** `residueModel_of_orbitalGroup` builds a `ResidueSchemeModel` from
  · a residual automorphism group `G` that is pretransitive + generously transitive (so `orbitalScheme G` exists),
  · `rank ≥ 2` (`G` has ≥ 3 orbitals — the primitive-rank-3+ input),
  · the **2-closure citation** `h2c : SchemeAutGroup(orbitalScheme G) = G` (Skresanov form), and
  · the **faithfulness count** `hcount : |G| = spineResidualCard k` (the residual `Aut` order matches the descent's
    counted residual stabilizer).
The `schurian` axiom and `hne` (all relations occur) are FREE (orbital scheme). So the whole `M` obligation reduces,
with no remaining scheme-construction, to exactly {a pretransitive residual group, a 2-closure citation, a count
bridge} — the honest residual, none of it an `UnhandledResidue`. The group `G` + `hcount` is the "faithfulness" piece
(supplied by the assume-VT / recovery step); `h2c` is the scoped 2-closure citation (needs the residue primitive
rank-3 first, i.e. the `hImprim`/primitivity item).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementP3

namespace ChainDescent.ConfinementSchurianModel

open ChainDescent
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP1

variable {n : Nat}

/-- **★ The scheme-extraction constructor.** Build the confinement's `ResidueSchemeModel` from a residual automorphism
group `G` (pretransitive + generously transitive), its rank ≥ 2, the 2-closure citation `h2c`, and the faithfulness
count `hcount`. The `S := orbitalScheme G` is schurian by construction; `hne` is proved outright; `hcard` is `h2c`
composed with `hcount`. This crystallizes the SchurianScheme modelling gap into its three genuine inputs and shows the
scheme-construction itself is not a gap. -/
noncomputable def residueModel_of_orbitalGroup
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (k : Nat)
    [Nonempty (Fin n)]
    {G : Subgroup (Equiv.Perm (Fin n))}
    (htrans : MulAction.IsPretransitive G (Fin n))
    (hsymm : ∀ v w : Fin n, (orbMk v w : Orbital G) = orbMk w v)
    (hrank : 2 ≤ (orbitalScheme G htrans hsymm).rank)
    (h2c : (orbitalScheme G htrans hsymm).toAssociationScheme.SchemeAutGroup = G)
    (hcount : Nat.card G = spineResidualCard adj P₀ χι₀ sel k) :
    ResidueSchemeModel adj P₀ χι₀ sel k where
  S := orbitalScheme G htrans hsymm
  hne := fun i => by
    refine ⟨(orbitalIdx G i).out.1, (orbitalIdx G i).out.2, ?_⟩
    show decide (orbitalIdx G i = orbMk (orbitalIdx G i).out.1 (orbitalIdx G i).out.2) = true
    rw [orbMk_out, decide_eq_true_eq]
  hrank := hrank
  hcard := by rw [h2c]; exact hcount

end ChainDescent.ConfinementSchurianModel
