/-
# FINER→COARSER TRANSFER — the honest scope (and a vacuity correction)

## The correction (2026-07-04)

An earlier draft of this file tried to conclude a predicate `GroupReproduced Sc := ∃ gens, closure gens =
SchemeAutGroup Sc` for the coarse scheme. **That predicate is VACUOUS** — `⟨↑(SchemeAutGroup Sc), Subgroup.closure_eq _⟩`
proves it for *every* scheme, with no recovery content whatsoever. This is the exact regression the project already
flagged and excised (`Cascade.lean` "do not regress (2026-06-07)": the retired `SchemeReproduced`). The genuine,
non-vacuous "reaches rigid" predicate is `SchemeRecoveredByDepth` — keyed on the **visible-realizer harvest** over
`warmRefine (schemeAdj S)`, non-vacuous precisely because the same-cell realizer clause is *false when cells ⊋ orbits*.

**The decisive consequence.** `SchemeRecoveredByDepth Sc bound` is about the **coarse** scheme's own `warmRefine`,
whose cells ⊋ orbits at any bounded/poly base for the forms graph — that IS the node-4 stall. So the *non-vacuous*
"coarse reaches rigid" is **false** here, and the only *true* version is the *vacuous* tautology. **Route C cannot
produce a non-vacuous `SchemeRecoveredByDepth Sc`** — there is no finer→coarser transfer at that level. What Route C
does is **change the canonization object**: it augments the descent with the recovered form `Q` (a global, poly,
iso-invariant computation — F4), i.e. it runs on the **fine** scheme `affineScheme (isometryGroup Q)`, whose
`SchemeRecoveredByDepth` *is* non-vacuously true (fine cells = orbits at a bounded base — the Route C adapter). The
coarse graph is then canonized because that finer colouring is an iso-invariant refinement of it (brick-1 + F4),
computable in poly, adding no branching. "Poly" stays the project's usual meta-claim over that augmented descent.

## What this file therefore proves (all genuinely non-vacuous)

1. `affineG_le_schemeAutGroup` — `affineG G₀ ≤ SchemeAutGroup (affineScheme G₀)`: the affine group acts as scheme
   automorphisms of its own orbital scheme (reusable; the `≥` half of every 2-closure identity here).
2. `schemeAutGroup_affineScheme_mono` — `H ≤ G ⟹ SchemeAutGroup (affineScheme H) ≤ SchemeAutGroup (affineScheme G)`:
   a finer affine scheme has a smaller automorphism group. Instantiated as `isometrySimilitude_schemeAutGroup_mono`
   (fine ⟶ coarse), the honest sense in which "the recovered form only *refines*".
3. `schemeAutGroup_coarse_eq_affineG` — modulo the Skresanov 2-closure citation `hSkresanov` (the coarse forms graph
   has no unexpected automorphisms), the coarse scheme's automorphism group is *exactly* the affine similitude group
   `affineG (similitudeGroup Q) = translations ⋊ AΓO(Q)`. This is the non-vacuous group-pinning the |Aut| side and the
   meta poly argument consume; it is where the reference-pin "scalings" live (`AΓO ⊋ AO`).

These are the transfer's *provable* content. The step "coarse graph is poly-canonized" is the meta-composition of the
**fine** adapter (`SchemeRecoveredByDepth fine`, genuine) + the F4/brick-1 canonicity bridge + `schemeAutGroup_coarse_eq_affineG`;
it is not a further non-vacuous Lean predicate (any such predicate on the coarse `warmRefine` is either vacuous or false).

NOT in build (scratch; `lake env lean ChainDescent/ScratchRecoveredFormTransfer.lean`).
-/
import ChainDescent.CascadeAffine

namespace ChainDescent

open scoped Classical

variable {p d : ℕ} [Fact p.Prime]

/-- **(A) The affine group acts as scheme automorphisms of its own affine scheme** — `affineG G₀ ≤
SchemeAutGroup (affineScheme G₀)`. An `affineG G₀`-element preserves every `affineG G₀`-orbital (`orbMk_smul`),
so it preserves `relOfPair` (`affineScheme_relOfPair_eq_iff`), hence is a scheme automorphism
(`isSchemeAut_of_relOfPair_eq`). The `≥` half of the 2-closure identity for the affine forms graphs; reusable for
both the fine (`isometryGroup`) and coarse (`similitudeGroup`) schemes. Axiom-clean. -/
theorem affineG_le_schemeAutGroup
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) :
    affineG G₀ ≤ (affineScheme G₀ hneg).toAssociationScheme.SchemeAutGroup := by
  intro σ hσ
  show IsSchemeAut (affineScheme G₀ hneg).toAssociationScheme σ
  apply isSchemeAut_of_relOfPair_eq
  intro v w
  rw [affineScheme_relOfPair_eq_iff G₀ hneg]
  simpa using orbMk_smul (⟨σ, hσ⟩ : affineG G₀) v w

/-- **`hmono` — a finer affine scheme has a smaller automorphism group.** For `H ≤ G` (both `∋ −1`),
`SchemeAutGroup (affineScheme H) ≤ SchemeAutGroup (affineScheme G)`: the `H`-scheme is finer
(`affineScheme_refines_of_le`), so an `H`-scheme automorphism (which preserves the finer `relOfPair`) also preserves
the coarser one, hence is a `G`-scheme automorphism. The elementary over-group inequality, proved outright. -/
theorem schemeAutGroup_affineScheme_mono
    {H G : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))} (hHG : H ≤ G)
    (hnegH : LinearEquiv.neg (ZMod p) ∈ H) (hnegG : LinearEquiv.neg (ZMod p) ∈ G) :
    (affineScheme H hnegH).toAssociationScheme.SchemeAutGroup
      ≤ (affineScheme G hnegG).toAssociationScheme.SchemeAutGroup := by
  intro π hπ
  have hπ' : IsSchemeAut (affineScheme H hnegH).toAssociationScheme π := hπ
  show IsSchemeAut (affineScheme G hnegG).toAssociationScheme π
  apply isSchemeAut_of_relOfPair_eq
  intro v w
  have hf : (affineScheme H hnegH).toAssociationScheme.relOfPair (π v) (π w)
          = (affineScheme H hnegH).toAssociationScheme.relOfPair v w := hπ'.relOfPair_eq v w
  rw [affineScheme_relOfPair_eq_iff H hnegH, orbMk_affine_eq_iff] at hf
  rw [affineScheme_relOfPair_eq_iff G hnegG, orbMk_affine_eq_iff]
  obtain ⟨g₀, hg₀, hg⟩ := hf
  exact ⟨g₀, hHG hg₀, hg⟩

/-- The concrete `hmono` for the isometry ⟶ similitude refinement (Route C's fine ⟶ coarse): the recovered form's
exact-value (isometry) scheme has a smaller Aut group than the given isotropy-only (similitude) graph. -/
theorem isometrySimilitude_schemeAutGroup_mono (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) :
    (affineScheme (isometryGroup Q) (neg_mem_isometryGroup Q)).toAssociationScheme.SchemeAutGroup
      ≤ (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).toAssociationScheme.SchemeAutGroup :=
  schemeAutGroup_affineScheme_mono (isometry_le_similitude Q)
    (neg_mem_isometryGroup Q) (neg_mem_similitudeGroup Q)

/-- **The Skresanov 2-closure citation (generic, one named premise for all four families).** `AffineSchemeTwoClosed`
says the affine scheme of `G₀` has **no unexpected automorphisms**: every scheme automorphism is already an affine
`G₀`-map (`SchemeAutGroup(affineScheme G₀) ≤ affineG G₀`, i.e. the 2-closure of `affineG G₀` is itself). For the
coarse forms-graph groups (`similitudeGroup Q`; the multi-form `jointConeStab Qs`; the Suzuki ovoid-cone stabilizer)
this is **Skresanov's rank-3 affine 2-closure theorem** [arXiv:2007.14696 / 2202.03746] — a legitimate scoped
citation, carried like `Theorem41Statement`/`G3`. Its converse `≥` (`affineG_le_schemeAutGroup`) is *proved*, so the
citation supplies only the one nontrivial direction. -/
def AffineSchemeTwoClosed {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : Prop :=
  (affineScheme G₀ hneg).toAssociationScheme.SchemeAutGroup ≤ affineG G₀

/-- **The coarse scheme's automorphism group is EXACTLY the affine `G₀`-group — generic, modulo the one named
Skresanov citation.** `le_antisymm` of the cited `AffineSchemeTwoClosed` (`≤`) and the proved `affineG_le_schemeAutGroup`
(`≥`). This is the non-vacuous group-pinning Route C supports: for every forms-graph family it pins
`SchemeAutGroup(coarse) = affineG G₀ = translations ⋊ (the known classical group)` — the object the |Aut|-recovery
runtime (hand the known group to Schreier–Sims) and the meta poly argument consume. **One lemma, all four families**
(instantiate `G₀ := similitudeGroup Q` / `jointConeStab Qs` / the Suzuki cone stabilizer). It is *not* a "reaches
rigid" predicate — those are vacuous (`∃ gens, closure = group`) or false at bounded coarse-`warmRefine` depth (node-4);
this is the honest group-level statement. -/
theorem schemeAutGroup_affineScheme_eq_affineG
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (h2c : AffineSchemeTwoClosed hneg) :
    (affineScheme G₀ hneg).toAssociationScheme.SchemeAutGroup = affineG G₀ :=
  le_antisymm h2c (affineG_le_schemeAutGroup hneg)

/-- **Affine-polar instance** — the given `VO^ε` graph's automorphism group is exactly `affineG (similitudeGroup Q) =
translations ⋊ AΓO(Q)`, modulo Skresanov. The `G₀ := similitudeGroup Q` case of `schemeAutGroup_affineScheme_eq_affineG`;
the multi-form families are the `jointConeStab Qs` case of the *same* lemma. -/
theorem schemeAutGroup_coarse_eq_affineG (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (h2c : AffineSchemeTwoClosed (neg_mem_similitudeGroup Q)) :
    (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).toAssociationScheme.SchemeAutGroup
      = affineG (similitudeGroup Q) :=
  schemeAutGroup_affineScheme_eq_affineG (neg_mem_similitudeGroup Q) h2c

/-- **Route C poly-support certificate for the given (coarse) forms graph.** The honest, non-vacuous statement of
what Route C delivers, bundling the three Lean-certifiable facts:
  (i)  `SchemeAutGroup(coarse) = affineG(similitudeGroup Q)` — the given graph's automorphism group is *exactly* the
       known classical affine group `translations ⋊ AΓO(Q)` (modulo the Skresanov citation `h2c`) → hand it to
       Schreier–Sims for `|Aut|` and the canonical labelling;
  (ii) `SchemeRecoveredByDepth fine bound` — the recovered-form (fine) scheme's **genuine** bounded-depth harvest
       recovers its automorphisms (the Route C `FormAdapter` output, `hfine` — non-vacuous, unlike anything on the
       coarse `warmRefine`);
  (iii)`SchemeAutGroup(fine) ≤ SchemeAutGroup(coarse)` — the recovered form only *refines*, never fabricates.
Together with F4 (`recoveredForm_colouring_equivariant`, ScratchRouteC — the recovered colouring is iso-invariant and
poly-computable) this is the full structural support for the **meta** poly-canonization of the given graph: recover
`Q` (poly, global), refine to the fine scheme (free, iso-invariant, discretizes at the `hfine` base), read off `Aut`
from (i). No open math remains — only the citations `{h2c = Skresanov, the per-family determiner, Buekenhout–Shult,
G3}` and the standard model assumptions. -/
theorem routeC_polySupport (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {bound : ℕ}
    (h2c : AffineSchemeTwoClosed (neg_mem_similitudeGroup Q))
    (hfine : SchemeRecoveredByDepth (p ^ d)
      (affineScheme (isometryGroup Q) (neg_mem_isometryGroup Q)) bound) :
    (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).toAssociationScheme.SchemeAutGroup
        = affineG (similitudeGroup Q)
      ∧ SchemeRecoveredByDepth (p ^ d)
          (affineScheme (isometryGroup Q) (neg_mem_isometryGroup Q)) bound
      ∧ (affineScheme (isometryGroup Q) (neg_mem_isometryGroup Q)).toAssociationScheme.SchemeAutGroup
          ≤ (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).toAssociationScheme.SchemeAutGroup :=
  ⟨schemeAutGroup_coarse_eq_affineG Q h2c, hfine, isometrySimilitude_schemeAutGroup_mono Q⟩

end ChainDescent

#print axioms ChainDescent.affineG_le_schemeAutGroup
#print axioms ChainDescent.schemeAutGroup_affineScheme_mono
#print axioms ChainDescent.schemeAutGroup_affineScheme_eq_affineG
#print axioms ChainDescent.schemeAutGroup_coarse_eq_affineG
#print axioms ChainDescent.routeC_polySupport
