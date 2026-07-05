/-
# Route C — the seam: four family seals → one correctness object.

This module is the **combine** layer of Route C. It carries:

1. `SealDisj` — the seal disjunction (`reachesRigidOrCameron` conclusion shape) with the free `IsCameronScheme`
   predicate + depth `bound` as parameters.
2. **The generic seam dispatch** (`reachesRigidOrCameron_seamDispatch` / `…_affineResidue`) — a residue `S` that is
   Cameron, or realized (`SchemeRealizes f S Y`) by *some* already-sealed scheme `Y`, is itself sealed. One theorem
   dispatches every branch of the Skresanov-isolated affine residue — the four forms-graph families **and** the
   cyclotomic branch (`cyclotomic_sealDisj`) — since all conclude the same `SealDisj` shape. This form carries the
   *generic* transport obligation `htransport` (transporting an arbitrary `SealDisj Y` needs all four disjuncts).
3. **The affine-polar atom-free capstone** (`reachesRigidOrCameron_viaSchurianRank3Affine_proved`) — for the
   affine-polar family the transport obligation is **discharged**, not carried: the forms-graph seal is Cameron-free
   and inhabits only `SchemeRecoveredByDepth`, so it transports the single **light** predicate
   `SeparatesAtBoundedBase` (via `RouteCTransport.separatesAtBoundedBase_transport`) and re-derives on `S` through
   `reachesRigidOrCameron_viaSpielman`. No `IsCameronScheme`-invariance premise, no `SchemeBlockRecovered`/`schemeEquiv`.
4. **The finer→coarser group-pinning** (`schemeAutGroup_affineScheme_eq_affineG` &c.) — modulo the named Skresanov
   rank-3 2-closure citation `AffineSchemeTwoClosed`, the coarse forms graph's automorphism group is *exactly*
   `affineG G₀ = translations ⋊ AΓO(Q)` (all four families, one lemma). This is the non-vacuous |Aut|-side content; the
   "poly-canonized" claim itself is the project's standard meta-composition, not a coarse-scheme Lean predicate (any
   such predicate is vacuous or false at bounded coarse-`warmRefine` depth = node-4). Bundled in `routeC_polySupport`.

Supersedes the scratch spike files `ScratchSeam` (its carried-`htransport` `reachesRigidOrCameron_viaSchurianRank3Affine`
is dropped — subsumed by the generic dispatch and superseded by the proved capstone), `ScratchSeamTransport`,
`ScratchSeamDispatch`, `ScratchRecoveredFormTransfer`. The cross-graph transport toolkit lives in `RouteCTransport`.
-/
import ChainDescent.CascadeAffine
import ChainDescent.RouteCTransport

namespace ChainDescent

open scoped Classical

/-- The seal disjunction for a scheme `X` (the conclusion shape of `…viaIsotropySeparates_wittFree`), with the free
`IsCameronScheme` predicate and depth `bound` as parameters. -/
def SealDisj (IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop) (bound : Nat)
    {n : Nat} (X : SchurianScheme n) : Prop :=
  ((SchemeBlockRecovered n X ∨ AbelianConsumed n X) ∨ SchemeRecoveredByDepth n X bound)
    ∨ IsCameronScheme n X

/-! ## The generic seam dispatch (cyclotomic branch included) -/

section Dispatch
variable {n : Nat}

/-- **The generic seam dispatch.** If the residue `S` is either Cameron, or realized (`S ≅ Y` via a
relation-preserving permutation `f`) by *some* concrete scheme `Y` that is already sealed (`SealDisj Y`), then `S`
is sealed. The single "sealed realized `Y`" disjunct absorbs **every** case of the classification — the cyclotomic
scheme (`cyclotomic_sealDisj`) and each forms-graph family alike — so this one theorem dispatches all of them,
cyclotomic branch included. `htransport` is the carried (generic) transport obligation. -/
theorem reachesRigidOrCameron_seamDispatch
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme n)
    (htransport : ∀ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
        SchemeRealizes f S Y → SealDisj IsCameronScheme bound Y → SealDisj IsCameronScheme bound S)
    (hclass : IsCameronScheme n S ∨
        ∃ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
          SchemeRealizes f S Y ∧ SealDisj IsCameronScheme bound Y) :
    SealDisj IsCameronScheme bound S := by
  rcases hclass with hcam | ⟨Y, f, hreal, hY⟩
  · exact Or.inr hcam
  · exact htransport Y f hreal hY

/-- **The full affine residue reaches the seal disjunction — cyclotomic branch included.** The named-intent form of
`reachesRigidOrCameron_seamDispatch`: it is the seam over the *whole* Skresanov-isolated affine residue (the
cyclotomic scheme via `cyclotomic_sealDisj`, the four forms-graph families via `viaSpielman`/adapter), not just the
forms-graph part. -/
theorem reachesRigidOrCameron_affineResidue
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme n)
    (htransport : ∀ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
        SchemeRealizes f S Y → SealDisj IsCameronScheme bound Y → SealDisj IsCameronScheme bound S)
    (hclass : IsCameronScheme n S ∨
        ∃ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
          SchemeRealizes f S Y ∧ SealDisj IsCameronScheme bound Y) :
    SealDisj IsCameronScheme bound S :=
  reachesRigidOrCameron_seamDispatch S htransport hclass

end Dispatch

/-! ## The affine-polar producer + the L1-proved atom-free capstone + the cyclotomic input -/

section Rank3Affine
variable {p d : ℕ} [Fact p.Prime]

/-- **The Cameron-free `SeparatesAtBoundedBase` producer (extracted).** The forms-graph chain's own Cameron-free
content, lifted out of `reachesRigidOrCameron_viaSymmetryBrokenBase`'s body *before* the `Or.inl (Or.inr …)`
disjunction padding: `IsotropySeparatesAtBase Q T` (+ bounded `T`) gives a bounded base that discretises the
affine-polar similitude scheme. Verbatim the witness that body feeds to `viaSpielman`. -/
theorem separatesAtBoundedBase_affinePolar
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) {bound : Nat} (hcard : T.card ≤ bound)
    (hIso : IsotropySeparatesAtBase Q T) :
    SeparatesAtBoundedBase (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) bound :=
  ⟨T, hcard,
    discrete_affineScheme_of_twoRoundDiffSeparates (similitudeGroup Q) (neg_mem_similitudeGroup Q) (T := T)
      (separatesAtBase_of_isotropySeparates_weak Q (relationRefinesIsotropy_similitude Q) hIso)⟩

/-- **The seam, `htransport` PROVED (not carried).** For the affine-polar family the transport obligation of the
generic dispatch is discharged. Forms-graph branch: extract the Cameron-free `SeparatesAtBoundedBase` on the concrete
`affineScheme(Q)` (`separatesAtBoundedBase_affinePolar`), transport it to `S`
(`separatesAtBoundedBase_transport`), then `viaSpielman` on `S` gives `SealDisj S` directly — so only the single
`SchemeRecoveredByDepth` disjunct is ever transported (via the light `SeparatesAtBoundedBase`), never
`SchemeBlockRecovered`/`schemeEquiv` or `IsCameronScheme`. Cameron branch: `Or.inr` directly on `S`. -/
theorem reachesRigidOrCameron_viaSchurianRank3Affine_proved
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme (p ^ d))
    (hclass : IsCameronScheme (p ^ d) S ∨
        ∃ (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (T : Finset (Fin (p ^ d)))
          (f : Equiv.Perm (Fin (p ^ d))),
          T.card ≤ bound ∧ IsotropySeparatesAtBase Q T ∧
          SchemeRealizes f S (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))) :
    SealDisj IsCameronScheme bound S := by
  rcases hclass with hcam | ⟨Q, T, f, hT, hIso, hreal⟩
  · exact Or.inr hcam
  · exact reachesRigidOrCameron_viaSpielman S
      (separatesAtBoundedBase_transport hreal (separatesAtBoundedBase_affinePolar Q T hT hIso))

/-- **The cyclotomic branch is a valid dispatch input.** The 1-dimensional cyclotomic scheme
`affineScheme (G0pow hd β)` satisfies `SealDisj` — its seal is `reachesRigidOrCameron_affineSlice` (modulo the cited
`TwinsAreSemilinear` / Ponomarenko 2-separability and `PrimitiveCCClassification`), whose conclusion is definitionally
`SealDisj`. Feeding `Y := affineScheme (G0pow hd β)` into `reachesRigidOrCameron_seamDispatch` routes the cyclotomic
case — the branch the four-case sketch dropped. -/
theorem cyclotomic_sealDisj (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1),
        ∃ v w, (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank)
    (hdb : d ≤ bound)
    (hcite : ∀ T : Finset (Fin (p ^ d)), TwinsAreSemilinear hd β hβneg T)
    (hImprim : ¬ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))) :
    SealDisj IsCameronScheme bound (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) :=
  reachesRigidOrCameron_affineSlice hd β hβneg hClassify hne hrank hdb hcite hImprim

end Rank3Affine

/-! ## The finer→coarser group-pinning (the |Aut| side; meta poly-support) -/

section GroupPinning
variable {p d : ℕ} [Fact p.Prime]

/-- **The affine group acts as scheme automorphisms of its own affine scheme** — `affineG G₀ ≤
SchemeAutGroup (affineScheme G₀)`. An `affineG G₀`-element preserves every `affineG G₀`-orbital (`orbMk_smul`),
so it preserves `relOfPair`, hence is a scheme automorphism. The `≥` half of the 2-closure identity for the affine
forms graphs; reusable for both the fine (`isometryGroup`) and coarse (`similitudeGroup`) schemes. -/
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
`SchemeAutGroup (affineScheme H) ≤ SchemeAutGroup (affineScheme G)`: the `H`-scheme is finer, so an `H`-scheme
automorphism also preserves the coarser `relOfPair`, hence is a `G`-scheme automorphism. -/
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
`G₀`-map (`SchemeAutGroup(affineScheme G₀) ≤ affineG G₀`). For the coarse forms-graph groups (`similitudeGroup Q`;
the multi-form `jointConeStab Qs`; the Suzuki ovoid-cone stabilizer) this is **Skresanov's rank-3 affine 2-closure
theorem** [arXiv:2007.14696 / 2202.03746] — a legitimate scoped citation, carried like `Theorem41Statement`/`G3`. Its
converse `≥` (`affineG_le_schemeAutGroup`) is *proved*, so the citation supplies only the one nontrivial direction. -/
def AffineSchemeTwoClosed {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : Prop :=
  (affineScheme G₀ hneg).toAssociationScheme.SchemeAutGroup ≤ affineG G₀

/-- **The coarse scheme's automorphism group is EXACTLY the affine `G₀`-group — generic, modulo the one named
Skresanov citation.** `le_antisymm` of the cited `AffineSchemeTwoClosed` (`≤`) and the proved
`affineG_le_schemeAutGroup` (`≥`). For every forms-graph family it pins `SchemeAutGroup(coarse) = affineG G₀ =
translations ⋊ (the known classical group)` — the object the |Aut|-recovery runtime (hand the known group to
Schreier–Sims) and the meta poly argument consume. **One lemma, all four families** (instantiate `G₀ := similitudeGroup
Q` / `jointConeStab Qs` / the Suzuki cone stabilizer). -/
theorem schemeAutGroup_affineScheme_eq_affineG
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (h2c : AffineSchemeTwoClosed hneg) :
    (affineScheme G₀ hneg).toAssociationScheme.SchemeAutGroup = affineG G₀ :=
  le_antisymm h2c (affineG_le_schemeAutGroup hneg)

/-- **Affine-polar instance** — the given `VO^ε` graph's automorphism group is exactly `affineG (similitudeGroup Q) =
translations ⋊ AΓO(Q)`, modulo Skresanov. The `G₀ := similitudeGroup Q` case of
`schemeAutGroup_affineScheme_eq_affineG`; the multi-form families are the `jointConeStab Qs` case of the same lemma. -/
theorem schemeAutGroup_coarse_eq_affineG (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (h2c : AffineSchemeTwoClosed (neg_mem_similitudeGroup Q)) :
    (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).toAssociationScheme.SchemeAutGroup
      = affineG (similitudeGroup Q) :=
  schemeAutGroup_affineScheme_eq_affineG (neg_mem_similitudeGroup Q) h2c

/-- **Route C poly-support certificate for the given (coarse) forms graph.** The honest, non-vacuous statement of
what Route C delivers, bundling the three Lean-certifiable facts: (i) `SchemeAutGroup(coarse) = affineG(similitudeGroup
Q)` — the given graph's automorphism group is *exactly* the known classical affine group `translations ⋊ AΓO(Q)`
(modulo Skresanov `h2c`) → hand it to Schreier–Sims for `|Aut|` and the canonical labelling; (ii)
`SchemeRecoveredByDepth fine bound` — the recovered-form (fine) scheme's **genuine** bounded-depth harvest recovers its
automorphisms (the Route C `FormAdapter` output, non-vacuous, unlike anything on the coarse `warmRefine`); (iii)
`SchemeAutGroup(fine) ≤ SchemeAutGroup(coarse)` — the recovered form only *refines*, never fabricates. With F4
(`RouteC.recoveredForm_colouring_equivariant`) this is the full structural support for the **meta** poly-canonization
of the given graph. -/
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

end GroupPinning

end ChainDescent
