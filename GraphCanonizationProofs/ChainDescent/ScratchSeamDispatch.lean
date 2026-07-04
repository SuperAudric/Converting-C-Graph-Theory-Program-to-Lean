/-
# SEAM DISPATCH — the full affine residue, INCLUDING the cyclotomic branch (§9.1 T4)

`ScratchSeam.lean` dispatched a residue `S` to *one* forms-graph family (`∃ Q T f, IsotropySeparatesAtBase Q T ∧
SchemeRealizes f S (affineScheme(similitudeGroup Q))`). But the schurian rank-3 affine residue the classification
(Cameron + Liebeck + Skresanov) produces is `{1-dim cyclotomic} ∪ {forms-graphs (c)–(f)}` — and the **cyclotomic
branch was silently dropped** (route-c plan §9.1: "5 cases, not 4").

This file closes that gap by observing the cyclotomic seal `reachesRigidOrCameron_affineSlice` concludes the **same
`SealDisj` shape** as every forms-graph seal. So the honest dispatch is generic: **`S` is Cameron, or realized
(`S ≅ Y` via a permutation `f`) by SOME concrete scheme `Y` that is ALREADY sealed (`SealDisj Y`).** Both the
cyclotomic scheme (via `affineSlice`) and each forms-graph family (via its pair-route / `viaSpielman` seal) are
instances of the single "sealed realized `Y`" disjunct — one dispatch theorem covers all of them, cyclotomic
included. The transport obligation `htransport` (= L1, the seal disjunction is invariant along a realizing
permutation) is carried, exactly as in `ScratchSeam`.

Landed here (axiom-clean, NOT in build; `lake env lean ChainDescent/ScratchSeamDispatch.lean`):
* `reachesRigidOrCameron_seamDispatch` — the generic dispatch (subsumes `ScratchSeam`'s forms-graph-only form).
* `cyclotomic_sealDisj` — the cyclotomic scheme `affineScheme (G0pow β)` satisfies `SealDisj` (via `affineSlice`),
  so it is a valid dispatch input — the branch §9.1 dropped, now first-class.
* `reachesRigidOrCameron_affineResidue` — the combined statement: a residue that is Cameron, or the cyclotomic
  scheme, or a forms-graph family (each supplied as a sealed realized `Y`) reaches the seal disjunction.
-/
import ChainDescent.ScratchSeam

namespace ChainDescent

open scoped Classical

variable {p d : ℕ} [Fact p.Prime]

/-- **The generic seam dispatch.** If the residue `S` is either Cameron, or realized (`S ≅ Y` via a relation-preserving
permutation `f`) by *some* concrete scheme `Y` that is already sealed (`SealDisj Y`), then `S` is sealed. The single
"sealed realized `Y`" disjunct absorbs **every** case of the classification — the cyclotomic scheme (`cyclotomic_sealDisj`)
and each forms-graph family (its pair-route / adapter seal) alike — so this one theorem dispatches all of them,
including the cyclotomic branch that the four-case sketch omitted. `htransport` is the carried transport obligation
(= L1). Generalizes `ScratchSeam.reachesRigidOrCameron_viaSchurianRank3Affine` (its forms-graph `∃ Q T f, …` disjunct
is the special case `Y := affineScheme (similitudeGroup Q)`). -/
theorem reachesRigidOrCameron_seamDispatch {n : Nat}
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

/-- **The cyclotomic branch is a valid dispatch input.** The 1-dimensional cyclotomic scheme
`affineScheme (G0pow hd β)` satisfies `SealDisj` — its seal is `reachesRigidOrCameron_affineSlice` (modulo the cited
`TwinsAreSemilinear` / Ponomarenko 2-separability and `PrimitiveCCClassification`), whose conclusion is *definitionally*
`SealDisj`. So feeding `Y := affineScheme (G0pow hd β)` into `reachesRigidOrCameron_seamDispatch` routes the cyclotomic
case — the branch §9.1 dropped. -/
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

/-- **The full affine residue reaches the seal disjunction — cyclotomic branch included.** Packages the dispatch: `S`
is Cameron, or realized by a sealed `Y`; the intended `Y`s are the cyclotomic scheme (`cyclotomic_sealDisj`) and the
four forms-graph families (each `affineScheme(G₀)` sealed by `viaSpielman`/adapter). This is `reachesRigidOrCameron_seamDispatch`
under the name that records the intent: it is the seam over the *whole* Skresanov-isolated affine residue, not just the
forms-graph part. -/
theorem reachesRigidOrCameron_affineResidue {n : Nat}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme n)
    (htransport : ∀ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
        SchemeRealizes f S Y → SealDisj IsCameronScheme bound Y → SealDisj IsCameronScheme bound S)
    (hclass : IsCameronScheme n S ∨
        ∃ (Y : SchurianScheme n) (f : Equiv.Perm (Fin n)),
          SchemeRealizes f S Y ∧ SealDisj IsCameronScheme bound Y) :
    SealDisj IsCameronScheme bound S :=
  reachesRigidOrCameron_seamDispatch S htransport hclass

end ChainDescent

#print axioms ChainDescent.reachesRigidOrCameron_seamDispatch
#print axioms ChainDescent.cyclotomic_sealDisj
#print axioms ChainDescent.reachesRigidOrCameron_affineResidue
