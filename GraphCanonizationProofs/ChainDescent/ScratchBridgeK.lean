/-
# Bridge lift (concern #4), the soft endpoint — a `Z`-separating base discharges `ZProfileSeparatesK` (abstract `K`).

The V-indexed, abstract-`[Field K]` analog of `ScratchBridgeZ.zProfileSeparates_of_zSep`. Pure logic on the
predicate (no analytic content): if every pair of distinct vertices is separated by *some* sub-frame in the joint
isotropic counts, then `ScratchFieldGen.ZProfileSeparatesK Q T` holds. This is the endpoint the increment-4/5 matching
feeds (a `Z`-separating base ⟹ `ZProfileSeparatesK` ⟹ — via `isotropySeparatesK_of_zProfileSeparatesK` + the q=p
adapter — the seal).

The *analytic* half of the bridge (the per-pair `jointIsoCountK_ne_of_chiSep_pair`, i.e. the `Z = qᵈ + χ(det G₂)·K·(…)`
closed form turning a χ-separating pair into a `Z`-separating one) is the large remaining lift of
`ScratchLemmaA`/`ScratchBridge{A,B,C,D}` over abstract `K` — tracked separately.

Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build.
-/
import ChainDescent.ScratchFieldGen

namespace ChainDescent

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-- **The bridge reduction (abstract `K`).** If every pair of distinct points is separated by some sub-frame `S ⊆ T`
in the joint isotropic counts, then `ZProfileSeparatesK Q T` holds. -/
theorem zProfileSeparatesK_of_zSep (Q : QuadraticForm K (Fin d → K))
    (T : Finset (Fin d → K))
    (hsep : ∀ u u' : Fin d → K, u ≠ u' →
      ∃ S, S ⊆ T ∧ jointIsoCountK Q u S ≠ jointIsoCountK Q u' S) :
    ZProfileSeparatesK Q T := by
  intro u u' hall
  by_cases h : u = u'
  · subst h; exact ⟨rfl, fun _ => rfl⟩
  · obtain ⟨S, hS, hne⟩ := hsep u u' h
    exact absurd (hall S hS) hne

end ChainDescent

#print axioms ChainDescent.zProfileSeparatesK_of_zSep
