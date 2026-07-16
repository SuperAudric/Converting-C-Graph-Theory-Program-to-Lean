import ChainDescent.OrbitPrune

/-!
# `P3c` — `prunedSupply d`: match from ONE reference entry, not all pairs

## The win, and why it is provable

`deepMatchSupply d` matches **every** `(branch, sequence)` table entry against **every** other — `|table|²` colour
matches, the dominant cost (`|table|² · n²`). The waste is real and the fix is exact: `matchCol` **composes**
(`rankSwap ψₐ ψ_c = rankSwap ψ_b ψ_c ∘ rankSwap ψₐ ψ_b`), so matching every entry against **one fixed discrete
reference** `r` already generates the *same group* — `|table|` matches, not `|table|²`. Quadratic → linear.

The `SameOrbits` proof does not even need the composition identity. Because the enumeration is **length-closed**
(`α · (v, s)` is a table entry whenever `(v, s)` is, for any automorphism `α` — `mem_allSeqs_map`), the two verified
sets are **equal as membership sets**:
- **pruned ⊆ deep** — a reference match `matchCol r q` is one of the all-pairs candidates (`p := r`'s entry).
- **deep ⊆ pruned** — a verified `g` (an automorphism) equals `matchCol r (g·r)` (`matchCol_self_transport`), and
  `g·r` is a table entry (`g` permutes `branches`, `mem_allSeqs_map`). So `g` is a reference match too.

Equal verified sets ⟹ same orbits (`WordReach` depends only on generator **membership**) ⟹ `OrbitPrune.SameOrbits`
⟹ `①`/`②`/`③` transfer wholesale via `OrbitPrune.guarded_mixed_canonizer_of_sameOrbits`. **No equivariance proof on
the pruned supply**, exactly as the P3 reduction promised. As a bonus this **subsumes the dedup win** (matching from
one reference yields `≈ |table|` candidates, not `|table|²`, so the verified list — and the orbit BFS over it — is far
shorter).

⚠ **What this does NOT yet do:** it kills the `|table|²` pairing but not the `n^d` *inside* `|table|` (the sequence
enumeration). Collapsing that to a sum needs the online sequence-orbit pruning (`seqReps ≪ |allSeqs|`, measured) — a
separate, harder increment. This is the clean, provable first half.
-/

namespace ChainDescent
namespace PrunedSupply

open ChainDescent.Descend
open ChainDescent.Consume
  (Supply gens verified rep WordReach IsColAut CellIsOrbit matchCol exists_targetColour_of_mem)
open ChainDescent.DeepMatch
  (deepTable deepMatchSupply deepCol deepData allSeqs mem_deepTable_iff deepTable_col
   matchCol_self_transport mem_allSeqs_map supplyEquivariant_deepMatchSupply)
open ChainDescent.Force (Key KeyEquivariant lookaheadKey keyEquivariant_lookahead)
open ChainDescent.Composite (forceThenConsume)

variable {n : Nat}

/-! ## 1. `WordReach`, hence `SameOrbits`, depends only on generator MEMBERSHIP -/

/-- `WordReach` only reads whether a generator is **in** the list — never its position or multiplicity. -/
theorem wordReach_congr_mem {G₁ G₂ : List (Equiv.Perm (Fin n))} (h : ∀ g, g ∈ G₁ ↔ g ∈ G₂)
    {u w : Fin n} (hr : WordReach G₁ u w) : WordReach G₂ u w := by
  induction hr with
  | refl => exact WordReach.refl _
  | step _ hg ih => exact ih.step ((h _).mp hg)

/-- Two supplies whose **verified** lists have the same membership prove the same orbits. -/
theorem sameOrbits_of_verified_mem {S₁ S₂ : Supply n}
    (h : ∀ (adj : AdjMatrix n) (χ : Colouring n) (g : Equiv.Perm (Fin n)),
      g ∈ verified S₁ adj χ ↔ g ∈ verified S₂ adj χ) :
    OrbitPrune.SameOrbits S₁ S₂ := fun adj χ u w =>
  ⟨wordReach_congr_mem (h adj χ), wordReach_congr_mem (fun g => (h adj χ g).symm)⟩

/-! ## 2. The reference-matching supply -/

/-- The colouring of the first **discrete** table entry, if any. `matchCol r _` is `none` unless `r` is discrete, so
this is the only sensible reference. -/
def refCol? (adj : AdjMatrix n) (χ : Colouring n) (d : Nat) : Option (Colouring n) :=
  ((deepTable adj χ d).find? (fun p => decide (Discrete p.2.col))).map (fun p => p.2.col)

/-- **★ THE REFERENCE-MATCHING ORACLE.** Match the single reference entry against every table entry — `|table|`
colour matches instead of `|table|²`. Untrusted (`consume` re-verifies), same as `deepMatchSupply`. -/
def prunedSupply (d : Nat) : Supply n := fun adj χ =>
  let table := deepTable adj χ d
  match refCol? adj χ d with
  | none => ([], table.length * (d + 1) * CostModel.WarmRefine.warmRefineCost n)
  | some r =>
      (table.filterMap (fun q => matchCol r q.2.col),
       table.length * (d + 1) * CostModel.WarmRefine.warmRefineCost n + table.length * (n * n))

theorem gens_prunedSupply (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    gens (prunedSupply (n := n) d) adj χ
      = (refCol? adj χ d).elim []
          (fun r => (deepTable adj χ d).filterMap (fun q => matchCol r q.2.col)) := by
  show (prunedSupply (n := n) d adj χ).1 = _
  unfold prunedSupply
  cases refCol? adj χ d <;> rfl

/-- Membership in the **pruned** candidate list. -/
theorem mem_gens_prunedSupply {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (prunedSupply (n := n) d) adj χ ↔
      ∃ r, refCol? adj χ d = some r ∧ ∃ q ∈ deepTable adj χ d, matchCol r q.2.col = some g := by
  simp only [gens_prunedSupply]
  cases hr : refCol? adj χ d with
  | none => simp
  | some r =>
      simp only [Option.elim_some, List.mem_filterMap]
      constructor
      · rintro ⟨q, hq, hmc⟩; exact ⟨r, rfl, q, hq, hmc⟩
      · rintro ⟨r', hr', q, hq, hmc⟩
        obtain rfl := Option.some.inj hr'; exact ⟨q, hq, hmc⟩

/-- Membership in the **all-pairs** (`deepMatchSupply`) candidate list. -/
theorem mem_gens_deepMatchSupply_raw {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (deepMatchSupply (n := n) d) adj χ ↔
      ∃ p ∈ deepTable adj χ d, ∃ q ∈ deepTable adj χ d, matchCol p.2.col q.2.col = some g := by
  show g ∈ ((deepTable adj χ d).flatMap
    (fun p => (deepTable adj χ d).filterMap (fun q => matchCol p.2.col q.2.col))) ↔ _
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hmem⟩
    obtain ⟨q, hq, hmc⟩ := List.mem_filterMap.mp hmem
    exact ⟨p, hp, q, hq, hmc⟩
  · rintro ⟨p, hp, q, hq, hmc⟩
    exact ⟨p, hp, List.mem_filterMap.mpr ⟨q, hq, hmc⟩⟩

/-! ## 3. The reference entry is discrete, and a verified `g` maps it to another table entry -/

/-- Whatever `refCol?` returns is **discrete** (it is the `find?` predicate). -/
theorem discrete_refCol {d : Nat} {adj : AdjMatrix n} {χ : Colouring n} {r : Colouring n}
    (h : refCol? adj χ d = some r) : Discrete r := by
  unfold refCol? at h
  obtain ⟨p, hfind, hpr⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some hfind
  simpa [hpr] using of_decide_eq_true this

/-- The reference is one of the table entries' colourings. -/
theorem refCol_eq_deepCol {d : Nat} {adj : AdjMatrix n} {χ : Colouring n} {r : Colouring n}
    (h : refCol? adj χ d = some r) : ∃ p ∈ deepTable adj χ d, p.2.col = r := by
  unfold refCol? at h
  obtain ⟨p, hfind, hpr⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p, List.mem_of_find?_eq_some hfind, hpr⟩

/-- A **discrete** table entry forces the reference to exist. -/
theorem refCol_isSome_of_discrete {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {p : (Fin n × List (Fin n)) × Refine.ColData n} (hp : p ∈ deepTable adj χ d)
    (hd : Discrete p.2.col) : ∃ r, refCol? adj χ d = some r := by
  rcases h : (deepTable adj χ d).find? (fun x => decide (Discrete x.2.col)) with _ | p'
  · rw [List.find?_eq_none] at h
    exact absurd (by simpa using hd) (h p hp)
  · exact ⟨p'.2.col, by simp [refCol?, h]⟩

/-- A verified automorphism **permutes the branch cell** (it preserves colours, and `branches` is a colour class). -/
theorem mem_branches_of_isColAut {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) {v : Fin n} (hv : v ∈ branches χ) : g v ∈ branches χ := by
  obtain ⟨c, hc, hvc⟩ := exists_targetColour_of_mem hv
  exact (mem_branches_iff hc (g v)).mpr (by rw [hg.2]; exact hvc)

/-- **★ THE KEY CONSTRUCTION.** For a verified automorphism `g` and the reference entry `r = (v₀, s₀)`, the
`g`-image `(g v₀, s₀.map g)` is **also a table entry**, and its colouring is `g`-transport of `r`. So
`matchCol r (that entry) = some g` (`matchCol_self_transport`) — every verified `g` is a reference match. -/
theorem exists_image_entry {d : Nat} {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) {r : Colouring n} (hr : refCol? adj χ d = some r) :
    ∃ q ∈ deepTable adj χ d, matchCol r q.2.col = some g := by
  obtain ⟨p, hp, hpr⟩ := refCol_eq_deepCol hr
  obtain ⟨v₀, hv₀, s₀, hs₀, rfl⟩ := mem_deepTable_iff.mp hp
  have hrcol : r = deepCol adj χ (v₀ :: s₀) := by rw [← hpr]; exact deepTable_col hp
  set q : (Fin n × List (Fin n)) × Refine.ColData n :=
    ((g v₀, s₀.map g), deepData adj (Refine.warmRefineVec adj (indivOne χ (g v₀))) (s₀.map g))
    with hqdef
  refine ⟨q, ?_, ?_⟩
  · exact mem_deepTable_iff.mpr
      ⟨g v₀, mem_branches_of_isColAut hg hv₀, s₀.map g, (mem_allSeqs_map g d s₀).mpr hs₀, rfl⟩
  · have hqcol : q.2.col = deepCol adj χ (g v₀ :: s₀.map g) := by
      rw [hqdef]
      show (deepData adj (Refine.warmRefineVec adj (indivOne χ (g v₀))) (s₀.map g)).col
          = deepCol adj (Refine.warmRefineR adj (indivOne χ (g v₀))) (s₀.map g)
      rw [DeepMatch.deepData_col, Refine.warmRefineVec_col_eq]
    rw [hqcol]
    have himg : deepCol adj χ (g v₀ :: s₀.map g) = transportColouring g r := by
      have h1 : deepCol adj χ (g v₀ :: s₀.map g) = deepCol adj χ ((v₀ :: s₀).map g) := by
        simp [List.map_cons]
      rw [h1, OrbitPrune.deepCol_aut hg (v₀ :: s₀), hrcol]
    rw [himg]
    exact matchCol_self_transport g (discrete_refCol hr)

/-! ## 4. ★★★ THE VERIFIED SETS ARE EQUAL — hence `SameOrbits`, hence `①`/`②`/`③` -/

theorem verified_mem_iff (d : Nat) (adj : AdjMatrix n) (χ : Colouring n) (g : Equiv.Perm (Fin n)) :
    g ∈ verified (prunedSupply (n := n) d) adj χ ↔ g ∈ verified (deepMatchSupply (n := n) d) adj χ := by
  simp only [verified, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hmem, haut⟩
    refine ⟨?_, haut⟩
    obtain ⟨r, hr, q, hq, hmc⟩ := mem_gens_prunedSupply.mp hmem
    obtain ⟨p, hp, hpr⟩ := refCol_eq_deepCol hr
    exact mem_gens_deepMatchSupply_raw.mpr ⟨p, hp, q, hq, by rw [hpr]; exact hmc⟩
  · rintro ⟨hmem, haut⟩
    refine ⟨?_, haut⟩
    obtain ⟨p, hp, q, hq, hmc⟩ := mem_gens_deepMatchSupply_raw.mp hmem
    have hdp : Discrete p.2.col := by
      by_contra hnd
      simp [matchCol, dif_neg hnd] at hmc
    obtain ⟨r, hr⟩ := refCol_isSome_of_discrete hp hdp
    obtain ⟨q', hq', hmc'⟩ := exists_image_entry haut hr
    exact mem_gens_prunedSupply.mpr ⟨r, hr, q', hq', hmc'⟩

/-- **★★★ `prunedSupply d` PROVES THE SAME ORBITS AS `deepMatchSupply d`** — with no equivariance obligation of its
own. This is the entire `①` obligation of the pruned supply, discharged. -/
theorem sameOrbits_deepMatchSupply (d : Nat) :
    OrbitPrune.SameOrbits (deepMatchSupply (n := n) d) (prunedSupply (n := n) d) :=
  sameOrbits_of_verified_mem (fun adj χ g => (verified_mem_iff d adj χ g).symm)

/-- **★★★ THE PRUNED MIXED CANONIZER.** `①a`/`①b`/`①c` (sound, complete, iso-invariant answer-and-flag) for the
guarded composite over the **cheaper** reference-matching supply — inherited wholesale from `deepMatchSupply`'s
equivariance through the `SameOrbits` reduction, with **no** equivariance proof on `prunedSupply`. -/
theorem prunedSupply_guarded_canonizer {d : Nat} {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key (prunedSupply (n := n) d)))) :=
  OrbitPrune.guarded_mixed_canonizer_of_sameOrbits hk
    (supplyEquivariant_deepMatchSupply d) (sameOrbits_deepMatchSupply d)

/-- The same, with the concrete `lookaheadKey`. -/
theorem prunedSupply_lookahead_canonizer (d : Nat) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (lookaheadKey (n := n)) (prunedSupply (n := n) d)))) :=
  prunedSupply_guarded_canonizer keyEquivariant_lookahead

end PrunedSupply
end ChainDescent
