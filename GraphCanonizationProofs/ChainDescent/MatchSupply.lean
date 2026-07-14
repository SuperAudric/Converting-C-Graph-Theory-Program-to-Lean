import ChainDescent.Consume

/-!
# `matchSupply` — the COLOUR-MATCH oracle, in the descent's own vocabulary

(`chain-descent-cascade-oracle.md` §C.4; `CascadeOracle.matchOracle`.)

## Why this is not a port

The cascade oracle (`CascadeOracle.matchOracle`) is the project's answer to "which branch vertices are
interchangeable". It is **construct-and-check**: individualize `v`, individualize `w`, refine both; if the two
refinements are discrete, build the permutation matching one colour-order to the other, and **return it only if it
verifies** as an automorphism. Soundness is unconditional (`matchOracle_orbitMapSpec`); firing is conditional on the
node *discretizing* (`matchOracle_fires_of_insertDiscrete` — the `CellsAreOrbits`-free form).

Its statements live in the **spine chain** vocabulary — a `PMatrix` `P` plus a committed `Finset` `D`, with
`Aut_D = ResidualAut adj P D = IsAut ∧ P-preserving ∧ FixesPointwise D`. The descent records the same information
in a single **colouring** `χ` (committed vertices carry unique colours; `indivOne` is index-free). The two
vocabularies agree on the part that matters — `Spine.IsAut π adj` is *literally* `Consume.IsColAut`'s first
conjunct — so rather than port the chain apparatus, this file rebuilds the same construct-and-check oracle over
`(adj, χ)` directly. Consequences:

* **soundness is free** — the resolver already re-verifies every candidate (`Consume.verified`), so a *wrong*
  construction costs branches, never correctness. Nothing here is trusted;
* **firing is a theorem, not a hypothesis** — `matchCandidate_eq_of_isColAut` below shows the construction does not
  merely *find* an automorphism, it **reconstructs exactly the one that exists**;
* and the supply is a **structural function of `(adj, χ)`**, which is what `Stall.StallEquivariant` (the flag's new
  obligation) needs — unlike the demo supplies, which hand back a fixed generator list and provably break `①c`.

## The firing theorem, stated honestly

> **`cellIsOrbit_matchSupply`** — if individualizing a branch vertex **discretizes** (the cascade's `hdisc` / depth
> witness), then `matchSupply` recovers **every** colouring-preserving automorphism between branch vertices, so a
> branch cell that *is* an orbit is certified as one.

That is exactly the cascade oracle's honest strength — no `CellsAreOrbits`, no localisation hypothesis — expressed
where `consume` can consume it. What it does **not** cover is the multi-step regime (`lockstep_disc_imp_stab_trivial`:
a one-step discretizing colour match provably cannot harvest a multi-step moved orbit), which is where the
cross-branch harvest lives and where the Cameron / node-4 obstruction sits.
-/

namespace ChainDescent
namespace Consume

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend

variable {n : Nat}

/-! ## 1. The colour-match permutation

Two discrete colourings each order the vertices. The permutation carrying one order to the other is computable
(`rankInv`), and it is a genuine `Equiv` because `vertexRank` is injective on a discrete colouring. -/

/-- **The colour-match permutation**: send the vertex of rank `i` under `ψv` to the vertex of rank `i` under `ψw`. -/
def rankSwap (ψv ψw : Colouring n) (hv : Discrete ψv) (hw : Discrete ψw) : Equiv.Perm (Fin n) where
  toFun u := rankInv ψw (Colouring.vertexRank ψv u)
  invFun u := rankInv ψv (Colouring.vertexRank ψw u)
  left_inv u := by
    have hinj : Function.Injective (Colouring.vertexRank ψv) := fun a b hab =>
      (Colouring.rankPerm ψv hv).injective hab
    refine hinj ?_
    rw [rankInv_spec ψv hv, rankInv_spec ψw hw]
  right_inv u := by
    have hinj : Function.Injective (Colouring.vertexRank ψw) := fun a b hab =>
      (Colouring.rankPerm ψw hw).injective hab
    refine hinj ?_
    rw [rankInv_spec ψw hw, rankInv_spec ψv hv]

@[simp] theorem rankSwap_apply (ψv ψw : Colouring n) (hv : Discrete ψv) (hw : Discrete ψw) (u : Fin n) :
    rankSwap ψv ψw hv hw u = rankInv ψw (Colouring.vertexRank ψv u) := rfl

/-! ## 2. The candidate — construct, do not trust -/

/-- The refinement reached by individualizing `v` (materialised — **never** a `… → Colouring n` definition; see the
eta-expansion trap in `Refine.lean` §4). -/
def lookData (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Refine.ColData n :=
  Refine.warmRefineVec adj (indivOne χ v)

theorem lookData_col (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (lookData adj χ v).col = Refine.warmRefineR adj (indivOne χ v) :=
  Refine.warmRefineVec_col_eq adj (indivOne χ v)

/-- **The construct-and-check candidate, at the level of COLOURINGS.** If both refinements discretize, hand back
the colour-match permutation. It is a *candidate only* — `Consume.verified` re-checks it edge-by-edge, so nothing
here needs to be trusted.

⚠ Phrased on `Colouring`, not `ColData`, **on purpose**: the transport lemmas (§5) relate the *colourings* of two
`ColData` values that are not themselves equal, and a `ColData`-level `dite` cannot be rewritten under. -/
def matchCol (ψv ψw : Colouring n) : Option (Equiv.Perm (Fin n)) :=
  if hv : Discrete ψv then
    if hw : Discrete ψw then some (rankSwap ψv ψw hv hw) else none
  else none

/-- The same, reading the materialised `ColData` (the form `matchSupply` pairs over). -/
def matchFrom (dv dw : Refine.ColData n) : Option (Equiv.Perm (Fin n)) :=
  matchCol dv.col dw.col

def matchCandidate (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  matchFrom (lookData adj χ v) (lookData adj χ w)

/-- **★★ THE ORACLE RECONSTRUCTS THE AUTOMORPHISM EXACTLY.**

If some colouring-preserving automorphism `α` carries `v` to `w`, and individualizing `v` **discretizes**, then the
construction fires **and returns `α` itself**. It does not merely find *an* automorphism — the colour-match
permutation *is* `α`.

The proof is the descent's own transport layer: `α·adj = adj` and `α·χ = χ`, so refining after individualizing
`w = α v` gives exactly `ψv ∘ α⁻¹`; ranks therefore transport (`vertexRank_transport`), and the rank-matching
permutation is forced to be `α`. -/
theorem matchCandidate_eq_of_isColAut {adj : AdjMatrix n} {χ : Colouring n}
    {α : Equiv.Perm (Fin n)} (hα : IsColAut adj χ α) (v : Fin n)
    (hdisc : Discrete ((lookData adj χ v).col)) :
    matchCandidate adj χ v (α v) = some α := by
  -- the `w`-side refinement is the `v`-side one, transported by `α`
  have hψ : (lookData adj χ (α v)).col = transportColouring α ((lookData adj χ v).col) := by
    rw [lookData_col, lookData_col]
    -- individualizing `α v` is individualizing `v`, transported (`α` preserves `χ`)
    have hind : transportColouring α (indivOne χ v) = indivOne χ (α v) := by
      rw [← indivOne_transport α χ v, hα.transport]
    -- and refinement is equivariant, with `α·adj = adj`
    have h := Refine.refineEquivariant_encodeFree α adj (indivOne χ v)
    rw [hα.relabel, hind] at h
    simpa [Refine.refineV_encodeFree] using h
  have hdw : Discrete ((lookData adj χ (α v)).col) := by
    rw [hψ]; exact (discrete_transport α _).mpr hdisc
  -- so the rank-matching permutation sends `u ↦ α u`
  have hrank : ∀ u : Fin n,
      rankInv ((lookData adj χ (α v)).col) (Colouring.vertexRank ((lookData adj χ v).col) u) = α u := by
    intro u
    have hinj : Function.Injective (Colouring.vertexRank ((lookData adj χ (α v)).col)) := fun a b hab =>
      (Colouring.rankPerm _ hdw).injective hab
    refine hinj ?_
    rw [rankInv_spec _ hdw]
    rw [hψ]
    exact (vertexRank_transport α ((lookData adj χ v).col) u).symm
  unfold matchCandidate matchFrom matchCol
  rw [dif_pos hdisc, dif_pos hdw]
  congr 1
  exact Equiv.ext (fun u => by rw [rankSwap_apply]; exact hrank u)

/-! ## 3. The supply -/

/-- **★ THE COLOUR-MATCH SUPPLY.** Query the construct-and-check candidate on every ordered pair of branch vertices
and hand back everything it built. Untrusted, as always: `Consume.verified` filters it through the decidable
`IsColAut` check, so `consume_canonizer` continues to hold for it with no obligation whatsoever.

⚠ **The refinements are materialised ONCE, before pairing.** The obvious phrasing — `flatMap` over `v`, `filterMap`
over `w`, calling `matchCandidate adj χ v w` — recomputes `lookData adj χ v` for **every pair**, i.e. `|cell|²`
refinements where `|cell|` suffice. That is an `O(n)` factor in the *algorithm*, not merely in a test: measured, it
was the difference between a 3.5-minute and a ~20-second canonization of `F12`. Pairing over the *materialised*
`ColData` list keeps it at one refinement per branch. -/
def matchSupply : Supply n := fun adj χ =>
  let data : List (Fin n × Refine.ColData n) :=
    (branches χ).map (fun v => (v, lookData adj χ v))
  (data.flatMap (fun p => data.filterMap (fun q => matchFrom p.2 q.2)),
   -- ONE refinement per branch, then `|cell|²` cheap rank-matches
   (branches χ).length * CostModel.WarmRefine.warmRefineCost n
     + (branches χ).length * (branches χ).length * (n * n))

theorem mem_gens_matchSupply {adj : AdjMatrix n} {χ : Colouring n} {v w : Fin n}
    (hv : v ∈ branches χ) (hw : w ∈ branches χ) {π : Equiv.Perm (Fin n)}
    (h : matchCandidate adj χ v w = some π) : π ∈ gens (matchSupply (n := n)) adj χ := by
  refine List.mem_flatMap.mpr ⟨(v, lookData adj χ v), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · exact List.mem_filterMap.mpr ⟨(w, lookData adj χ w), List.mem_map.mpr ⟨w, hw, rfl⟩, h⟩

/-- Everything the supply produces and the resolver keeps is a genuine automorphism (this is just
`isColAut_of_mem_verified`, recorded here for the firing argument). -/
theorem mem_verified_matchSupply {adj : AdjMatrix n} {χ : Colouring n}
    {α : Equiv.Perm (Fin n)} (hα : IsColAut adj χ α) {v : Fin n} (hv : v ∈ branches χ)
    (hαv : α v ∈ branches χ) (hdisc : Discrete ((lookData adj χ v).col)) :
    α ∈ verified (matchSupply (n := n)) adj χ := by
  refine List.mem_filter.mpr ⟨?_, by simpa using hα⟩
  exact mem_gens_matchSupply hv hαv (matchCandidate_eq_of_isColAut hα v hdisc)

/-! ## 4. ★★★ THE FIRING THEOREM — the cascade oracle's honest strength -/

/-- **The one-step depth witness** (`hdisc` in the cascade oracle's completeness): individualizing any branch vertex
discretizes the refinement. This is *the* condition `matchOracle_fires_of_insertDiscrete` fires under, and it is
where the Cameron / node-4 obstruction lives — not in the construction. -/
def Discretizing (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ v ∈ branches χ, Discrete ((lookData adj χ v).col)

/-- **★★★ `matchSupply` CERTIFIES EVERY ORBIT IT CAN SEE.** At a discretizing node, any colouring-preserving
automorphism between two branch vertices is **recovered, verified, and available to `consume`** — so a branch cell
that really is a single orbit is certified as one, and `consume` collapses it to one branch
(`consume_singleton_of_cellIsOrbit`).

This is the cascade oracle's `hdisc`-only firing (`matchOracle_fires_of_insertDiscrete`), with **no**
`CellsAreOrbits` and **no** localisation hypothesis, transported into the resolver's vocabulary. -/
theorem cellIsOrbit_matchSupply {adj : AdjMatrix n} {χ : Colouring n}
    (hd : Discretizing adj χ)
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ α : Equiv.Perm (Fin n),
        IsColAut adj χ α ∧ α u = w) :
    CellIsOrbit (matchSupply (n := n)) adj χ := by
  intro u hu w hw
  obtain ⟨α, hα, hαu⟩ := horb u hu w hw
  -- the automorphism is in the *verified* generator list, so one step of `WordReach` suffices
  have hmem : α ∈ verified (matchSupply (n := n)) adj χ :=
    mem_verified_matchSupply hα hu (by rw [hαu]; exact hw) (hd u hu)
  have := (WordReach.refl (G := verified (matchSupply (n := n)) adj χ) u).step hmem
  rwa [hαu] at this

/-! ## 5. ★★ TRANSPORT — the supply is a STRUCTURAL function, hence EQUIVARIANT

This is what `SupplyTransport.GensEquivariant` asks for, and it is the reason `matchSupply` — unlike a supply that
hands back a *fixed* generator list — can carry the **flag**. Soundness needs nothing from the supply
(`consume_canonizer` holds for every supply, because a covering resolver is *value*-invisible); the **flag** does,
because `Stall.stalled` reads the narrowing's *length*, which depends on how many orbits the supply actually
proves. See `SupplyTransport.lean` for the full argument and for the `#guard`ed counterexample that shows the
obligation is not free.

Everything below is bookkeeping around one fact: **the colour-match permutation conjugates.** `rankSwap` is built
from ranks, ranks transport (`vertexRank_transport`), so `rankSwap (σ·ψv) (σ·ψw) = σ · rankSwap ψv ψw · σ⁻¹`. -/

/-- `rankInv` transports: the vertex of rank `i` under `σ·ψ` is the `σ`-image of the vertex of rank `i` under
`ψ`. -/
theorem rankInv_transport (σ : Equiv.Perm (Fin n)) {ψ : Colouring n} (hd : Discrete ψ) (i : Fin n) :
    rankInv (transportColouring σ ψ) i = σ (rankInv ψ i) := by
  have hd' : Discrete (transportColouring σ ψ) := (discrete_transport σ ψ).mpr hd
  have hinj : Function.Injective (Colouring.vertexRank (transportColouring σ ψ)) := fun a b hab =>
    (Colouring.rankPerm _ hd').injective hab
  refine hinj ?_
  rw [rankInv_spec _ hd', vertexRank_transport σ ψ (rankInv ψ i), rankInv_spec ψ hd]

/-- **★ THE COLOUR-MATCH PERMUTATION CONJUGATES.** -/
theorem rankSwap_conj (σ : Equiv.Perm (Fin n)) {ψv ψw : Colouring n}
    (hv : Discrete ψv) (hw : Discrete ψw)
    (hv' : Discrete (transportColouring σ ψv)) (hw' : Discrete (transportColouring σ ψw)) :
    rankSwap (transportColouring σ ψv) (transportColouring σ ψw) hv' hw'
      = σ * rankSwap ψv ψw hv hw * σ⁻¹ := by
  refine Equiv.ext (fun u => ?_)
  have hrank : Colouring.vertexRank (transportColouring σ ψv) u
      = Colouring.vertexRank ψv (σ.symm u) := by
    have h := vertexRank_transport σ ψv (σ.symm u)
    rwa [Equiv.apply_symm_apply] at h
  show rankInv (transportColouring σ ψw) (Colouring.vertexRank (transportColouring σ ψv) u)
      = σ (rankSwap ψv ψw hv hw (σ.symm u))
  rw [hrank, rankInv_transport σ hw]
  rfl

/-- The candidate constructor transports (up to conjugation), **including its failure mode**: it declines to
construct on `σ·G` exactly where it declines on `G`. -/
theorem matchCol_transport (σ : Equiv.Perm (Fin n)) (ψv ψw : Colouring n) :
    matchCol (transportColouring σ ψv) (transportColouring σ ψw)
      = (matchCol ψv ψw).map (fun t => σ * t * σ⁻¹) := by
  unfold matchCol
  by_cases hv : Discrete ψv
  · have hv' : Discrete (transportColouring σ ψv) := (discrete_transport σ ψv).mpr hv
    by_cases hw : Discrete ψw
    · have hw' : Discrete (transportColouring σ ψw) := (discrete_transport σ ψw).mpr hw
      rw [dif_pos hv', dif_pos hw', dif_pos hv, dif_pos hw]
      simp [rankSwap_conj σ hv hw hv' hw']
    · have hw' : ¬ Discrete (transportColouring σ ψw) := fun hc =>
        hw ((discrete_transport σ ψw).mp hc)
      rw [dif_pos hv', dif_neg hw', dif_pos hv, dif_neg hw]
      rfl
  · have hv' : ¬ Discrete (transportColouring σ ψv) := fun hc =>
      hv ((discrete_transport σ ψv).mp hc)
    rw [dif_neg hv', dif_neg hv]
    rfl

/-- The look-ahead refinement transports (refiner equivariance + `indivOne_transport`). -/
theorem lookData_col_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) :
    (lookData (relabelAdj σ adj) (transportColouring σ χ) (σ v)).col
      = transportColouring σ ((lookData adj χ v).col) := by
  rw [lookData_col, lookData_col, indivOne_transport σ χ v]
  simpa [Refine.refineV_encodeFree] using Refine.refineEquivariant_encodeFree σ adj (indivOne χ v)

/-- **★ THE CANDIDATE CONJUGATES.** -/
theorem matchCandidate_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v w : Fin n) :
    matchCandidate (relabelAdj σ adj) (transportColouring σ χ) (σ v) (σ w)
      = (matchCandidate adj χ v w).map (fun t => σ * t * σ⁻¹) := by
  unfold matchCandidate matchFrom
  rw [lookData_col_transport, lookData_col_transport, matchCol_transport]

/-- **Membership in the supply, characterised.** The generators are exactly the candidates the construction built
on some ordered pair of branch vertices. -/
theorem mem_gens_matchSupply_iff {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)} :
    g ∈ gens (matchSupply (n := n)) adj χ ↔
      ∃ v ∈ branches χ, ∃ w ∈ branches χ, matchCandidate adj χ v w = some g := by
  constructor
  · intro hg
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨q, hq2, hmf⟩ := List.mem_filterMap.mp hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq2
    exact ⟨v, hv, w, hw, hmf⟩
  · rintro ⟨v, hv, w, hw, h⟩
    exact mem_gens_matchSupply hv hw h

end Consume
end ChainDescent
