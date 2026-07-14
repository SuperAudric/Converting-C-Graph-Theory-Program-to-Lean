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

/-- **The construct-and-check candidate.** Individualize `v` and `w`, refine both; if both discretize, hand back the
colour-match permutation. It is a *candidate only* — `Consume.verified` re-checks it edge-by-edge, so nothing here
needs to be trusted. -/
def matchCandidate (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  let ψv : Colouring n := (lookData adj χ v).col
  let ψw : Colouring n := (lookData adj χ w).col
  if hv : Discrete ψv then
    if hw : Discrete ψw then some (rankSwap ψv ψw hv hw) else none
  else none

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
  unfold matchCandidate
  simp only []
  rw [dif_pos hdisc, dif_pos hdw]
  congr 1
  exact Equiv.ext (fun u => by rw [rankSwap_apply]; exact hrank u)

/-! ## 3. The supply -/

/-- **★ THE COLOUR-MATCH SUPPLY.** Query the construct-and-check candidate on every ordered pair of branch vertices
and hand back everything it built. Untrusted, as always: `Consume.verified` filters it through the decidable
`IsColAut` check, so `consume_canonizer` continues to hold for it with no obligation whatsoever. -/
def matchSupply : Supply n := fun adj χ =>
  ((branches χ).flatMap (fun v =>
      (branches χ).filterMap (fun w => matchCandidate adj χ v w)),
   -- one refinement per query, `|cell|²` queries
   (branches χ).length * (branches χ).length
     * (2 * CostModel.WarmRefine.warmRefineCost n + n * n))

theorem mem_gens_matchSupply {adj : AdjMatrix n} {χ : Colouring n} {v w : Fin n}
    (hv : v ∈ branches χ) (hw : w ∈ branches χ) {π : Equiv.Perm (Fin n)}
    (h : matchCandidate adj χ v w = some π) : π ∈ gens (matchSupply (n := n)) adj χ := by
  refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
  exact List.mem_filterMap.mpr ⟨w, hw, h⟩

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

end Consume
end ChainDescent
