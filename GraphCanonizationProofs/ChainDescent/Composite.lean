import ChainDescent.Consume
import ChainDescent.Force

/-!
# `forceThenConsume` — THE MIXED RESOLVER (both moves, one cell)

(`docs/chain-descent-mixed-composition.md` §1.3 + §1.5; `chain-descent-ir-blindspot-solver.md` §11.11.)

## Why this file has to exist

`descend` takes **one** resolver. `Consume.lean` and `Force.lean` each build one, and each is a canonizer on its
own — but the engine the project actually models is **interleaved** (IR §11.11): almost every real residue is
*mixed*, and needs **both** moves at the **same** cell — consume the symmetry that is there, force the rest. With
only the two separate instances, the mixed object — the one this whole track is named for — did not exist.

## Why it did not just drop out of the existing contract

The composite is **neither** of the two sufficient conditions:

* it is **not `Covering`** — force changes the aggregate (that is the point of forcing);
* it is **not `NarrowEquivariant`** — consume's choice of orbit representative is deliberately *non*-equivariant
  (orbit members are indistinguishable to refinement, so no canonical choice exists).

So it satisfies neither, and could not be admitted. The fix (`Descend.lean` §9, sufficient condition 3) is to see
that both routes are the *same* condition against different reference lists, and to generalize the reference to an
arbitrary **equivariant intermediate `N`** (`CoveringOfAt rf R N` + `NarrowFnEquivariant N`):

| route | `N` |
|---|---|
| `Covering` (consume alone) | `branches` |
| `NarrowEquivariant` (force alone) | `narrow R` itself |
| **the composite** | **the FORCED set** |

Force narrows `branches` equivariantly down to `N`; consume then **covers `N`** — its discards are redundant
*within* `N`. One contract, three instances.

## ★ The lemma that makes it true: the forced set is a UNION OF ORBITS

The composite is sound only because consume, run inside the forced set, cannot **escape** it: an orbit
representative of a kept branch must itself be kept. That is exactly `Force.mem_keepMin_of_aut`, and it follows
from `KeyEquivariant` alone — an equivariant key is **constant on colouring-preserving automorphism orbits**
(`Force.keyV_aut_invariant`), so the argmin set is a union of whole orbits and never cuts one in half.

**Consequence — the ORDER IS FORCED, for the proof.** `force`-then-`consume` composes cleanly; the reverse order
(consume first, then rank the surviving representatives) is *value*-equivalent but has no such clean covering
argument, because the intermediate list is then non-equivariant. The docs' remark that the schedule "is an
efficiency concern, never a correctness one" is right about the **answer** and wrong about the **proof**.

## ★★ What it buys: completeness on BOTH domains

The two firing theorems compose. The composite narrows a cell to **one branch** whenever *either* route can act:

* `forceThenConsume_singleton_of_cellIsOrbit` — the cell is a single orbit of the supply's verified generators
  (the **symmetric** case: consume finishes it);
* `forceThenConsume_singleton_of_separating` — the key separates the cell (the **rigid** case: force finishes it).

Neither is a soundness hypothesis — the composite is a canonizer regardless (`composite_canonizer`). They are the
**②/firing** obligations, and they are precisely the two jobs the oracle and the rigid solver were always meant to
do. Cells where **neither** holds are **the residue**.
-/

namespace ChainDescent
namespace Composite

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV KeyEquivariant keepMin forceBy)
open ChainDescent.Consume (Supply verified rep)

variable {n : Nat}

/-! ## 1. The object -/

/-- **The forced set**, as an intermediate narrowing (`NarrowFn`) — the reference list the composite covers. -/
def forcedSet (key : Key n) : NarrowFn n := fun adj χ => keepMin key adj χ (branches χ)

/-- **★ THE MIXED RESOLVER.** Force first (narrow equivariantly to the least-key branches), then consume (keep one
orbit representative among those). Both moves, at one cell, in one resolver — this is the object the interleaved
model asks for.

Costs are **summed**, not hidden: the force half is billed for every key evaluation, the consume half for the
supply's own work plus verification plus the orbit search. -/
def forceThenConsume (key : Key n) (S : Supply n) : Resolver n := fun adj χ B =>
  let F := forceBy key adj χ B
  let B' := F.1.getD B
  let C := Consume.consume S adj χ B'
  (C.1, F.2 + C.2)

theorem narrow_forceThenConsume (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceThenConsume key S) adj χ
      = ((forcedSet key adj χ).map (rep (verified S adj χ))).dedup := rfl

/-- The forced set sits inside the branch cell. -/
theorem forcedSet_subset (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) {v : Fin n}
    (hv : v ∈ forcedSet key adj χ) : v ∈ branches χ :=
  (Force.mem_keepMin_iff v |>.mp hv).1

/-- The forced set is nonempty on a non-discrete node. -/
theorem forcedSet_ne_nil (key : Key n) (adj : AdjMatrix n) {χ : Colouring n} (hd : ¬ Discrete χ) :
    forcedSet key adj χ ≠ [] := by
  have := (Force.narrowProper_forceBy key).1 adj χ hd
  rwa [Force.narrow_forceBy] at this

/-! ## 2. ★ THE KEY LEMMA — an orbit representative never escapes the forced set

This is where `KeyEquivariant` does the work a second time. The representative `rep G b` of a kept branch `b` is
reached from `b` by a *verified automorphism* `α`; an equivariant key cannot tell `b` from `α b`; so `rep G b`
attains the same (minimal) key and is kept too. Without this, consume could pick a representative outside the
forced set and the covering argument would collapse. -/

theorem rep_mem_forcedSet {key : Key n} (hk : KeyEquivariant key) (S : Supply n)
    (adj : AdjMatrix n) (χ : Colouring n) {b : Fin n} (hb : b ∈ forcedSet key adj χ) :
    rep (verified S adj χ) b ∈ forcedSet key adj χ := by
  have hbB : b ∈ branches χ := forcedSet_subset key adj χ hb
  -- the representative is reached from `b` by a verified colouring-preserving automorphism
  obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (adj := adj) (χ := χ)
    (fun _ hg => Consume.isColAut_of_mem_verified hg) b
  have hrepB : rep (verified S adj χ) b ∈ branches χ :=
    Consume.orbit_subset_branches hbB (Consume.rep_mem_orbit _ b)
  have := Force.mem_keepMin_of_aut hk hα.relabel hα.transport hb (by rw [hαb]; exact hrepB)
  rwa [hαb] at this

/-! ## 3. Soundness — the composite meets the resolver contract -/

/-- The forced set is an **equivariant** intermediate (it is exactly `narrow (forceBy key)`). -/
theorem narrowFnEquivariant_forcedSet {key : Key n} (hk : KeyEquivariant key) :
    NarrowFnEquivariant (forcedSet key) :=
  fun σ adj χ => Force.narrowEquivariant_forceBy hk σ adj χ

/-- **★★ THE COMPOSITE COVERS THE FORCED SET.** Consume's discards *inside* the forced set are redundant: each is
value-equal (`Consume.branchVal_eq_of_isColAut`, i.e. `descend_transport` at an automorphism) to the kept
representative, and by `rep_mem_forcedSet` that representative is still in the forced set. -/
theorem coveringOfAt_forceThenConsume {rf : Refiner n} (hre : RefineEquivariant rf)
    {key : Key n} (hk : KeyEquivariant key) (S : Supply n) :
    CoveringOfAt rf (forceThenConsume key S) (forcedSet key) := by
  intro fuel ih adj χ
  set R := forceThenConsume key S with hR
  set G := verified S adj χ with hG
  set f : Fin n → Option (Labelled n) :=
    fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 with hf
  -- every branch of the forced set is value-equal to its orbit representative
  have hval : ∀ b : Fin n, f (rep G b) = f b := by
    intro b
    obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (adj := adj) (χ := χ)
      (fun _ hg => Consume.isColAut_of_mem_verified hg) b
    rw [hf]
    simp only
    rw [← hαb]
    exact Consume.branchVal_eq_of_isColAut hre ih adj χ hα b
  refine aggregate_congr_mem ?_
  intro x
  rw [narrow_forceThenConsume, ← hG]
  constructor
  · -- kept ⟹ present over the forced set (the representative stays inside it)
    intro hx
    obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact List.mem_map.mpr ⟨v, hbv ▸ rep_mem_forcedSet hk S adj χ hb, hvx⟩
  · -- over the forced set ⟹ present among the kept (its representative carries the same value)
    intro hx
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
    refine List.mem_map.mpr ⟨rep G b, ?_, ?_⟩
    · exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    · rw [hval b]; exact hbx

/-- **★★★ THE MIXED RESOLVER MEETS THE CONTRACT.** Via the hybrid route: it covers an equivariant intermediate. -/
theorem narrowTransport_forceThenConsume {rf : Refiner n} (hre : RefineEquivariant rf)
    {key : Key n} (hk : KeyEquivariant key) (S : Supply n) :
    NarrowTransport rf (forceThenConsume key S) :=
  narrowTransport_of_coveringOfAt hre (narrowFnEquivariant_forcedSet hk)
    (coveringOfAt_forceThenConsume hre hk S)

/-- The composite is a **proper** narrowing (nonempty, inside the cell) — the totality hypothesis. -/
theorem narrowProper_forceThenConsume {key : Key n} (S : Supply n) :
    NarrowProper (forceThenConsume key S) := by
  constructor
  · intro adj χ hd
    rw [narrow_forceThenConsume]
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (forcedSet_ne_nil key adj hd)
    intro hnil
    have : rep (verified S adj χ) b ∈ ((forcedSet key adj χ).map (rep (verified S adj χ))).dedup :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    rw [hnil] at this
    exact absurd this (List.not_mem_nil)
  · intro adj χ v hv
    rw [narrow_forceThenConsume] at hv
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact hbv ▸ Consume.orbit_subset_branches (forcedSet_subset key adj χ hb)
      (Consume.rep_mem_orbit _ b)

/-! ## 4. ★ THE CAPSTONE -/

/-- **★★★ THE MIXED CANONIZER — both moves, one object, sound and total.**

`①a`/`①b`/`①c` plus totality, modulo **nothing but `KeyEquivariant key`** — and *nothing at all* on the oracle
supply, which stays untrusted. This is the object the interleaved model (IR §11.11) describes, and it is now the
one `descend` can actually be run on. -/
theorem composite_canonizer {key : Key n} (hk : KeyEquivariant key) (S : Supply n) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFree (n := n)) (forceThenConsume key S))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFree (n := n)) (forceThenConsume key S) adj ≠ none :=
  ⟨Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFree
      (narrowTransport_forceThenConsume Refine.refineEquivariant_encodeFree hk S),
   fun adj => Descend.canonForm?_ne_none Refine.refineSplits_encodeFree
      (narrowProper_forceThenConsume S) adj⟩

/-- The runnable version. -/
theorem composite_canonizer_fast {key : Key n} (hk : KeyEquivariant key) (S : Supply n) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenConsume key S))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenConsume key S) adj ≠ none := by
  rw [Refine.encodeFreeFast_eq]
  exact composite_canonizer hk S

/-! ## 5. ★★ FIRING — the composite removes ALL branching on BOTH domains

This is the payoff, and the thing neither resolver could deliver alone. Each theorem says: on its domain, the
mixed resolver narrows the cell to **one** branch — no fan-out at all. -/

/-- **★★★ THE SYMMETRIC CASE.** If the branch cell is a single orbit of the supply's verified generators, the
composite narrows it to **one** branch. (Force provably cannot fire here — `Force.forceBy_no_narrowing_on_orbit` —
so this is consume's domain, and consume finishes it completely.) -/
theorem forceThenConsume_singleton_of_cellIsOrbit {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (hd : ¬ Discrete χ) (horb : Consume.CellIsOrbit S adj χ) :
    (narrow (forceThenConsume key S) adj χ).length = 1 := by
  rw [narrow_forceThenConsume]
  refine Consume.dedup_map_length_one (forcedSet_ne_nil key adj hd) (fun a ha b hb => ?_)
  exact Consume.rep_const_of_cellIsOrbit horb
    (forcedSet_subset key adj χ ha) (forcedSet_subset key adj χ hb)

/-- **★★★ THE RIGID CASE.** If the key **separates** the branch cell, the composite narrows it to **one** branch.
(Consume provably cannot fire here — a separating key means no two branches are automorphic — so this is force's
domain, and force finishes it completely.)

This is the precise firing obligation the rigid solver's key inherits: **separate the cell**. It is §11.12's P1/P3,
on the ②-side of the ledger, in one line. -/
theorem forceThenConsume_singleton_of_separating {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (hd : ¬ Discrete χ)
    (hsep : ∀ u ∈ branches χ, ∀ w ∈ branches χ, keyV key adj χ u = keyV key adj χ w → u = w) :
    (narrow (forceThenConsume key S) adj χ).length = 1 := by
  -- force alone already collapses the cell to a singleton; consume then maps that one branch to its rep
  have hone : (forcedSet key adj χ).length = 1 := by
    have := Force.forceBy_singleton_of_separating (key := key) (adj := adj) (χ := χ) hd hsep
    rwa [Force.narrow_forceBy] at this
  rw [narrow_forceThenConsume]
  refine Consume.dedup_map_length_one (fun hnil => by rw [hnil] at hone; simp at hone)
    (fun a ha b hb => ?_)
  -- a one-element list is trivially constant under any map
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hone
  rw [hv] at ha hb
  rw [List.mem_singleton.mp ha, List.mem_singleton.mp hb]

/-! ### ★★★ PARTIAL POWER ⟹ PARTIAL PROGRESS (the anti-perfectionism theorem)

The two singleton theorems above are the **perfect endpoints**, and on their own they are a trap: read as the whole
story they say *"only a perfect oracle or a perfect key counts"*, which is the opposite of the project's own
"over-splitting is safe" rule — and they say **nothing at all** about the realistic middle (a cell splitting into
three orbits, a key sorting it into three classes).

`forceThenConsume_narrows_of_partial` is the honest statement. **Any** capability from **either** side — the supply
proving a *single* automorphism between two branches, or the key separating a *single* pair — **strictly** reduces
the fan-out. No threshold, no cliff, no perfection required: a resolver is rewarded for exactly what it can prove
and penalized for nothing it cannot. The singleton theorems are then just the case where the reward is total.

**★ What the force/consume split really buys: ATTRIBUTION.** At a branch cell the dichotomy is exhaustive — a
choice between two vertices either leaves the reachable output matrices unchanged (a **symmetry**, consume's to
take) or it changes them (a **real decision**, force's to take). So **every surviving branch pair is assignable to
exactly one resolver's weakness**: either the supply failed to connect an automorphic pair, or the key failed to
separate a non-automorphic one. `forceThenConsume_stall` is that attribution, and it makes residual weakness
*localizable* — and, with the graded theorems above, *quantifiable* (how many pairs each side left on the table).
That is a measuring instrument for improving the resolvers, and it is the practical payoff of the tautology.

⚠ **It is NOT an impossibility argument, and must not be read as one.** A key that separated exactly the
non-automorphic pairs would collapse every cell to one branch — i.e. **a perfect key is *equivalent to* GI ∈ P**.
That makes it the route's **target**, not a barrier: this project's premise is that polynomial is not a wall (see
`00-START-HERE` §1, "isolate, don't close"). Nothing here licenses assuming such a key is unreachable — and no
theorem in this file does.

Either way, the `②` ledger is **additive**: a rigid solver that handles *part* of its residue, or an oracle that
finds *some* of `Aut`, contributes *proportionally*. The residue is what is left after every partial contribution. -/

/-- **★★★ THE ANTI-PERFECTIONISM THEOREM — partial power gives partial progress.**

If *either* the key separates two branches, *or* the supply's verified generators connect two distinct branches,
the composite's narrowing is **strictly shorter** than the full branch list. Neither resolver has to be complete,
or even good; each is rewarded for precisely the distinctions it can prove. -/
theorem forceThenConsume_narrows_of_partial {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    {adj : AdjMatrix n} {χ : Colouring n}
    (hpart :
      (∃ u ∈ branches χ, ∃ w ∈ branches χ, keyV key adj χ u ≠ keyV key adj χ w)
      ∨ (∃ u ∈ branches χ, ∃ w ∈ branches χ, u ≠ w
            ∧ Consume.WordReach (verified S adj χ) u w)) :
    (narrow (forceThenConsume key S) adj χ).length < (branches χ).length := by
  -- The narrowing is `dedup (map rep (forcedSet))`, so it is never longer than the forced set.
  have hle : (narrow (forceThenConsume key S) adj χ).length ≤ (forcedSet key adj χ).length := by
    rw [narrow_forceThenConsume]
    have h1 := (List.dedup_sublist ((forcedSet key adj χ).map (rep (verified S adj χ)))).length_le
    rw [List.length_map] at h1
    exact h1
  have hsub : ∀ x ∈ forcedSet key adj χ, x ∈ branches χ := fun x hx =>
    forcedSet_subset key adj χ hx
  have hFnodup : (forcedSet key adj χ).Nodup := Force.keepMin_nodup key adj χ
  have hFle : (forcedSet key adj χ).length ≤ (branches χ).length := by
    have h1 := List.toFinset_card_of_nodup hFnodup
    have h2 := List.toFinset_card_of_nodup (branches_nodup χ)
    have hs : (forcedSet key adj χ).toFinset ⊆ (branches χ).toFinset := fun x hx =>
      List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
    have := Finset.card_le_card hs
    omega
  rcases hpart with ⟨u, hu, w, hw, hne⟩ | ⟨u, hu, w, hw, huw, hreach⟩
  · -- FORCE fires: it discards a branch, and consume can only shorten further.
    have h := Force.forceBy_narrows_of_key_ne (key := key) hu hw hne
    rw [Force.narrow_forceBy] at h
    have h' : (forcedSet key adj χ).length < (branches χ).length := h
    omega
  · -- CONSUME fires. The key is constant on orbits, so `u` and `w` survive force together or not at all.
    have hkeyeq : keyV key adj χ u = keyV key adj χ w := by
      obtain ⟨α, hα, hαu⟩ := Consume.reach_of_mem_orbit
        (fun _ hg => Consume.isColAut_of_mem_verified hg) u n w
        (Consume.mem_orbit_of_wordReach hreach)
      rw [← hαu, Force.keyV_aut_invariant hk hα.relabel hα.transport u]
    by_cases hboth : u ∈ forcedSet key adj χ
    · -- both are in the forced set, and they get the same representative ⟹ a merge ⟹ strictly shorter
      have hwF : w ∈ forcedSet key adj χ := by
        obtain ⟨_, hmin⟩ := (Force.mem_keepMin_iff u).mp hboth
        exact (Force.mem_keepMin_iff w).mpr ⟨hw, fun z hz => by rw [← hkeyeq]; exact hmin z hz⟩
      have hlt : (narrow (forceThenConsume key S) adj χ).length < (forcedSet key adj χ).length := by
        rw [narrow_forceThenConsume]
        exact Consume.dedup_map_length_lt hFnodup hboth hwF huw
          (Consume.rep_eq_of_wordReach hreach)
      omega
    · -- force already discarded `u` ⟹ the forced set is strictly smaller than the cell
      have : (forcedSet key adj χ).length < (branches χ).length :=
        Descend.length_lt_of_missing hFnodup (branches_nodup χ) hsub hu hboth
      omega

/-- **The residue, named.** A cell the composite cannot collapse is one where the supply does not connect it *and*
the key does not separate it — neither move applies. That is the mutual stall (`②`'s real flag), and the graphs
that exhibit it are exactly `UnhandledResidue`. -/
theorem forceThenConsume_stall {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (hd : ¬ Discrete χ) (hstall : 1 < (narrow (forceThenConsume key S) adj χ).length) :
    (¬ Consume.CellIsOrbit S adj χ)
    ∧ (∃ u ∈ branches χ, ∃ w ∈ branches χ, u ≠ w ∧ keyV key adj χ u = keyV key adj χ w) := by
  constructor
  · intro horb
    rw [forceThenConsume_singleton_of_cellIsOrbit hd horb] at hstall
    omega
  · by_contra hc
    push_neg at hc
    -- no two distinct branches share a key ⟹ the key separates the cell ⟹ force collapses it
    have hsep : ∀ u ∈ branches χ, ∀ w ∈ branches χ,
        keyV key adj χ u = keyV key adj χ w → u = w := by
      intro u hu w hw hkey
      by_contra hne
      exact hc u hu w hw hne hkey
    have hone := forceThenConsume_singleton_of_separating (S := S) hd hsep
    omega

end Composite
end ChainDescent
