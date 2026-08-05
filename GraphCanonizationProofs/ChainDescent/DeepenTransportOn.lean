import ChainDescent.RestrictedTransport
import ChainDescent.DeepenComplete

/-!
# `①` ON A CLASS FOR THE **DEEPEN** OBJECT — `OrbitComplete` relativized

## What this closes

`DeepenComplete.branchOrbit_transport_of_orbitComplete` gives `①c` for the raw `deepenSupply`, but it
wants `OrbitComplete` **globally** (`∀ adj χ`) — exactly as `deepen_branchOrbit_transport` wanted global
`Tinhofer`, and for the same reason: `Descend.TransportAt` / `NarrowTransport` are `∀ adj σ χ`, so the
spine quantifies over graphs the class does not contain and colourings the descent never reaches.

`RestrictedTransport.lean` already performed this repair for the **force** spine
(`forceThenPick`), relativizing on (relabelling-closed class of graphs) × (reached colourings). Its
§1–§2.1 — `TransportOn` / `NarrowTransportOn` / `descend_transport_on` / `isoInvariantOn` /
`complete_on` / `flag_iso_invariant_on` — are **resolver-generic** and are reused verbatim here. What
that file supplied only for `forceThenPick` was the §3 contract discharge; this file supplies the
analogue for the **guarded mixed** object `Stall.guard (forceThenConsume key deepenSupply)`.

## The shape of the discharge, and where `OrbitComplete` actually enters

Three pieces, and only the third needs anything from the supply:

1. **The covering half is UNCONDITIONAL in the supply.** `Consume` verifies every candidate, so a
   discarded branch is automorphic to the kept one and the two have equal descent values
   (`RestrictedTransport.branchVal_eq_of_isColAut_on`). A broken oracle costs branches, never `①`.
2. **The forced set transports** from `KeyEquivariant` alone (`Composite.narrowFnEquivariant_forcedSet`).
3. **The FLAG must fire on both sides together** — `Stall.StallEquivariant`. *This* is the whole
   supply-side obligation, and it is what `OrbitComplete` buys: under it deepen's branch-orbit relation
   **is** the `IsColAut`-orbit relation, which conjugates, so the narrowing has the same length at
   `(adj, χ)` and at `(σ adj, σ χ)`.

⟹ the relativized contract needs `OrbitComplete` only at graphs **in the class** and colourings the
descent **reaches** — which is precisely the form `DeepenComplete` §3/§5 can supply.

## What this does and does not claim

It is `①` (sound unconditionally; iso-invariant, hence complete, **on the class**). It is **not**
totality: `OrbitComplete` says deepen recovers the orbits, not that the cell *is* one orbit, so a cell
with `k ≥ 2` orbits narrows to `k` branches and the guard flags. Never flagging is `Tinhofer`'s job
(`TwinFamily.answers_of_tinhoferGraph`), and `③` at this object is
`TwinFamily.not_tinhoferGraph_of_flag`, already proved.

▶ **To widen the covered class, supply a wider `C`**: all that is asked is `RelabelClosed C` and
*"`OrbitComplete` at every reached colouring"*. §6 instantiates it at `TwinFamily.TinhoferGraph`;
`DeepenComplete` §5's *good-or-rigid* weakening is what a wider instance should target.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned.
-/

namespace ChainDescent
namespace DeepenTransportOn

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut Supply verified)
open ChainDescent.Force (Key KeyEquivariant)
open ChainDescent.Composite (forceThenConsume forcedSet)
open ChainDescent.Stall (guard stalled)
open ChainDescent.RestrictedTransport (TransportOn NarrowTransportOn RelabelClosed)

variable {n : Nat}

/-! ## 1. The general contract route, relativized

`Descend.NarrowFnEquivariant` / `CoveringOfAt` / `narrowTransport_of_coveringOfAt` on
(class) × (reached colourings). The one addition over the global versions is `hNsub`: the intermediate
must live inside the branch cell, because the relativized `branchVal_transport_on` needs the child to
be *reached*, and `Reaches.step` is available exactly for a branch-cell vertex. Every intended
intermediate satisfies it (`Composite.forcedSet_subset`). -/

/-- `Descend.NarrowFnEquivariant`, relativized. -/
def NarrowFnEquivariantOn (C : AdjMatrix n → Prop) (rf : Refiner n) (N : NarrowFn n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n), C adj → ∀ (χ : Colouring n), Reaches rf adj χ →
    (N (relabelAdj σ adj) (transportColouring σ χ)).Perm ((N adj χ).map σ)

/-- `Descend.CoveringOfAt`, relativized. -/
def CoveringOfAtOn (C : AdjMatrix n → Prop) (rf : Refiner n) (R : Resolver n) (N : NarrowFn n) :
    Prop :=
  ∀ (fuel : Nat), TransportOn C rf R fuel →
    ∀ (adj : AdjMatrix n), C adj → ∀ (χ : Colouring n), Reaches rf adj χ →
      aggregate ((narrow R adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))
        = aggregate ((N adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

/-- **★★ THE RELATIVIZED SANDWICH** — the mirror of `Descend.narrowTransport_of_coveringOfAt`. The two
new consumptions are `RelabelClosed` (to know `σ adj` is still in the class) and
`RestrictedTransport.reaches_transport` (to know `σ χ` is still reached). -/
theorem narrowTransportOn_of_coveringOfAtOn {C : AdjMatrix n → Prop} {rf : Refiner n}
    {R : Resolver n} {N : NarrowFn n}
    (hre : RefineEquivariant rf) (hCcl : RelabelClosed C)
    (hNsub : ∀ adj : AdjMatrix n, C adj → ∀ χ : Colouring n, Reaches rf adj χ →
      ∀ v ∈ N adj χ, v ∈ branches χ)
    (hNe : NarrowFnEquivariantOn C rf N) (hcov : CoveringOfAtOn C rf R N) :
    NarrowTransportOn C rf R := by
  intro fuel ih adj hC σ χ hr hd
  have hCσ : C (relabelAdj σ adj) := hCcl σ adj hC
  have hrσ : Reaches rf (relabelAdj σ adj) (transportColouring σ χ) :=
    RestrictedTransport.reaches_transport hre σ hr
  rw [hcov fuel ih _ hCσ _ hrσ, hcov fuel ih adj hC χ hr]
  refine aggregate_perm (((hNe σ adj hC χ hr).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq (List.map_congr_left (fun v hv =>
    RestrictedTransport.branchVal_transport_on hre ih hC hr hd σ (hNsub adj hC χ hr v hv)))

/-! ## 2. The flag, relativized — `StallEquivariantOn` from branch-orbit transport

`SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport` is pointwise in
`(σ, adj, χ)`: it introduces them and then uses its `horb` at that one triple. So restricting `horb`
to the class restricts the conclusion, with the proof unchanged. -/

/-- `Stall.StallEquivariant`, relativized. -/
def StallEquivariantOn (C : AdjMatrix n → Prop) (rf : Refiner n) (R : Resolver n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n), C adj → ∀ (χ : Colouring n), Reaches rf adj χ →
    (narrow R (relabelAdj σ adj) (transportColouring σ χ)).length = (narrow R adj χ).length

/-- **★ THE FLAG IS EQUIVARIANT ON THE CLASS**, given that the branch-orbit relation transports there.
The narrowing reads the supply only through `Consume.rep` on `forcedSet ⊆ branches`, and `rep` there
depends only on the branch-orbit relation. -/
theorem stallEquivariantOn_forceThenConsume {C : AdjMatrix n → Prop} {rf : Refiner n} {key : Key n}
    (hk : KeyEquivariant key) {S : Supply n}
    (horb : ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n), C adj → ∀ (χ : Colouring n),
      Reaches rf adj χ → ∀ a b : Fin n, a ∈ branches χ → b ∈ branches χ →
      (Consume.WordReach (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
        ↔ Consume.WordReach (verified S adj χ) a b)) :
    StallEquivariantOn C rf (forceThenConsume key S) := by
  intro σ adj hC χ hr
  rw [Composite.narrow_forceThenConsume, Composite.narrow_forceThenConsume]
  have hperm : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).Perm
      ((forcedSet key adj χ).map σ) := Composite.narrowFnEquivariant_forcedSet hk σ adj χ
  have hFin : (forcedSet key (relabelAdj σ adj) (transportColouring σ χ)).toFinset
      = (forcedSet key adj χ).toFinset.image σ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [hperm.mem_iff]
    simp [List.mem_map]
  rw [SupplyTransport.dedup_map_length_eq_card_image,
      SupplyTransport.dedup_map_length_eq_card_image, hFin, Finset.image_image]
  refine SupplyTransport.card_image_congr_of_iff ?_
  intro a ha b hb
  simp only [Function.comp_apply]
  rw [Consume.rep_eq_iff_wordReach, Consume.rep_eq_iff_wordReach]
  exact horb σ adj hC χ hr a b
    (Composite.forcedSet_subset key adj χ (List.mem_toFinset.mp ha))
    (Composite.forcedSet_subset key adj χ (List.mem_toFinset.mp hb))

/-! ## 3. The guarded reference, relativized -/

/-- `Residue.narrowFnEquivariant_guardedRef` on the class — the reference is the forced set, emptied
when the node stalls, so it transports as soon as the *stall predicate* does. -/
theorem narrowFnEquivariantOn_guardedRef {C : AdjMatrix n → Prop} {rf : Refiner n} {key : Key n}
    (hk : KeyEquivariant key) {S : Supply n}
    (hse : StallEquivariantOn C rf (forceThenConsume key S)) :
    NarrowFnEquivariantOn C rf (Residue.guardedRef key S) := by
  intro σ adj hC χ hr
  unfold Residue.guardedRef stalled
  have hlen := hse σ adj hC χ hr
  by_cases h : 1 < (narrow (forceThenConsume key S) adj χ).length
  · rw [if_pos (by rw [hlen]; exact h), if_pos h]; simp
  · rw [if_neg (by rw [hlen]; exact h), if_neg h]
    exact Composite.narrowFnEquivariant_forcedSet hk σ adj χ

/-- The guarded reference lives in the branch cell — `hNsub` for §1. -/
theorem guardedRef_subset {key : Key n} {S : Supply n} (adj : AdjMatrix n) (χ : Colouring n)
    {v : Fin n} (hv : v ∈ Residue.guardedRef key S adj χ) : v ∈ branches χ := by
  unfold Residue.guardedRef at hv
  split at hv
  · exact absurd hv (by simp)
  · exact Composite.forcedSet_subset key adj χ hv

/-! ## 4. The covering, relativized — **unconditional in the supply**

`Residue.coveringOfAt_guarded`, with `Consume.branchVal_eq_of_isColAut` replaced by
`RestrictedTransport.branchVal_eq_of_isColAut_on`. The only care needed is that the relativized form
wants its vertex in the branch cell, so the value lemma is stated for forced-set members rather than
for every `b : Fin n`; both call sites are at forced-set members. -/

theorem coveringOfAtOn_guarded {C : AdjMatrix n → Prop} {rf : Refiner n}
    (hre : RefineEquivariant rf) {key : Key n} (hk : KeyEquivariant key) (S : Supply n) :
    CoveringOfAtOn C rf (guard (forceThenConsume key S)) (Residue.guardedRef key S) := by
  intro fuel ih adj hC χ hr
  set K := forceThenConsume key S with hK
  set R := guard K with hR
  set f : Fin n → Option (CanonSpec.Labelled n) :=
    fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 with hf
  rw [Stall.narrow_guard]
  unfold Residue.guardedRef
  by_cases hst : stalled K adj χ
  · rw [if_pos hst, if_pos hst]
  · rw [if_neg hst, if_neg hst]
    have hval : ∀ b ∈ forcedSet key adj χ,
        f (Consume.rep (verified S adj χ) b) = f b := by
      intro b hb
      have hbB : b ∈ branches χ := Composite.forcedSet_subset key adj χ hb
      obtain ⟨u, hune, huc⟩ := exists_partner_of_mem_branches hbB
      have hnd : ¬ Discrete χ := fun hdisc => hune (hdisc u b huc)
      obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (adj := adj) (χ := χ)
        (fun _ hg => Consume.isColAut_of_mem_verified hg) b
      rw [hf]; simp only; rw [← hαb]
      exact RestrictedTransport.branchVal_eq_of_isColAut_on hre ih hC hr hnd hα hbB
    refine aggregate_congr_mem ?_
    intro x
    rw [Composite.narrow_forceThenConsume]
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
      exact List.mem_map.mpr ⟨v, hbv ▸ Composite.rep_mem_forcedSet hk S adj χ hb, hvx⟩
    · intro hx
      obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
      refine List.mem_map.mpr ⟨Consume.rep (verified S adj χ) b, ?_, ?_⟩
      · exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
      · rw [hval b hb]; exact hbx

/-- **★★ THE CONTRACT ON THE CLASS, for the guarded mixed resolver.** -/
theorem narrowTransportOn_guarded {C : AdjMatrix n → Prop} {rf : Refiner n}
    (hre : RefineEquivariant rf) (hCcl : RelabelClosed C) {key : Key n} (hk : KeyEquivariant key)
    {S : Supply n} (hse : StallEquivariantOn C rf (forceThenConsume key S)) :
    NarrowTransportOn C rf (guard (forceThenConsume key S)) :=
  narrowTransportOn_of_coveringOfAtOn hre hCcl
    (fun _ _ _ _ _ hv => guardedRef_subset _ _ hv)
    (narrowFnEquivariantOn_guardedRef hk hse) (coveringOfAtOn_guarded hre hk S)

/-! ## 5. ★★★ `①` ON A CLASS FROM `OrbitComplete` -/

/-- deepen's branch-orbit relation transports **on the class** — the relativized
`DeepenComplete.branchOrbit_transport_of_orbitComplete`. Both sides equal the `IsColAut`-orbit
relation, which conjugates; `OrbitComplete` is consumed at `(adj, χ)` and at `(σ adj, σ χ)`, the
latter available because the class is relabelling-closed and `Reaches` transports. -/
theorem branchOrbit_transport_on {C : AdjMatrix n → Prop} {rf : Refiner n}
    (hre : RefineEquivariant rf) (hCcl : RelabelClosed C)
    (hOC : ∀ adj : AdjMatrix n, C adj → ∀ χ : Colouring n, Reaches rf adj χ →
      Deepen.OrbitComplete adj χ)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (hC : C adj) (χ : Colouring n)
    (hr : Reaches rf adj χ) (a b : Fin n) (ha : a ∈ branches χ) (_hb : b ∈ branches χ) :
    Consume.WordReach
        (verified Deepen.deepenSupply (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
      ↔ Consume.WordReach (verified Deepen.deepenSupply adj χ) a b := by
  have hσa : σ a ∈ branches (transportColouring σ χ) :=
    (branches_transport_perm σ χ).mem_iff.mpr (List.mem_map_of_mem ha)
  have hOCσ : Deepen.OrbitComplete (relabelAdj σ adj) (transportColouring σ χ) :=
    hOC _ (hCcl σ adj hC) _ (RestrictedTransport.reaches_transport hre σ hr)
  rw [Deepen.branch_orbit_iff_aut_of_orbitComplete hOCσ hσa,
      Deepen.branch_orbit_iff_aut_of_orbitComplete (hOC adj hC χ hr) ha]
  constructor
  · rintro ⟨β, hβ, hβa⟩
    refine ⟨σ⁻¹ * β * σ, ?_, ?_⟩
    · have hc := (Consume.isColAut_conj_iff σ (adj := adj) (χ := χ) (α := σ⁻¹ * β * σ)).mp
      rw [show σ * (σ⁻¹ * β * σ) * σ⁻¹ = β by group] at hc
      exact hc hβ
    · simp [Equiv.Perm.mul_apply, hβa]
  · rintro ⟨β, hβ, hβa⟩
    refine ⟨σ * β * σ⁻¹, (Consume.isColAut_conj_iff σ).mpr hβ, ?_⟩
    simp [Equiv.Perm.mul_apply, hβa]

/-- **★★★ THE CONTRACT AT `deepenSupply`, ON A CLASS WHERE `OrbitComplete` HOLDS.** -/
theorem narrowTransportOn_deepen {C : AdjMatrix n → Prop} {rf : Refiner n} {key : Key n}
    (hre : RefineEquivariant rf) (hk : KeyEquivariant key) (hCcl : RelabelClosed C)
    (hOC : ∀ adj : AdjMatrix n, C adj → ∀ χ : Colouring n, Reaches rf adj χ →
      Deepen.OrbitComplete adj χ) :
    NarrowTransportOn C rf (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) :=
  narrowTransportOn_guarded hre hCcl hk
    (stallEquivariantOn_forceThenConsume hk
      (fun σ adj hC χ hr a b ha hb => branchOrbit_transport_on hre hCcl hOC σ adj hC χ hr a b ha hb))

/-- **★★★ `①` ON THE CLASS FOR THE DEEPEN OBJECT.**

1. **sound** — unconditional, every graph;
2. **complete on the class** — equal outputs ⟺ isomorphic, whenever the left input is in `C`;
3. **the flag is iso-invariant on the class**.

⚠ Not totality: `OrbitComplete` recovers the orbits, it does not make the cell *one* orbit. A cell with
`k ≥ 2` orbits narrows to `k` branches and the guard flags — which is exactly what `③`
(`TwinFamily.not_tinhoferGraph_of_flag`) reads. -/
theorem canonizes_on_orbitComplete {C : AdjMatrix n → Prop} {key : Key n}
    (hk : KeyEquivariant key) (hCcl : RelabelClosed C)
    (hOC : ∀ adj : AdjMatrix n, C adj → ∀ χ : Colouring n,
      Reaches (Refine.encodeFreeFast (n := n)) adj χ → Deepen.OrbitComplete adj χ) :
    CanonSpec.SoundOpt
        (canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))))
    ∧ (∀ (G H : AdjMatrix n) (cG cH : CanonSpec.Labelled n), C G →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) G = some cG →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) H = some cH →
        (CanonSpec.GraphIso G H ↔ cG = cH))
    ∧ (∀ (G H : AdjMatrix n), C G → CanonSpec.GraphIso G H →
        (canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) G = none
         ↔ canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) H = none)) := by
  have hnt := narrowTransportOn_deepen Refine.refineEquivariant_encodeFreeFast hk hCcl hOC
  exact ⟨soundOpt_canonForm? _ _,
    fun G H cG cH hG h1 h2 =>
      RestrictedTransport.complete_on Refine.refineEquivariant_encodeFreeFast hnt hG cG cH h1 h2,
    fun G H hG hiso =>
      RestrictedTransport.flag_iso_invariant_on Refine.refineEquivariant_encodeFreeFast hnt hG hiso⟩

/-! ## 6. The instance — Tinhofer graphs

`TwinFamily.TinhoferGraph` is relabelling-closed (`RestrictedTransport.relabelClosed_tinhoferGraph`)
and every colouring the descent reaches is individualization-reachable
(`RestrictedTransport.indivReach_of_reaches`), hence `Deepen.Tinhofer`
(`TwinFamily.tinhofer_of_stepClosed`), hence `OrbitComplete`
(`DeepenComplete.orbitComplete_of_tinhofer`). -/

theorem orbitComplete_of_tinhoferGraph {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj)
    {χ : Colouring n} (hr : Reaches (Refine.encodeFreeFast (n := n)) adj χ) :
    Deepen.OrbitComplete adj χ :=
  Deepen.orbitComplete_of_tinhofer
    (TwinFamily.tinhofer_of_stepClosed (TwinFamily.stepClosed_indivReach adj) h
      (RestrictedTransport.indivReach_of_reaches hr))

/-- **★★★ `①` ON THE TINHOFER CLASS, AT THE DEEPEN OBJECT.** The companion to
`RestrictedTransport.canonizes_on_tinhofer`: same class, but at the object that carries the honest
flag and `③` (`TwinFamily.not_tinhoferGraph_of_flag`) rather than at the never-flagging
`forceThenPick`. -/
theorem canonizes_on_tinhofer_deepen {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.SoundOpt
        (canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))))
    ∧ (∀ (G H : AdjMatrix n) (cG cH : CanonSpec.Labelled n), TwinFamily.TinhoferGraph G →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) G = some cG →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) H = some cH →
        (CanonSpec.GraphIso G H ↔ cG = cH))
    ∧ (∀ (G H : AdjMatrix n), TwinFamily.TinhoferGraph G → CanonSpec.GraphIso G H →
        (canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) G = none
         ↔ canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume key (Deepen.deepenSupply (n := n)))) H = none)) :=
  canonizes_on_orbitComplete hk RestrictedTransport.relabelClosed_tinhoferGraph
    (fun _ hC _ hr => orbitComplete_of_tinhoferGraph hC hr)

/-! ## 7. ★★★ THE PACKAGE — `①` ∧ `②` ∧ `③` at ONE EXECUTABLE OBJECT

This is the wind-down's option **(v)** assembled. The object is
`Stall.guard (forceThenConsume holKeyFast deepenSupply)` — executable, no `orbKey`, no
`deepenSupplyGuarded`, nothing `noncomputable`:

| | what | where it comes from |
|---|---|---|
| `①a` | sound, **unconditional** | `Descend.soundOpt_canonForm?` |
| `①b` | complete **on the Tinhofer class** | §6 (this file) |
| `①c` | the flag is iso-invariant **on the class** | §6 (this file) |
| `②` | explicit polynomial, **unconditional, every input** | `SupplyCost.descentCost_guard_mixed_le` — the guard makes the descent a single path by construction, so no hypothesis is needed |
| `③` | flag ⟹ the input is **not Tinhofer** | `TwinFamily.not_tinhoferGraph_of_flag` |
| — | and it **never flags** on a Tinhofer graph | `TwinFamily.answers_of_tinhoferGraph` |

⚠⚠ **The honest reading of `①b`/`①c`.** They are proved *on the class*, not globally: completeness is
claimed for pairs whose **left** input is Tinhofer. Off the class the object is still sound (its output
is a genuine relabelling) but two non-isomorphic non-Tinhofer graphs are not proved to receive different
forms. That is the price of this object relative to `Publication.canonForm?`'s record object, whose
`①` is unconditional but which has no `③` — the trade the wind-down's option table records. -/

theorem descentCost_deepen_le (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (guard (forceThenConsume (Hol.holKeyFast (n := n)) (Deepen.deepenSupply (n := n)))) adj
      ≤ SupplyCost.pathBound n (n * (n * n * n * n * n) + n * n
          + SupplyCost.consumeNodeBound n (n * n * n * n * n * n) (n * n)) :=
  SupplyCost.descentCost_guard_mixed_le
    (fun χ v => RecordCost.keyCost_holKeyFast_le adj χ v)
    (TwinFamily.supplyCost_deepenSupply_le adj)
    (TwinFamily.gens_deepenSupply_length_le adj)

/-- **★★★ THE WHOLE PACKAGE AT ONE EXECUTABLE OBJECT.** See the table above for what each conjunct is
and what is *not* claimed. -/
theorem deepen_object_package :
    CanonSpec.SoundOpt
        (canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume (Hol.holKeyFast (n := n)) (Deepen.deepenSupply (n := n)))))
    ∧ (∀ (G H : AdjMatrix n) (cG cH : CanonSpec.Labelled n), TwinFamily.TinhoferGraph G →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume (Hol.holKeyFast (n := n))
            (Deepen.deepenSupply (n := n)))) G = some cG →
        canonForm? (Refine.encodeFreeFast (n := n))
          (guard (forceThenConsume (Hol.holKeyFast (n := n))
            (Deepen.deepenSupply (n := n)))) H = some cH →
        (CanonSpec.GraphIso G H ↔ cG = cH))
    ∧ (∀ adj : AdjMatrix n,
        descentCost (Refine.encodeFreeFast (n := n))
            (guard (forceThenConsume (Hol.holKeyFast (n := n)) (Deepen.deepenSupply (n := n)))) adj
          ≤ SupplyCost.pathBound n (n * (n * n * n * n * n) + n * n
              + SupplyCost.consumeNodeBound n (n * n * n * n * n * n) (n * n)))
    ∧ (∀ adj : AdjMatrix n,
        canonForm? (Refine.encodeFreeFast (n := n))
            (guard (forceThenConsume (Hol.holKeyFast (n := n))
              (Deepen.deepenSupply (n := n)))) adj = none →
          ¬ TwinFamily.TinhoferGraph adj) :=
  ⟨(canonizes_on_tinhofer_deepen Hol.keyEquivariant_holKeyFast).1,
   (canonizes_on_tinhofer_deepen Hol.keyEquivariant_holKeyFast).2.1,
   descentCost_deepen_le,
   fun _ hflag => TwinFamily.not_tinhoferGraph_of_flag hflag⟩

end DeepenTransportOn
end ChainDescent
