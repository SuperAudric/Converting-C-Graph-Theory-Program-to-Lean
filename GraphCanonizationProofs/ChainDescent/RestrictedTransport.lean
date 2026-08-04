import ChainDescent.TwinFamily
import ChainDescent.ForcePick

/-!
# `①` ON A CLASS — the transport spine, relativized, and **Tinhofer graphs are CANONIZED**

## The gap this closes

`TwinFamily` §10 proves a Tinhofer graph is `Residue.Handled`, hence **answered** within an explicit
polynomial budget, at an executable object. What it could not reach is `①`: `CanonSpec.IsoInvariantOpt`
is a property of the canonizer *as a function on every graph*, and so is the spine that establishes it —
[`Descend.TransportAt`](Descend.lean) is `∀ adj σ χ` and `Descend.NarrowTransport` likewise.

The Tinhofer facts are not of that shape. They hold on

* **(graphs)** the Tinhofer ones — not all `adj`; and
* **(colourings)** the *individualization-reachable* ones — not all `χ`. At an arbitrary `χ` a cell need
  not be an `Aut`-orbit even in a Tinhofer graph, so this axis is genuinely needed and is the one easy
  to overlook.

So the missing piece was never a theorem about `deepenSupply`'s orbits — that is
`Deepen.deepen_branch_orbit_iff_aut`, landed 2026-07-23, whose right-hand side *is* the true
automorphism-orbit relation and hence manifestly relabelling-invariant. The missing piece is the
**plumbing**: a transport spine quantified over a relabelling-closed class of graphs and the reached
colourings. This file supplies it, additively — nothing in `Descend.lean` changes, and every existing
theorem is untouched.

## The discharge needs no supply at all

`KeyComplete.KeySeparatesAt key adj χ` demands that branch pairs **no automorphism links** get
different keys. At a `SchurianAt` node every branch pair *is* linked, so the antecedent is false and the
predicate holds **vacuously, for every key** (`keySeparatesAt_of_schurianAt`, six lines). Hence
`ForcePick.forceThenPick key` — force, keep one, no supply, no verification, **no stall channel** — is
sound there: what it discards are genuine automorphic duplicates. That is the formal content of *"the
descent never took a wrong step, because there were none to take."*

⚠⚠ **This is NOT the route `ForcePick`'s header bans.** That warning —
*"do not instantiate `forceThenPick` at `orbKey`/`orbKeyG` and read the result as a canonizer"* — is
about `KeySeparatesAt` being satisfied for the **wrong reason**: a guarded key returning a constant off
its guard vacuously satisfies it *while genuine separation is still required*, and the singleton pick
then discards genuinely different branches. Here the vacuity is for the **right** reason: the cell has
no non-automorphic pairs at all, so there is nothing to separate and nothing unsound to discard. Same
syntactic shape, opposite semantics — recorded so this is not filed as the dead route.

## What lands

`canonizes_on_tinhofer`: on Tinhofer graphs the object is **sound** (unconditional), **iso-invariant**,
hence **complete**, it **never flags**, and it runs a single path within an explicit polynomial budget.
`deepenSupply` does not appear, so its declared flat `n⁶` charge is gone too — the whole `②` is the
key's.

⚠ The class hypothesis is still the non-computable `TwinFamily.TinhoferGraph`, and that remains correct:
it is a *classifier*, not part of the algorithm (`TwinFamily` §9). The object itself is executable for
any computable equivariant key — `Hol.holKeyFast`, say.

▶ **To widen the covered class, supply a wider `C`.** The only things asked of it are
`RelabelClosed C` and *"every reached non-discrete colouring is Schurian"*. A future resolver that
removes some rigid obstruction enlarges the second clause with nothing here re-proved.
-/

namespace ChainDescent
namespace RestrictedTransport

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut)
open ChainDescent.Force (Key KeyEquivariant)

variable {n : Nat}

/-! ## 1. `Reaches` transports along a relabelling

The reached set of the relabelled graph is the transported reached set. Needed because the covering
argument below is applied at **both** `adj` and `relabelAdj σ adj`. -/

theorem reaches_transport {rf : Refiner n} (hre : RefineEquivariant rf)
    (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n} (h : Reaches rf adj χ) :
    Reaches rf (relabelAdj σ adj) (transportColouring σ χ) := by
  induction h with
  | root =>
      have h0 : refineV rf (relabelAdj σ adj) (fun _ => 0)
          = transportColouring σ (refineV rf adj (fun _ => 0)) := by
        simpa [transportColouring] using hre σ adj (fun _ => 0)
      rw [← h0]
      exact Reaches.root
  | @step χ v _ hd hp ih =>
      have hd' : ¬ Discrete (transportColouring σ χ) :=
        fun hc => hd ((discrete_transport σ χ).mp hc)
      obtain ⟨u, hune, huc⟩ := hp
      have hp' : ∃ u', u' ≠ σ v ∧ transportColouring σ χ u' = transportColouring σ χ (σ v) := by
        refine ⟨σ u, fun hc => hune (σ.injective hc), ?_⟩
        show χ (σ.symm (σ u)) = χ (σ.symm (σ v))
        simpa using huc
      have hstep := Reaches.step (rf := rf) (adj := relabelAdj σ adj) (v := σ v) ih hd' hp'
      rwa [indivOne_transport σ χ v, hre σ adj (indivOne χ v)] at hstep

/-! ## 2. The relativized spine -/

/-- A class of graphs closed under relabelling — the minimum for "iso-invariant **on** the class" to be
a meaningful statement. -/
def RelabelClosed (C : AdjMatrix n → Prop) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n), C adj → C (relabelAdj σ adj)

/-- `Descend.TransportAt`, relativized on **both** axes: graphs in `C`, colourings the descent reaches. -/
def TransportOn (C : AdjMatrix n → Prop) (rf : Refiner n) (R : Resolver n) (fuel : Nat) : Prop :=
  ∀ (adj : AdjMatrix n), C adj → ∀ (σ : Equiv.Perm (Fin n)) (χ : Colouring n), Reaches rf adj χ →
    (descend rf R (relabelAdj σ adj) fuel (transportColouring σ χ)).1
      = (descend rf R adj fuel χ).1

/-- `Descend.NarrowTransport`, relativized the same way. -/
def NarrowTransportOn (C : AdjMatrix n → Prop) (rf : Refiner n) (R : Resolver n) : Prop :=
  ∀ (fuel : Nat), TransportOn C rf R fuel →
    ∀ (adj : AdjMatrix n), C adj → ∀ (σ : Equiv.Perm (Fin n)) (χ : Colouring n),
      Reaches rf adj χ → ¬ Discrete χ →
        aggregate ((narrow R (relabelAdj σ adj) (transportColouring σ χ)).map
            (fun v => (descend rf R (relabelAdj σ adj) fuel
                (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) v))).1))
          = aggregate ((narrow R adj χ).map
            (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

/-- **★★ THE RELATIVIZED TRANSPORT INDUCTION** — the exact mirror of `Descend.descend_transport`; the
recursion never leaves `adj`, so the graph axis threads through untouched and only the reached-colouring
side condition is new. -/
theorem descend_transport_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hnt : NarrowTransportOn C rf R) : ∀ fuel, TransportOn C rf R fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro adj _ σ χ _
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R _ ((discrete_transport σ χ).mpr hd) 0,
            descend_val_leaf rf R adj hd 0, leafMatrix_transport σ adj χ hd]
      · rw [descend_val_zero rf R _ (fun hc => hd ((discrete_transport σ χ).mp hc)),
            descend_val_zero rf R adj hd]
  | succ fuel ih =>
      intro adj hC σ χ hr
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R _ ((discrete_transport σ χ).mpr hd) (fuel + 1),
            descend_val_leaf rf R adj hd (fuel + 1), leafMatrix_transport σ adj χ hd]
      · rw [descend_val_succ rf R _ (fun hc => hd ((discrete_transport σ χ).mp hc)) fuel,
            descend_val_succ rf R adj hd fuel]
        exact hnt fuel ih adj hC σ χ hr hd

/-- **★★ ISO-INVARIANCE ON THE CLASS** — the relativized `Descend.isoInvariantOpt_canonForm?`. Note the
root colouring is `Reaches.root`, so no side condition escapes to the caller. -/
theorem isoInvariantOn {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransportOn C rf R)
    (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} (hC : C adj) :
    canonForm? rf R (relabelAdj σ adj) = canonForm? rf R adj := by
  show (descend rf R (relabelAdj σ adj) n (refineV rf (relabelAdj σ adj) (fun _ => 0))).1
      = (descend rf R adj n (refineV rf adj (fun _ => 0))).1
  have h0 : refineV rf (relabelAdj σ adj) (fun _ => 0)
      = transportColouring σ (refineV rf adj (fun _ => 0)) := by
    simpa [transportColouring] using hre σ adj (fun _ => 0)
  rw [h0]
  exact descend_transport_on hnt n adj hC σ _ Reaches.root

/-! ### 2.1 The payoffs, on the class -/

/-- Isomorphic inputs receive the same answer — `CanonSpec.eq_of_graphIso` on the class. Only the
**left** input needs to be in `C`: the right one is a relabelling of it. -/
theorem eq_of_graphIso_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransportOn C rf R)
    {G H : AdjMatrix n} (hG : C G) (h : CanonSpec.GraphIso G H) :
    canonForm? rf R G = canonForm? rf R H := by
  obtain ⟨π, hπ⟩ := h
  have hHrel : relabelAdj π G = H := CanonSpec.relabelAdj_eq_of_labelledAdj hπ
  rw [← hHrel, isoInvariantOn hre hnt π hG]

/-- **★★★ COMPLETENESS ON THE CLASS (`①b`).** Soundness is unconditional, so only the `→` direction
consumes the restricted invariance. -/
theorem complete_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransportOn C rf R)
    {G H : AdjMatrix n} (hG : C G) (cG cH : CanonSpec.Labelled n)
    (h1 : canonForm? rf R G = some cG) (h2 : canonForm? rf R H = some cH) :
    CanonSpec.GraphIso G H ↔ cG = cH := by
  constructor
  · intro hiso
    have hEq := eq_of_graphIso_on hre hnt hG hiso
    rw [h1, h2] at hEq
    exact Option.some.inj hEq
  · intro hEq
    obtain ⟨πG, hπG⟩ := soundOpt_canonForm? rf R G cG h1
    obtain ⟨πH, hπH⟩ := soundOpt_canonForm? rf R H cH h2
    exact CanonSpec.iso_of_labelledAdj_eq (hπG.symm.trans (hEq.trans hπH))

/-- **`①c` on the class** — flagging is a property of the isomorphism class. -/
theorem flag_iso_invariant_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransportOn C rf R)
    {G H : AdjMatrix n} (hG : C G) (h : CanonSpec.GraphIso G H) :
    canonForm? rf R G = none ↔ canonForm? rf R H = none := by
  rw [eq_of_graphIso_on hre hnt hG h]

/-! ## 3. Discharging the contract for `forceThenPick`

Two relativized bricks, then the sandwich. Everything mirrors `Descend`/`ForcePick`; the only change is
that the induction hypothesis is now available at `(C adj, Reaches χ)` rather than everywhere. -/

/-- `Descend.branchVal_transport` with the relativized IH. The reached-child side condition is exactly
`Reaches.step`, discharged from `v` sitting in the branch cell. -/
theorem branchVal_transport_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) {fuel : Nat} (ih : TransportOn C rf R fuel)
    {adj : AdjMatrix n} (hC : C adj) {χ : Colouring n} (hr : Reaches rf adj χ) (hd : ¬ Discrete χ)
    (σ : Equiv.Perm (Fin n)) {v : Fin n} (hv : v ∈ branches χ) :
    (descend rf R (relabelAdj σ adj) fuel
        (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) (σ v)))).1
      = (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 := by
  rw [indivOne_transport σ χ v, hre σ adj (indivOne χ v)]
  exact ih adj hC σ (refineV rf adj (indivOne χ v))
    (hr.step hd (exists_partner_of_mem_branches hv))

/-- `Consume.branchVal_eq_of_isColAut` with the relativized IH: an automorphism makes two branches
value-equal. -/
theorem branchVal_eq_of_isColAut_on {C : AdjMatrix n → Prop} {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) {fuel : Nat} (ih : TransportOn C rf R fuel)
    {adj : AdjMatrix n} (hC : C adj) {χ : Colouring n} (hr : Reaches rf adj χ) (hd : ¬ Discrete χ)
    {α : Equiv.Perm (Fin n)} (hα : IsColAut adj χ α) {v : Fin n} (hv : v ∈ branches χ) :
    (descend rf R adj fuel (refineV rf adj (indivOne χ (α v)))).1
      = (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 := by
  have h := branchVal_transport_on hre ih hC hr hd α hv
  rw [hα.relabel, hα.transport] at h
  exact h

/-- `ForcePick.coveringOfAt_forceThenPick`, relativized — the singleton pick covers the forced set,
because under `KeySeparatesAt` every survivor is automorphic to the one kept. -/
theorem coveringOfAt_forceThenPick_on {C : AdjMatrix n → Prop} {rf : Refiner n} {key : Key n}
    (hre : RefineEquivariant rf) {fuel : Nat}
    (ih : TransportOn C rf (ForcePick.forceThenPick key) fuel)
    {adj : AdjMatrix n} (hC : C adj) {χ : Colouring n} (hr : Reaches rf adj χ)
    (hK : KeyComplete.KeySeparatesAt key adj χ) :
    aggregate ((narrow (ForcePick.forceThenPick key) adj χ).map
        (fun v => (descend rf (ForcePick.forceThenPick key) adj fuel
          (refineV rf adj (indivOne χ v))).1))
      = aggregate ((Composite.forcedSet key adj χ).map
        (fun v => (descend rf (ForcePick.forceThenPick key) adj fuel
          (refineV rf adj (indivOne χ v))).1)) := by
  rw [ForcePick.narrow_forceThenPick]
  cases hL : Composite.forcedSet key adj χ with
  | nil => simp
  | cons p rest =>
      have hpF : p ∈ Composite.forcedSet key adj χ := by rw [hL]; exact List.mem_cons_self ..
      have hpB : p ∈ branches χ := Composite.forcedSet_subset key adj χ hpF
      obtain ⟨u, hune, huc⟩ := exists_partner_of_mem_branches hpB
      have hnd : ¬ Discrete χ := fun hdisc => hune (hdisc u p huc)
      have hval : ∀ b ∈ Composite.forcedSet key adj χ,
          (descend rf (ForcePick.forceThenPick key) adj fuel
              (refineV rf adj (indivOne χ b))).1
            = (descend rf (ForcePick.forceThenPick key) adj fuel
              (refineV rf adj (indivOne χ p))).1 := by
        intro b hbF
        obtain ⟨σ, hσ, hσp⟩ := KeyComplete.forcedSet_single_orbit_of_keySeparatesAt hK hpF hbF
        have h := branchVal_eq_of_isColAut_on hre ih hC hr hnd hσ hpB
        rw [hσp] at h
        exact h
      have htake : (p :: rest).take 1 = [p] := rfl
      refine aggregate_congr_mem (fun x => ⟨?_, ?_⟩)
      · intro hx
        obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
        exact List.mem_map.mpr ⟨b, List.mem_of_mem_take hb, hbx⟩
      · intro hx
        obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
        refine List.mem_map.mpr ⟨p, by rw [htake]; exact List.mem_cons_self .., ?_⟩
        rw [← hbx]
        exact (hval b (by rw [hL]; exact hb)).symm

/-- **★★★ THE CONTRACT ON THE CLASS.** `KeyEquivariant` makes the forced set an equivariant
intermediate; the relativized separation makes the singleton pick cover it — at `adj` *and* at
`relabelAdj σ adj`, which is where `RelabelClosed` and `reaches_transport` are consumed. -/
theorem narrowTransportOn_forceThenPick {C : AdjMatrix n → Prop} {rf : Refiner n} {key : Key n}
    (hre : RefineEquivariant rf) (hk : KeyEquivariant key) (hCcl : RelabelClosed C)
    (hsep : ∀ adj : AdjMatrix n, C adj → ∀ χ : Colouring n, Reaches rf adj χ → ¬ Discrete χ →
      KeyComplete.KeySeparatesAt key adj χ) :
    NarrowTransportOn C rf (ForcePick.forceThenPick key) := by
  intro fuel ih adj hC σ χ hr hd
  have hCσ : C (relabelAdj σ adj) := hCcl σ adj hC
  have hrσ : Reaches rf (relabelAdj σ adj) (transportColouring σ χ) := reaches_transport hre σ hr
  have hdσ : ¬ Discrete (transportColouring σ χ) :=
    fun hc => hd ((discrete_transport σ χ).mp hc)
  rw [coveringOfAt_forceThenPick_on hre ih hCσ hrσ (hsep _ hCσ _ hrσ hdσ),
      coveringOfAt_forceThenPick_on hre ih hC hr (hsep adj hC χ hr hd)]
  refine aggregate_perm (((Composite.narrowFnEquivariant_forcedSet hk σ adj χ).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq (List.map_congr_left (fun v hv =>
    branchVal_transport_on hre ih hC hr hd σ (Composite.forcedSet_subset key adj χ hv)))

/-! ## 4. ★ THE "NO WRONG STEP TO TAKE" LEMMA

The whole discharge, in six lines: at a Schurian node the separation hypothesis is **vacuous**, because
there is no non-automorphic branch pair for the key to have to separate. See the module doc-block for
why this is *not* the vacuity `ForcePick`'s header warns against. -/

theorem keySeparatesAt_of_schurianAt {adj : AdjMatrix n} {χ : Colouring n}
    (hS : TwinFamily.SchurianAt adj χ) (key : Key n) :
    KeyComplete.KeySeparatesAt key adj χ := by
  intro u hu w hw hno
  exfalso
  obtain ⟨c, hc, huc⟩ := Consume.exists_targetColour_of_mem hu
  have hwc : χ w = c := (Descend.mem_branches_iff hc w).mp hw
  obtain ⟨σ, hσ, hσu⟩ := hS c u w huc hwc
  exact hno σ hσ hσu

/-! ## 5. `TinhoferGraph` is a relabelling-closed class

`IndivReach` transports (root by refiner equivariance, step by `Deepen.step_transport`) and
`SchurianAt` transports by `DeepenCertified.cellSingleOrbit_transport_iso` — the *cross-graph*
conjugation, already in the library. -/

theorem indivReach_transport {adj : AdjMatrix n} (σ : Equiv.Perm (Fin n)) {χ : Colouring n}
    (h : TwinFamily.IndivReach adj χ) :
    TwinFamily.IndivReach (relabelAdj σ adj) (transportColouring σ χ) := by
  induction h with
  | root =>
      have h0 : TwinFamily.rootCol (relabelAdj σ adj)
          = transportColouring σ (TwinFamily.rootCol adj) := by
        show Descend.refineV (Refine.encodeFreeFast (n := n)) (relabelAdj σ adj) (fun _ => 0) = _
        simpa [transportColouring] using
          Refine.refineEquivariant_encodeFreeFast (n := n) σ adj (fun _ => 0)
      rw [← h0]
      exact TwinFamily.IndivReach.root
  | @step χ _ v ih =>
      have hstep := TwinFamily.IndivReach.step ih (σ v)
      rwa [Deepen.step_transport σ adj χ v] at hstep

theorem schurianAt_transport {adj : AdjMatrix n} {χ : Colouring n} (σ : Equiv.Perm (Fin n))
    (h : TwinFamily.SchurianAt adj χ) :
    TwinFamily.SchurianAt (relabelAdj σ adj) (transportColouring σ χ) :=
  fun cid => Deepen.cellSingleOrbit_transport_iso σ (h cid)

theorem relabelClosed_tinhoferGraph :
    RelabelClosed (TwinFamily.TinhoferGraph (n := n)) := by
  intro σ adj h ψ hψ
  -- pull `ψ` back along `σ⁻¹`, apply the hypothesis there, push the result forward
  have hback : TwinFamily.IndivReach adj (transportColouring σ⁻¹ ψ) := by
    have hb := indivReach_transport σ⁻¹ hψ
    rwa [← Deepen.relabelAdj_mul, inv_mul_cancel, Deepen.relabelAdj_one] at hb
  have hfwd := schurianAt_transport σ (h _ hback)
  rwa [Deepen.transportColouring_comp, mul_inv_cancel, Deepen.transportColouring_one] at hfwd

/-- Every colouring the descent reaches is individualization-reachable — the bridge from `Reaches`
(what the spine quantifies over) to `IndivReach` (what `TinhoferGraph` speaks about). -/
theorem indivReach_of_reaches {adj : AdjMatrix n} {χ : Colouring n}
    (hr : Reaches (Refine.encodeFreeFast (n := n)) adj χ) : TwinFamily.IndivReach adj χ :=
  TwinFamily.mem_of_reaches (TwinFamily.stepClosed_indivReach adj) TwinFamily.IndivReach.root hr

/-! ## 6. ★★★ THE CAPSTONE — Tinhofer graphs are CANONIZED -/

/-- The contract, at `TinhoferGraph`, for **any** equivariant key. -/
theorem narrowTransportOn_tinhofer {key : Key n} (hk : KeyEquivariant key) :
    NarrowTransportOn (TwinFamily.TinhoferGraph (n := n))
      (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) :=
  narrowTransportOn_forceThenPick Refine.refineEquivariant_encodeFreeFast hk
    relabelClosed_tinhoferGraph
    (fun _ hC _ hr _ => keySeparatesAt_of_schurianAt (hC _ (indivReach_of_reaches hr)) key)

/-- **★★★ `①` ON THE TINHOFER CLASS** — iso-invariance, hence (with unconditional soundness) a complete
isomorphism invariant, for any computable equivariant key. -/
theorem isoInvariant_on_tinhofer {key : Key n} (hk : KeyEquivariant key)
    (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj) :
    canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) (relabelAdj σ adj)
      = canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) adj :=
  isoInvariantOn Refine.refineEquivariant_encodeFreeFast (narrowTransportOn_tinhofer hk) σ h

/-- **★★★ THE HEADLINE — A TINHOFER GRAPH IS CANONIZED.**

1. **sound** — unconditional, every graph;
2. **complete on the class** — equal outputs ⟺ isomorphic, whenever the left input is Tinhofer;
3. **never flags** — `forceThenPick` has no stall channel at all, so this carries **no** hypothesis.

This is the upgrade of `TwinFamily.answers_of_tinhoferGraph` from *answers* to *canonizes*, and it uses
**no supply**: `deepenSupply` and its declared flat `n⁶` charge are gone. `②` is `descentCost_on_tinhofer`
below, and is likewise the key's cost alone. -/
theorem canonizes_on_tinhofer {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.SoundOpt
        (canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key))
    ∧ (∀ (G H : AdjMatrix n) (cG cH : CanonSpec.Labelled n), TwinFamily.TinhoferGraph G →
        canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) G = some cG →
        canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) H = some cH →
        (CanonSpec.GraphIso G H ↔ cG = cH))
    ∧ (∀ adj : AdjMatrix n,
        canonForm? (Refine.encodeFreeFast (n := n)) (ForcePick.forceThenPick key) adj ≠ none) := by
  refine ⟨soundOpt_canonForm? _ _, ?_, ?_⟩
  · exact fun G H cG cH hG h1 h2 =>
      complete_on Refine.refineEquivariant_encodeFreeFast (narrowTransportOn_tinhofer hk) hG
        cG cH h1 h2
  · intro adj
    rw [Refine.encodeFreeFast_eq]
    exact canonForm?_ne_none Refine.refineSplits_encodeFree
      (ForcePick.narrowProper_forceThenPick key) adj

/-- **`②`** — the same object's explicit polynomial budget, on **every** input (`ForcePick`'s bound is
unconditional; only the key's cost is billed, since there is no supply). At `Hol.holKeyFast`, `kc = n⁵`. -/
theorem descentCost_on_tinhofer (adj : AdjMatrix n) :
    descentCost (Refine.encodeFreeFast (n := n))
        (ForcePick.forceThenPick (Hol.holKeyFast (n := n))) adj
      ≤ n * n * n + (n + 1) * (1 + n * n * n + (n * (n * n * n * n * n) + n * n)) :=
  ForcePick.descentCost_forceThenPick_le (fun χ => le_of_eq (Cost.refiner_cost adj χ))
    (fun χ v => RecordCost.keyCost_holKeyFast_le adj χ v)

/-- The whole package at a **computable, equivariant** key — the publication statement. -/
theorem canonizes_on_tinhofer_holKeyFast :
    CanonSpec.SoundOpt
        (canonForm? (Refine.encodeFreeFast (n := n))
          (ForcePick.forceThenPick (Hol.holKeyFast (n := n))))
    ∧ (∀ (G H : AdjMatrix n) (cG cH : CanonSpec.Labelled n), TwinFamily.TinhoferGraph G →
        canonForm? (Refine.encodeFreeFast (n := n))
          (ForcePick.forceThenPick (Hol.holKeyFast (n := n))) G = some cG →
        canonForm? (Refine.encodeFreeFast (n := n))
          (ForcePick.forceThenPick (Hol.holKeyFast (n := n))) H = some cH →
        (CanonSpec.GraphIso G H ↔ cG = cH))
    ∧ (∀ adj : AdjMatrix n,
        canonForm? (Refine.encodeFreeFast (n := n))
          (ForcePick.forceThenPick (Hol.holKeyFast (n := n))) adj ≠ none) :=
  canonizes_on_tinhofer Hol.keyEquivariant_holKeyFast

end RestrictedTransport
end ChainDescent
