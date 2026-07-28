import ChainDescent.KeyComplete
import ChainDescent.SupplyCost

/-!
# `forceThenPick` — the resolver that CASHES the exhaustiveness corollary

## What this file is, and why it did not already exist

`KeyComplete.forcedSet_single_orbit_of_keySeparatesAt` proves that under `KeySeparatesAt` the force
key's argmin over the branch cell is a **single `IsColAut`-orbit**. In the DUAL scoping doc's words,
that means *"keeping one representative of the forced set is licensed by an automorphism that exists
but was never computed."* But nothing in the project **used** that licence: every built resolver still
reaches its singleton through consume, i.e. through a *computed* certificate
(`Composite.forceThenConsume` + `WordReach`). The corollary bought a right that no object exercised.

`forceThenPick key` exercises it: force, then keep **one** survivor — `(forcedSet).take 1` — with no
supply, no verification and no orbit search. Its `①` rides the third contract route
(`Descend.CoveringOfAt` at `N = forcedSet`), whose covering witness is `descend_transport` at an
automorphism; here that automorphism is supplied by the corollary rather than by a supply's `verified`
list. This is *exactly* the shape `Descend.lean` §9 describes and no instance had used.

## ★ What it buys — the whole package reduces to ONE conjunction

| | discharged by | hypothesis |
|---|---|---|
| `①a` sound | `Descend.isCanonicalFormOpt_canonForm?` | — |
| `①b`/`①c` iso-invariant | `narrowTransport_forceThenPick` | **`KeyEquivariant` + `KeySeparates`** |
| totality — **the flag NEVER fires** | `narrowProper_forceThenPick` | **none** |
| `②` single path | `resolvedAll_forceThenPick` (`take 1`, by construction) | **none** |
| `②` explicit polynomial | `descentCost_forceThenPick_le` | a `keyCost` bound |

So the canonizer's *entire* remaining content is the conjunction the DUAL doc §10.2 names:

> **`KeySeparates key adj ∧ Force.KeyEquivariant key`, at poly `keyCost`.**

`keySeparates_rawKey` shows the first conjunct alone is cheap (poly, global, unconditional);
`keyEquivariant_orbKey` shows the second alone is free. **The wall is having both at once**, and this
file is where that statement stops being prose: it is the hypothesis set of `forcePick_record`.

## ⚠ What it does NOT buy — read before treating this as progress on the wall

* **It fires nowhere new today.** At a `Tinhofer` node the composite already resolves
  (`KeyComplete.nodeResolved_of_tinhofer`), and off its guard `orbKey`/`orbKeyG` return the constant
  `[]`, which does not separate. So no *built* key satisfies the global `KeySeparates` **and**
  `KeyEquivariant` together, and this resolver's instantiations are the same conditional scaffolds as
  `deepenSupply_guarded_canonizer_direct`. The gain is that two coupled carried predicates
  (`Tinhofer` on consume, `SolverSeparates` on force) become one.
* **The 2026-07-10 FORK objection applies verbatim** (DUAL §10.4). `KeySeparatesAt` is informative
  only when the key's failure to separate means *"no separation exists"*, not *"the key deferred"*. A
  guarded key that returns a constant off its guard satisfies the *negation* vacuously — and, plugged
  into **this** resolver, that is not merely uninformative but **unsound-in-hypothesis**: the
  singleton pick would discard genuinely different branches. The hypothesis is therefore carried
  explicitly at every instantiation and is never claimed for a built key. Do not instantiate
  `forceThenPick` at `orbKey`/`orbKeyG` and read the result as a canonizer.
* **It is not a fourth contract route.** It is the third route (`CoveringOfAt`) at a new intermediate
  witness. Nothing about `descend`, `①` or the contract changes.
-/

namespace ChainDescent
namespace ForcePick

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV keyCost KeyEquivariant keepMin forceBy)
open ChainDescent.Consume (IsColAut)
open ChainDescent.KeyComplete (KeySeparates KeySeparatesAt)

variable {n : Nat}

/-! ## 1. The object -/

/-- **★ THE RESOLVER.** Force (narrow equivariantly to the least-key branches), then keep **one** of
the survivors. The discarded survivors are pairwise automorphic under `KeySeparatesAt`, so the
discard is sound — but, unlike consume's, the automorphism is never computed and costs nothing.

Cost is `forceBy`'s: one key evaluation per branch. There is no supply call and no orbit BFS. -/
def forceThenPick (key : Key n) : Resolver n := fun adj χ B =>
  let F := forceBy key adj χ B
  (some ((F.1.getD B).take 1), F.2)

/-- The narrowing is the first element of the forced set (definitional). -/
theorem narrow_forceThenPick (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceThenPick key) adj χ = (Composite.forcedSet key adj χ).take 1 := rfl

/-- The cost is exactly `forceBy`'s — the pick itself is free (definitional). -/
theorem forceThenPick_cost (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    (forceThenPick key adj χ B).2 = (B.map (keyCost key adj χ)).sum + n * n := rfl

/-! ## 2. `②` — no fan-out, **by construction**

`Stall.guard` buys `ResolvedAll` by *flagging* the nodes it cannot resolve. This buys it by
*resolving* them — at the price of the `KeySeparates` hypothesis on `①`, which is the honest place for
it. Note neither theorem below carries any hypothesis at all: the fan-out bound is structural. -/

theorem narrow_length_le_one (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) :
    (narrow (forceThenPick key) adj χ).length ≤ 1 := by
  rw [narrow_forceThenPick]
  simp

/-- **`Cost.ResolvedAll` with NO hypothesis** — the descent is a single path on every input. -/
theorem resolvedAll_forceThenPick (key : Key n) (adj : AdjMatrix n) :
    Cost.ResolvedAll (forceThenPick key) adj :=
  fun χ _ => narrow_length_le_one key adj χ

/-! ## 3. Properness — **the flag never fires**, with no hypothesis

`Composite.forcedSet_ne_nil` says force never empties a non-discrete cell, and `take 1` of a nonempty
list is a singleton. So this resolver has no stall channel at all: `③`'s residue is *empty* for it,
and every remaining question is pushed onto `①`'s `KeySeparates`. -/

theorem narrowProper_forceThenPick (key : Key n) : NarrowProper (forceThenPick key) := by
  constructor
  · intro adj χ hd
    rw [narrow_forceThenPick]
    cases hL : Composite.forcedSet key adj χ with
    | nil => exact absurd hL (Composite.forcedSet_ne_nil key adj hd)
    | cons p rest => simp
  · intro adj χ v hv
    rw [narrow_forceThenPick] at hv
    exact Composite.forcedSet_subset key adj χ (List.mem_of_mem_take hv)

/-! ## 4. ★★ `①` — the covering, from `KeySeparates` alone

The one new proof in this file. Every member of the forced set is automorphic to the picked one
(`forcedSet_single_orbit_of_keySeparatesAt`), so every member carries the **same branch value**
(`Consume.branchVal_eq_of_isColAut` — `descend_transport` at that automorphism). The mapped value
lists therefore have the same *membership*, which is all `aggregate` reads. -/

theorem coveringOfAt_forceThenPick {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    {adj : AdjMatrix n} (hsep : KeySeparates key adj) :
    ∀ (fuel : Nat), TransportAt rf (forceThenPick key) fuel →
      ∀ χ : Colouring n,
        aggregate ((narrow (forceThenPick key) adj χ).map
            (fun v => (descend rf (forceThenPick key) adj fuel (refineV rf adj (indivOne χ v))).1))
          = aggregate ((Composite.forcedSet key adj χ).map
            (fun v => (descend rf (forceThenPick key) adj fuel (refineV rf adj (indivOne χ v))).1)) := by
  intro fuel ih χ
  rw [narrow_forceThenPick]
  cases hL : Composite.forcedSet key adj χ with
  | nil => simp
  | cons p rest =>
      -- the cell is nonempty, so the node is not discrete and the hypothesis applies here
      have hpF : p ∈ Composite.forcedSet key adj χ := by rw [hL]; exact List.mem_cons_self ..
      have hpB : p ∈ branches χ := Composite.forcedSet_subset key adj χ hpF
      obtain ⟨u, hune, huc⟩ := exists_partner_of_mem_branches hpB
      have hnd : ¬ Discrete χ := fun hdisc => hune (hdisc u p huc)
      have hK : KeySeparatesAt key adj χ := hsep χ hnd
      -- every survivor carries the picked one's branch value
      have hval : ∀ b ∈ Composite.forcedSet key adj χ,
          (descend rf (forceThenPick key) adj fuel (refineV rf adj (indivOne χ b))).1
            = (descend rf (forceThenPick key) adj fuel (refineV rf adj (indivOne χ p))).1 := by
        intro b hbF
        obtain ⟨σ, hσ, hσp⟩ := KeyComplete.forcedSet_single_orbit_of_keySeparatesAt hK hpF hbF
        have h := Consume.branchVal_eq_of_isColAut hre ih adj χ hσ p
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

/-- **★★★ THE CONTRACT, from `{KeyEquivariant, KeySeparates}`.** `KeyEquivariant` makes the forced set
an equivariant intermediate; `KeySeparates` makes the singleton pick cover it. -/
theorem narrowTransport_forceThenPick {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    (hk : KeyEquivariant key) (hsep : ∀ adj : AdjMatrix n, KeySeparates key adj) :
    NarrowTransport rf (forceThenPick key) :=
  narrowTransport_of_coveringOfAt hre (Composite.narrowFnEquivariant_forcedSet hk)
    (fun fuel ih adj χ => coveringOfAt_forceThenPick hre (hsep adj) fuel ih χ)

/-! ## 5. The canonizer -/

/-- **★★★ `①` + TOTALITY for the pick resolver.** The totality half carries **no** hypothesis: this
object cannot flag. -/
theorem forcePick_canonizer {key : Key n} (hk : KeyEquivariant key)
    (hsep : ∀ adj : AdjMatrix n, KeySeparates key adj) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFree (n := n)) (forceThenPick key))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFree (n := n)) (forceThenPick key) adj ≠ none :=
  ⟨Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFree
      (narrowTransport_forceThenPick Refine.refineEquivariant_encodeFree hk hsep),
   fun adj => Descend.canonForm?_ne_none Refine.refineSplits_encodeFree
      (narrowProper_forceThenPick key) adj⟩

/-- The runnable version. -/
theorem forcePick_canonizer_fast {key : Key n} (hk : KeyEquivariant key)
    (hsep : ∀ adj : AdjMatrix n, KeySeparates key adj) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenPick key))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenPick key) adj ≠ none := by
  rw [Refine.encodeFreeFast_eq]
  exact forcePick_canonizer hk hsep

/-! ## 6. `②` — the explicit polynomial

The per-node bill is `forceBy`'s and nothing else (no supply, no verification, no BFS), so the whole
`②` is `n` key evaluations per node over a single path of `≤ n + 1` nodes. -/

theorem forceThenPick_cost_le {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {B : List (Fin n)} {kc : Nat} (hB : B.length ≤ n)
    (hk : ∀ v : Fin n, keyCost key adj χ v ≤ kc) :
    (forceThenPick key adj χ B).2 ≤ n * kc + n * n := by
  rw [forceThenPick_cost]
  have hsum : (B.map (keyCost key adj χ)).sum ≤ B.length * kc := by
    refine le_trans (List.sum_le_card_nsmul _ kc ?_) ?_
    · intro x hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact hk v
    · rw [List.length_map, smul_eq_mul]
  exact Nat.add_le_add (le_trans hsum (Nat.mul_le_mul hB le_rfl)) le_rfl

/-- **★★ `②`, explicit, with NO firing hypothesis** — the fan-out bound is structural, so the only
input is a `keyCost` bound. -/
theorem descentCost_forceThenPick_le {rf : Refiner n} {key : Key n} {adj : AdjMatrix n}
    {c₁ kc : Nat} (hrf : ∀ χ : Colouring n, (rf adj χ).2 ≤ c₁)
    (hk : ∀ (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc) :
    Descend.descentCost rf (forceThenPick key) adj
      ≤ c₁ + (n + 1) * (1 + c₁ + (n * kc + n * n)) :=
  Cost.descentCost_le_of_resolved (resolvedAll_forceThenPick key adj) hrf
    (fun χ => forceThenPick_cost_le (SupplyCost.branches_length_le χ) (hk χ))

/-! ## 7. ★★★ THE RECORD STATEMENT — `①` + `②` + "the flag never fires", in one place

This is the file's point. Read the hypothesis list as the project's target, stated once:

> a force key that is **equivariant**, **separating** and **poly** is a complete polynomial canonizer.

Every clause of the conclusion is unconditional given those three. Nothing here claims such a key
exists — `keySeparates_rawKey` gives the second and third without the first, `keyEquivariant_orbKey`
gives the first without the second. -/

theorem forcePick_record {key : Key n} {c₁ kc : Nat} (hk : KeyEquivariant key)
    (hsep : ∀ adj : AdjMatrix n, KeySeparates key adj)
    (hrf : ∀ (adj : AdjMatrix n) (χ : Colouring n), (Refine.encodeFreeFast (n := n) adj χ).2 ≤ c₁)
    (hkc : ∀ (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc) :
    -- `①a`/`①b`/`①c`
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenPick key))
    -- the flag never fires
    ∧ (∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceThenPick key) adj ≠ none)
    -- `②` explicit polynomial, on every input
    ∧ (∀ adj : AdjMatrix n,
        Descend.descentCost (Refine.encodeFreeFast (n := n)) (forceThenPick key) adj
          ≤ c₁ + (n + 1) * (1 + c₁ + (n * kc + n * n))) :=
  ⟨(forcePick_canonizer_fast hk hsep).1, (forcePick_canonizer_fast hk hsep).2,
   fun adj => descentCost_forceThenPick_le (hrf adj) (hkc adj)⟩

end ForcePick
end ChainDescent
