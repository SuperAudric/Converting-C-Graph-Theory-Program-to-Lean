import ChainDescent.DeepenGuard
import ChainDescent.SelectNode

/-!
# `KeySeparates` — the ONE predicate the dual resolver reduces to

## What this file is

The consume side and the force side each carry a domain hypothesis today: consume carries `Tinhofer`
(per family, and *deciding* it is the automorphism-partition problem — GI-complete by Booth–Colbourn
§2.3), force carries `SolverSeparates` (the rigid seal's separation obligation). This file states the
predicate that **absorbs the first into the second** and proves the absorption:

> **`KeySeparatesAt key adj χ`** — the force key separates every pair in the branch cell that no
> colour-automorphism links.

Under it, the argmin of the key over the branch cell is *semantically* a single orbit
(`forcedSet_single_orbit_of_keySeparatesAt`) — so consume has nothing left to certify: keeping one
representative of the forced set is licensed by an automorphism that **exists but was never computed**.
The consume-side guard (`Tinhofer` / `CertPath`) stops being a correctness prerequisite and becomes a
*firing accelerator*.

## ⚠ The honest label: this is a UNIFICATION, not a weakening

`KeySeparates` is not weaker than the wall. A cell that is a single orbit contains **no**
non-automorphic pairs, so "separates every non-automorphic pair" carries no exception clause — a key
with this property globally collapses every cell to one orbit, which is the target. What the reduction
buys is that there is now **one** named carried predicate about an object under construction, instead
of two coupled ones. Compare the recorded verdict on `hImprim`: *consolidation, not breakthrough*.

**This is the repaired form of a dead route — read the obituaries before re-scoping it.** The retired
`assume-VT` prune (`docs/chain-descent-cost-model.md` §7a, `endgame-spec` §1a) consumed without a
verified automorphism on a *threshold-gated* flag (`base > baseMax`), and crash-landed on **fusion**: a
conditional symmetry fused with a rigid decision (Chang-A) is not vertex-transitive, so pruning it was
unsound. The repair is structural — Algorithm A had **no force resolver**, so "unresolved" conflated
*VT* with *fused*; Chang-A's rigid decision is exposed once the symmetry is consumed
(`A_stall < A_full`) and force acts on it, so `KeySeparatesAt` is *false* at that node and the licence
never fires there. The separate 2026-07-10 vacuity failure (`ConfinementCitations.hflag` uninhabited)
does **not** transfer: that was a universally-quantified citation bundle, where this is a per-node
predicate with measured inhabitants (§3).

⚠ **The surviving objection, recorded so it is checked and not assumed** (the 2026-07-10 audit's FORK).
`KeySeparatesAt` is only informative when the key's failure to separate means *"no separation exists"*
and not *"the key deferred"*. A guarded key that returns a constant off its guard satisfies the
*negation* of the hypothesis vacuously — which is why §3's instantiations carry the guard as an
explicit hypothesis rather than dropping it.

**★ §4a SHARPENS THE LABEL ABOVE, and settles the falsifier question by theorem.** The unguarded read
satisfies `KeySeparates` **globally, at `n⁴` cost** (`keySeparates_rawKey`, from the unconditional
`isColAut_of_readKey_eq`). So `KeySeparates` *alone* is cheap and is **not** the wall; what is GI-hard
is the conjunction `KeySeparates ∧ Force.KeyEquivariant`. The two built keys sit on opposite sides of
it: `rawKey` separates but is not equivariant (its `leafOf` breaks ties by vertex index); `orbKey` /
`orbKeyG` buy equivariance with a guard and pay in separation coverage wherever the guard shuts. **The
guard purchases equivariance, not separation** — and the "falsifier" for the guarded keys is therefore
trivial and uninformative (any two non-automorphic branches whose guards are both shut).

## What is proved here

* §1 the predicate, per node and globally.
* §2 **`forcedSet_single_orbit_of_keySeparatesAt`** — the exhaustiveness corollary: under the
  hypothesis the forced set is a single `IsColAut`-orbit, *whatever* the key is.
* §2 **`forceThenConsume_singleton_of_forcedWordReach`** — the composite's firing lemma generalized
  from `CellIsOrbit` (a statement about the WHOLE cell, false at a mixed node) to the forced set.
  This is the brick `Composite.forceThenConsume_singleton_of_cellIsOrbit` was missing.
* §3 non-vacuity: `orbKey` satisfies the predicate at every `Tinhofer` node, `orbKeyG S` at every
  `CertifiedG S` node.
* §4 **`forceThenConsume_singleton_of_tinhofer`** and **`nodeResolved_of_tinhofer`** — the mixed
  firing theorem: at an `Tinhofer` node the composite narrows the branch cell to **exactly one**
  branch, hence `Select.NodeResolved`. Note this is *not* reachable through `Cost.CellResolved`: at a
  mixed node (cell has ≥ 2 orbits, key ties inside each) **neither** of its two disjuncts holds, yet
  the composite resolves. `NodeResolved` is the honest predicate and is discharged directly.
* §4a **`keySeparates_rawKey`** — the separation half is poly-achievable on its own; the wall is its
  conjunction with `KeyEquivariant`.
* §5 **`reaches_of_descentReach`** — the bridge from `DeepenLocated`'s relocation relation to
  `Descend.Reaches`, which is what `HandledS` quantifies over; then
  **`consume_fail_locates_resolved`**, which is `consume_fail_force_fires` with both of its weaknesses
  removed (the node is a node the canonizer *visits*, and the conclusion is `≤ 1`, not merely strict).
-/

namespace ChainDescent
namespace KeyComplete

open ChainDescent.Consume (IsColAut Supply verified WordReach)
open ChainDescent.Force (Key keyV keepMin)

variable {n : Nat}

/-! ## 1. The predicate -/

/-- **`KeySeparatesAt`** — at this node, the key separates every branch pair that no colour-automorphism
links. Equivalently (contrapositive): *equal keys inside the branch cell ⟹ same orbit*. -/
def KeySeparatesAt (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ Descend.branches χ, ∀ w ∈ Descend.branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
      keyV key adj χ u ≠ keyV key adj χ w

/-- The global form — the carried obligation. This is the force side's `SolverSeparates` stated against
the descent's own branch cell, and by §2 it is *also* everything the consume side needs. -/
def KeySeparates (key : Key n) (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, ¬ Discrete χ → KeySeparatesAt key adj χ

/-! ## 2. ★★ THE EXHAUSTIVENESS COROLLARY

Everything in the forced set shares the key's minimum value (that is what `keepMin` is), so the
hypothesis applies to every pair in it and returns an automorphism. No property of the key beyond
`KeySeparatesAt` is used — in particular no equivariance, no guard, no supply. -/

/-- **★★★ The forced set is a single `IsColAut`-orbit.** The generic form of
`Deepen.forcedSet_single_orbit`, with `KeySeparatesAt` in place of `Tinhofer` + `orbKey`'s internals.

This is the whole content of the reduction: after force has acted, *any* two survivors are related by
a genuine automorphism, so discarding all but one is sound **without a certificate**. -/
theorem forcedSet_single_orbit_of_keySeparatesAt {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    (hK : KeySeparatesAt key adj χ) {u w : Fin n}
    (hu : u ∈ Composite.forcedSet key adj χ) (hw : w ∈ Composite.forcedSet key adj χ) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  obtain ⟨hub, hminu⟩ := (Force.mem_keepMin_iff u).mp hu
  obtain ⟨hwb, hminw⟩ := (Force.mem_keepMin_iff w).mp hw
  have hkey : keyV key adj χ u = keyV key adj χ w :=
    Descend.lexLeList_antisymm _ _ (hminu w hwb) (hminw u hub)
  by_contra hno
  exact hK u hub w hwb (fun σ hσ hσuw => hno ⟨σ, hσ, hσuw⟩) hkey

/-- **The composite's firing lemma, generalized to the FORCED SET.**
`Composite.forceThenConsume_singleton_of_cellIsOrbit` asks for `CellIsOrbit S` — a statement about the
**whole** branch cell, which is false at exactly the mixed nodes the composite exists for. All the
proof ever needs is that `rep` is constant on the forced set, i.e. pairwise `WordReach` there. -/
theorem forceThenConsume_singleton_of_forcedWordReach {key : Key n} {S : Supply n}
    {adj : AdjMatrix n} {χ : Colouring n} (hd : ¬ Discrete χ)
    (hreach : ∀ a ∈ Composite.forcedSet key adj χ, ∀ b ∈ Composite.forcedSet key adj χ,
      WordReach (verified S adj χ) a b) :
    (Descend.narrow (Composite.forceThenConsume key S) adj χ).length = 1 := by
  rw [Composite.narrow_forceThenConsume]
  exact Consume.dedup_map_length_one (Composite.forcedSet_ne_nil key adj hd)
    (fun a ha b hb => Consume.rep_eq_of_wordReach (hreach a ha b hb))

/-! ## 3. Non-vacuity — the built keys satisfy the predicate on their guards

⚠ Neither instantiation is global: both carry the guard, exactly as the FORK warns. `orbKey` off its
guard returns the constant `[]`, so it does **not** satisfy `KeySeparates` unconditionally, and this
file does not pretend otherwise. -/

/-- `orbKey` separates every non-automorphic branch pair at an `Tinhofer` node. -/
theorem keySeparatesAt_orbKey_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n}
    (hA : Deepen.Tinhofer adj χ) : KeySeparatesAt Deepen.orbKey adj χ :=
  fun u hu w hw hno => Deepen.orbKey_ne_of_no_aut (hA u hu) (hA w hw) hno

/-- The poly-guarded key, on its own guard. -/
theorem keySeparatesAt_orbKeyG_of_certifiedG {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (hG : Deepen.CertifiedG S adj χ) : KeySeparatesAt (Deepen.orbKeyG S) adj χ :=
  fun u hu w hw hno => Deepen.orbKeyG_ne_of_no_aut (hG u hu) (hG w hw) hno

/-! ## 4. ★★★ THE MIXED FIRING THEOREM

At an `Tinhofer` node the composite resolves the branch cell **completely** — one branch, no fan-out —
and it does so in the case neither `Cost.CellResolved` disjunct covers. The consume half is supplied by
`Deepen.deepen_branch_orbit_iff_aut` (deepen's branch orbits ARE the `IsColAut`-orbits at an `Tinhofer`
node), which has been landed since 2026-07-23; the force half is §2. -/

/-- **The composite narrows an `Tinhofer` node's branch cell to exactly one branch.** -/
theorem forceThenConsume_singleton_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n}
    (hd : ¬ Discrete χ) (hA : Deepen.Tinhofer adj χ) :
    (Descend.narrow (Composite.forceThenConsume Deepen.orbKey Deepen.deepenSupply) adj χ).length
      = 1 :=
  forceThenConsume_singleton_of_forcedWordReach hd (fun _a ha _b hb =>
    (Deepen.deepen_branch_orbit_iff_aut adj χ hA
        (Composite.forcedSet_subset _ adj χ ha)).mpr
      (forcedSet_single_orbit_of_keySeparatesAt (keySeparatesAt_orbKey_of_tinhofer hA) ha hb))

/-- **★★ `Select.NodeResolved` at every `Tinhofer` node** — the predicate `HandledS` (hence `②`'s
single path and `③`'s flag characterization) actually consumes. The landed hook
`Deepen.consume_fail_force_fires` gives only *strict* narrowing, which nothing downstream reads; this
gives `≤ 1`. -/
theorem nodeResolved_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n} (hd : ¬ Discrete χ)
    (hA : Deepen.Tinhofer adj χ) :
    Select.NodeResolved Deepen.orbKey Deepen.deepenSupply adj χ := by
  obtain ⟨c₀, hc₀⟩ := Select.exists_targetColour_of_not_discrete hd
  refine ⟨c₀, Finset.mem_of_min hc₀, ?_⟩
  rw [Select.cellNarrow_targetColour hc₀]
  exact le_of_eq (forceThenConsume_singleton_of_tinhofer hd hA)

/-! ## 4a. ★★★ `KeySeparates` ALONE IS POLY-ACHIEVABLE — the honest decomposition

The scoping doc's §10.4 asks for a falsifier: *a node where the key ties the whole cell and the cell has
≥ 2 true orbits.* For the **guarded** keys that falsifier is trivial and uninteresting — off its guard
`orbKey` returns the constant `[]`, so any two non-automorphic branches with both guards shut tie. But
that is a statement about the *guard*, not about the read, and the read settles the question outright:

> `DeepenExact.isColAut_of_readKey_eq` is **unconditional** — equal reads of two whole-graph-discrete
> leaves force a colour-automorphism. So the **unguarded** read *never* ties a non-automorphic pair.

Hence `KeySeparates` is satisfied, globally and at poly cost, by the raw read (`rawKey` below). **This
sharpens §10.2's label.** `KeySeparates` on its own is *not* the wall and is *not* equivalent to the
target — it is cheap. What is GI-hard is the **conjunction**

    `KeySeparates key adj`  ∧  `Force.KeyEquivariant key`

and the two built keys sit on the two sides of it: `rawKey` has separation and **fails** equivariance
(its `leafOf` breaks ties by vertex index); `orbKey`/`orbKeyG` buy equivariance with a guard and **pay
in separation coverage** wherever the guard shuts. The guard is not protecting the *separation* — it is
purchasing the *equivariance*, and that is the whole trade. -/

/-- The unguarded read: `orbKey` with the `if` removed. **Not** `KeyEquivariant` — the greedy descent
picks by vertex index — so it is not usable as a force key. It exists to make the decomposition above a
theorem rather than a remark. -/
def rawKey : Force.Key n := fun adj χ v =>
  (Deepen.readKey adj (Descend.indivOne χ v) (Deepen.leafOf adj n (Deepen.step adj χ v)).col,
   n * n * n * n)

@[simp] theorem keyV_rawKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (rawKey (n := n)) adj χ v =
      Deepen.readKey adj (Descend.indivOne χ v) (Deepen.leafOf adj n (Deepen.step adj χ v)).col :=
  rfl

/-- **★★ `KeySeparates` holds for the raw read, with no hypothesis and at `n⁴` cost.** So the predicate
is *non-vacuous globally*, and the wall is the conjunction with `KeyEquivariant`, not this half. -/
theorem keySeparates_rawKey (adj : AdjMatrix n) : KeySeparates (rawKey (n := n)) adj := by
  intro χ _ u _ w _ hno hkey
  rw [keyV_rawKey, keyV_rawKey] at hkey
  obtain ⟨ρ, hρ, hρu⟩ :=
    Deepen.isColAut_of_readKey_eq (χ := χ) (u := u) (w := w)
      (Deepen.leafOf_discrete_n adj (Deepen.step adj χ u))
      (Deepen.leafOf_lt adj n (Deepen.step adj χ u) (fun x => Deepen.step_col_lt adj χ u x))
      (Deepen.leafOf_discrete_n adj (Deepen.step adj χ w))
      (Deepen.leafOf_lt adj n (Deepen.step adj χ w) (fun x => Deepen.step_col_lt adj χ w x))
      hkey
  exact hno ρ hρ hρu

/-- Consequently the forced set of the raw read is a single orbit — the exhaustiveness corollary at a
key that satisfies its hypothesis unconditionally. -/
theorem forcedSet_single_orbit_rawKey {adj : AdjMatrix n} {χ : Colouring n} (hd : ¬ Discrete χ)
    {u w : Fin n} (hu : u ∈ Composite.forcedSet (rawKey (n := n)) adj χ)
    (hw : w ∈ Composite.forcedSet (rawKey (n := n)) adj χ) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w :=
  forcedSet_single_orbit_of_keySeparatesAt (keySeparates_rawKey adj χ hd) hu hw

/-! ## 5. `DescentReach ⟹ Descend.Reaches` — the bridge D1 needed
orbKeyG
`Select.HandledS` quantifies over `Descend.Reaches`; `DeepenLocated`'s relocation delivers
`DescentReach`. The two step relations carry **exactly** the same side condition (a vertex with a
same-colour partner — `Descend.Reaches.step` vs `DescentReach.cons`) and `Deepen.step` *is*
`refineV encodeFreeFast ∘ indivOne`, so the bridge is near-definitional. Without it the node D1 produces
is not formally known to be one the canonizer visits. -/

theorem step_col_eq_refineV (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (Deepen.step adj χ v).col
      = Descend.refineV (Refine.encodeFreeFast (n := n)) adj (Descend.indivOne χ v) := by
  rw [Refine.refineV_encodeFreeFast]; exact Deepen.step_col_eq adj χ v

/-- **The bridge.** Everything `DescentReach` can walk to, the descent can reach. -/
theorem reaches_of_descentReach {adj : AdjMatrix n} {χ ψ : Colouring n}
    (h : Deepen.DescentReach adj χ ψ) :
    Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ →
      Descend.Reaches (Refine.encodeFreeFast (n := n)) adj ψ := by
  induction h with
  | refl _ => exact id
  | cons v hp _ ih =>
      intro hχ
      refine ih ?_
      obtain ⟨u, huv, hcol⟩ := hp
      have hnd : ¬ Discrete _ := fun hdisc => huv (hdisc u v hcol)
      have hstep := Descend.Reaches.step (v := v) hχ hnd ⟨u, huv, hcol⟩
      rw [← step_col_eq_refineV] at hstep
      exact hstep

/-- **★★ A consume failure locates a REACHED node that the fused resolver RESOLVES** — and which
carries a genuine rigid decision in its branch cell. This is `DeepenExact.consume_fail_force_fires`
with its two weaknesses removed: the node is now known to be one the canonizer visits (§5), and the
conclusion is `NodeResolved` (`≤ 1`) rather than strict narrowing (§4). -/
theorem consume_fail_locates_resolved {adj : AdjMatrix n} {χ : Colouring n}
    (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) (hd : ¬ Discrete χ)
    (hfail : ¬ Consume.CellIsOrbit Deepen.deepenSupply adj χ) :
    ∃ ψ : Colouring n,
      Descend.Reaches (Refine.encodeFreeFast (n := n)) adj ψ ∧
      Select.NodeResolved Deepen.orbKey Deepen.deepenSupply adj ψ ∧
      ∃ cid, Descend.targetColour ψ = some cid ∧ Deepen.RigidObstructionAt adj ψ cid := by
  obtain ⟨ψ, hreach, hAψ, ⟨cid, hct, hobs⟩, _⟩ :=
    Deepen.consume_fail_force_fires_guarded (Deck.deckSupply (n := n)) adj hd hfail
  have hrψ := reaches_of_descentReach hreach hr
  -- the obstruction itself witnesses non-discreteness: a same-colour pair no automorphism links
  -- cannot be a single vertex (the identity would link it), so `ψ` has two vertices of colour `cid`.
  obtain ⟨u, w, hu, hw, hno⟩ := hobs
  have huw : u ≠ w := fun h => hno 1 (IsColAut.one adj ψ) (by simpa using h)
  have hdψ : ¬ Discrete ψ := fun hdisc => huw (hdisc u w (hu.trans hw.symm))
  exact ⟨ψ, hrψ, nodeResolved_of_tinhofer hdψ hAψ, cid, hct, ⟨u, w, hu, hw, hno⟩⟩

/-- **`HandledS` on the all-`Tinhofer` class** — the first population of the sel-aware capability
predicate, which `chain-descent-remaining-work.md` §1T records as having **zero** families today.
The hypothesis is per-node over the REACHED set, not the global `∀ adj χ` of
`deepenSupply_guarded_canonizer_direct`. -/
theorem handledS_of_reached_tinhofer {adj : AdjMatrix n}
    (hA : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ →
      ¬ Discrete χ → Deepen.Tinhofer adj χ) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  fun χ hr hd => nodeResolved_of_tinhofer hd (hA χ hr hd)

end KeyComplete
end ChainDescent
