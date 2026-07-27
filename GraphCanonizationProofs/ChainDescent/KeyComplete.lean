import ChainDescent.DeepenGuard
import ChainDescent.SelectNode

/-!
# `KeySeparates` — the ONE predicate the dual resolver reduces to

## What this file is

The consume side and the force side each carry a domain hypothesis today: consume carries `Amenable`
(per family, and *deciding* it is the automorphism-partition problem — GI-complete by Booth–Colbourn
§2.3), force carries `SolverSeparates` (the rigid seal's separation obligation). This file states the
predicate that **absorbs the first into the second** and proves the absorption:

> **`KeySeparatesAt key adj χ`** — the force key separates every pair in the branch cell that no
> colour-automorphism links.

Under it, the argmin of the key over the branch cell is *semantically* a single orbit
(`forcedSet_single_orbit_of_keySeparatesAt`) — so consume has nothing left to certify: keeping one
representative of the forced set is licensed by an automorphism that **exists but was never computed**.
The consume-side guard (`Amenable` / `CertPath`) stops being a correctness prerequisite and becomes a
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
explicit hypothesis rather than dropping it. The falsifier to hunt is a node where the key ties the
whole cell and the cell has ≥ 2 true orbits; the CFI-cubic `m = 8` node is where exactness and
invariance parted before.

## What is proved here

* §1 the predicate, per node and globally.
* §2 **`forcedSet_single_orbit_of_keySeparatesAt`** — the exhaustiveness corollary: under the
  hypothesis the forced set is a single `IsColAut`-orbit, *whatever* the key is.
* §2 **`forceThenConsume_singleton_of_forcedWordReach`** — the composite's firing lemma generalized
  from `CellIsOrbit` (a statement about the WHOLE cell, false at a mixed node) to the forced set.
  This is the brick `Composite.forceThenConsume_singleton_of_cellIsOrbit` was missing.
* §3 non-vacuity: `orbKey` satisfies the predicate at every `Amenable` node, `orbKeyG S` at every
  `CertifiedG S` node.
* §4 **`forceThenConsume_singleton_of_amenable`** and **`nodeResolved_of_amenable`** — the mixed
  firing theorem: at an `Amenable` node the composite narrows the branch cell to **exactly one**
  branch, hence `Select.NodeResolved`. Note this is *not* reachable through `Cost.CellResolved`: at a
  mixed node (cell has ≥ 2 orbits, key ties inside each) **neither** of its two disjuncts holds, yet
  the composite resolves. `NodeResolved` is the honest predicate and is discharged directly.
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
`Deepen.forcedSet_single_orbit`, with `KeySeparatesAt` in place of `Amenable` + `orbKey`'s internals.

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

/-- `orbKey` separates every non-automorphic branch pair at an `Amenable` node. -/
theorem keySeparatesAt_orbKey_of_amenable {adj : AdjMatrix n} {χ : Colouring n}
    (hA : Deepen.Amenable adj χ) : KeySeparatesAt Deepen.orbKey adj χ :=
  fun u hu w hw hno => Deepen.orbKey_ne_of_no_aut (hA u hu) (hA w hw) hno

/-- The poly-guarded key, on its own guard. -/
theorem keySeparatesAt_orbKeyG_of_certifiedG {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (hG : Deepen.CertifiedG S adj χ) : KeySeparatesAt (Deepen.orbKeyG S) adj χ :=
  fun u hu w hw hno => Deepen.orbKeyG_ne_of_no_aut (hG u hu) (hG w hw) hno

/-! ## 4. ★★★ THE MIXED FIRING THEOREM

At an `Amenable` node the composite resolves the branch cell **completely** — one branch, no fan-out —
and it does so in the case neither `Cost.CellResolved` disjunct covers. The consume half is supplied by
`Deepen.deepen_branch_orbit_iff_aut` (deepen's branch orbits ARE the `IsColAut`-orbits at an `Amenable`
node), which has been landed since 2026-07-23; the force half is §2. -/

/-- **The composite narrows an `Amenable` node's branch cell to exactly one branch.** -/
theorem forceThenConsume_singleton_of_amenable {adj : AdjMatrix n} {χ : Colouring n}
    (hd : ¬ Discrete χ) (hA : Deepen.Amenable adj χ) :
    (Descend.narrow (Composite.forceThenConsume Deepen.orbKey Deepen.deepenSupply) adj χ).length
      = 1 :=
  forceThenConsume_singleton_of_forcedWordReach hd (fun _a ha _b hb =>
    (Deepen.deepen_branch_orbit_iff_aut adj χ hA
        (Composite.forcedSet_subset _ adj χ ha)).mpr
      (forcedSet_single_orbit_of_keySeparatesAt (keySeparatesAt_orbKey_of_amenable hA) ha hb))

/-- **★★ `Select.NodeResolved` at every `Amenable` node** — the predicate `HandledS` (hence `②`'s
single path and `③`'s flag characterization) actually consumes. The landed hook
`Deepen.consume_fail_force_fires` gives only *strict* narrowing, which nothing downstream reads; this
gives `≤ 1`. -/
theorem nodeResolved_of_amenable {adj : AdjMatrix n} {χ : Colouring n} (hd : ¬ Discrete χ)
    (hA : Deepen.Amenable adj χ) :
    Select.NodeResolved Deepen.orbKey Deepen.deepenSupply adj χ := by
  obtain ⟨c₀, hc₀⟩ := Select.exists_targetColour_of_not_discrete hd
  refine ⟨c₀, Finset.mem_of_min hc₀, ?_⟩
  rw [Select.cellNarrow_targetColour hc₀]
  exact le_of_eq (forceThenConsume_singleton_of_amenable hd hA)

/-- **`HandledS` on the all-`Amenable` class** — the first population of the sel-aware capability
predicate, which `chain-descent-remaining-work.md` §1T records as having **zero** families today.
The hypothesis is per-node over the REACHED set, not the global `∀ adj χ` of
`deepenSupply_guarded_canonizer_direct`. -/
theorem handledS_of_reached_amenable {adj : AdjMatrix n}
    (hA : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ →
      ¬ Discrete χ → Deepen.Amenable adj χ) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  fun χ hr hd => nodeResolved_of_amenable hd (hA χ hr hd)

end KeyComplete
end ChainDescent
