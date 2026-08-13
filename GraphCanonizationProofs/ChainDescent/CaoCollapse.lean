import ChainDescent.CaoTarget
import ChainDescent.CaoEnsemble

/-!
# The single-copy collapse — the Lean footing for the item-1 proof plan

(`docs/chain-descent-cao-carrier-falsifiers.md` **§6d** and **§6e**. Read §6d.1 first: it is the
*method*, and it is the reason a **guess** can prove an upper bound.)

## What this file is

The falsifier programme reduced to one question: how strong is the gauge ensemble's 2-WL colouring?
The ensemble has `L·2^{C(L,2)}` vertices, so it cannot be computed — but §6d.1 observes that it does
not have to be. `wl` is the **coarsest** stable refinement of the atoms, so *exhibiting* any stable
colouring that refines the atoms bounds the closure from above, with no computation on the big object
at all.

That method is already machine-checked in this repo (`CaoTarget.refines_wl2_of_stable`, from FT1's
`PartitionClosure.refines_wl_of_stable`). This file does three things with it:

| | |
|---|---|
| **§1** | names the method in the form the collapse argument cites, at `rootPair` and at `ext` |
| **§2** | the **round-indexed** form, which is the skeleton resolution **R1** of §6e.5 needs |
| **§3** | the frame layer: slots, the `S_L` action, and the classification `(t, t', |k ∩ k'|)` of §6d.2(a) — with **invariance proved** and the **`≤ 12` bound proved** |

⚠ **What is deliberately NOT here.** The ensemble itself is not constructed, and §6d.2(b) — the
cross-copy averaging — is not proved; §6e.4 is exactly that gap. Per the standing steer, a pinned
statement nobody has proved can be false, so the one open piece appears as a `Prop`
(`FrameClassComplete`) rather than as a theorem, in the same style as `CaoEnsemble.Propagates`.

★ **Direction discipline (§6d.1).** The bound says the closure is *coarser* than the guess. So a
**merge** in the guess forces a merge in the closure — which is what refutes CAO propagation — while a
**separation** in the guess implies nothing whatever about the ensemble. Every use of §1 must check
which side it is on.
-/

namespace ChainDescent
namespace CaoCollapse

open ChainDescent.PartitionClosure
open ChainDescent.CaoTarget

variable {n : Nat}

/-! ## 1. ★★★ The method — a stable guess bounds the closure from above -/

/-- **★★★ THE METHOD, at the root closure (doc §6d.1).** Any 2-WL-**stable** colouring `s` that
refines the atoms is refined *by nothing coarser than* the closure: `rootPair adj` is coarser than
`s`. So an upper bound on the ensemble's 2-WL needs only a guess plus a stability check — never a
computation on the exponential object.

This is `CaoTarget.refines_wl2_of_stable` with `rootPair` unfolded; it is restated here because the
collapse argument cites it in exactly this shape and the unfolding is the part that is easy to get
backwards. -/
theorem rootPair_upperBound_of_stable {adj : AdjMatrix n} {s : Col2 n}
    (hs : Stable (round2 (n := n)) s) (h : PartitionClosure.Refines s (initCol2 adj)) :
    PartitionClosure.Refines s (rootPair adj) :=
  refines_wl2_of_stable hs h

/-- **The same, after individualization** — which is the shape CAO propagation actually asks about,
since the hypothesis individualizes a vertex before taking the closure. -/
theorem ext_upperBound_of_stable {c s : Col2 n} {v : Fin n}
    (hs : Stable (round2 (n := n)) s) (h : PartitionClosure.Refines s (meet c (ptsPair v))) :
    PartitionClosure.Refines s (ext c v) :=
  refines_wl2_of_stable hs h

/-- **A merge in the guess is a merge in the closure.** The usable direction of §6d.1, isolated so
that a refutation argument cites it and cannot silently use the other one: if a stable `s` refining
the atoms gives two pairs the *same* colour, the closure does too. -/
theorem merge_of_stable_merge {adj : AdjMatrix n} {s : Col2 n}
    (hs : Stable (round2 (n := n)) s) (h : PartitionClosure.Refines s (initCol2 adj))
    {p q : Fin n × Fin n} (hpq : s p = s q) : rootPair adj p = rootPair adj q :=
  rootPair_upperBound_of_stable hs h p q hpq

/-! ## 2. R1's skeleton — the bound holds at every round, not only at the fixpoint

§6e.5's resolution **R1** proves the collapse by induction on the WL round. The round-indexed form of
the method is what that induction consumes: the guess bounds *every* iterate, so an inductive
invariant maintained round by round suffices. -/

/-- **The round-indexed method.** A stable guess refining `c` refines every iterate of the round — so
an induction on rounds may assume the bound at round `k` when establishing it at `k + 1`. -/
theorem rounds_upperBound_of_stable {c s : Col2 n} (hs : Stable (round2 (n := n)) s)
    (h : PartitionClosure.Refines s c) (k : Nat) :
    PartitionClosure.Refines s ((round2 (n := n))^[k] c) :=
  refines_iterate_of_stable isRound_round2 hs h k

/-! ## 3. The frame layer (§6d.2(a))

A slot is an unordered pair of labels; the frame carries two vertices per slot, one per type. §6d.2(a)
observes that frame–frame pair colours can never exceed **12**, for every `L`: WL is coarser than the
orbit partition (`CaoTarget.inv2_wl2`, already machine-checked), and `S_L`'s orbits on ordered pairs
of slots are classified by `|k ∩ k'| ∈ {0,1,2}`.

Two halves. **Invariance** — `|k ∩ k'|` is an `S_L`-invariant — is proved below, together with the
`≤ 2` bound that yields `2 · 2 · 3 = 12`. **Completeness** — that the invariant *separates* the orbits
— is the pinned target; it needs `4 ≤ L` and an extension of a partial injection to a permutation. -/

section Frame

variable {L : Nat}

/-- A slot: an unordered pair of labels. -/
def Slot (L : Nat) : Type := {s : Finset (Fin L) // s.card = 2}

instance : DecidableEq (Slot L) := Subtype.instDecidableEq

/-- The label group acts on slots. -/
def mapSlot (σ : Equiv.Perm (Fin L)) (k : Slot L) : Slot L :=
  ⟨k.1.image σ, by rw [Finset.card_image_of_injective _ σ.injective]; exact k.2⟩

@[simp] theorem mapSlot_val (σ : Equiv.Perm (Fin L)) (k : Slot L) :
    (mapSlot σ k).1 = k.1.image σ := rfl

/-- **The 12 classes.** A frame–frame pair carries its two types and the size of the slot overlap —
and §6d.2(a) says the ensemble's 2-WL colouring of frame pairs is exactly this, for every `L`. -/
def frameClass (k k' : Slot L) (t t' : Bool) : Bool × Bool × Nat :=
  (t, t', (k.1 ∩ k'.1).card)

/-- **Invariance.** The classification is constant on `S_L`-orbits, so the orbit partition of frame
pairs is at least as coarse as `frameClass`. -/
theorem frameClass_mapSlot (σ : Equiv.Perm (Fin L)) (k k' : Slot L) (t t' : Bool) :
    frameClass (mapSlot σ k) (mapSlot σ k') t t' = frameClass k k' t t' := by
  simp only [frameClass, mapSlot_val]
  refine congrArg _ (congrArg _ ?_)
  rw [← Finset.image_inter _ _ σ.injective, Finset.card_image_of_injective _ σ.injective]

/-- The overlap of two slots is at most `2`, so `frameClass` takes at most `2 · 2 · 3 = 12` values —
the `≤ 12` of §6d.2(a), and it is uniform in `L`. -/
theorem frameClass_overlap_le (k k' : Slot L) : (k.1 ∩ k'.1).card ≤ 2 := by
  have h : (k.1 ∩ k'.1).card ≤ k.1.card := Finset.card_le_card Finset.inter_subset_left
  rwa [k.2] at h

/-- **⛔ THE PINNED TARGET — the completeness half of §6d.2(a).** That `frameClass` *separates* the
`S_L`-orbits, i.e. two ordered slot pairs with equal overlap are related by a label permutation.

⚠ Stated, not proved, and deliberately so: this project's standing steer is that a pinned statement
nobody has tried to prove can be false — *prove the pin, do not cite it*. It needs `4 ≤ L` (with
`L = 3` there are no two disjoint slots, so the `overlap = 0` class is empty) and the extension of a
partial injection on at most four points to a permutation of `Fin L`. -/
def FrameClassComplete (L : Nat) : Prop :=
  4 ≤ L → ∀ k k' m m' : Slot L, (k.1 ∩ k'.1).card = (m.1 ∩ m'.1).card →
    ∃ σ : Equiv.Perm (Fin L), mapSlot σ k = m ∧ mapSlot σ k' = m'

/-- Completeness would give what §6d.2(a) is used for: the orbit partition of frame pairs is *exactly*
`frameClass`, hence at most 12 cells, hence — since WL is coarser than orbits — so is the ensemble's
frame–frame colouring. This records the implication so that proving the pin immediately discharges the
consumer. -/
theorem frameClass_eq_orbit_of_complete (hc : FrameClassComplete L) (hL : 4 ≤ L)
    (k k' m m' : Slot L) (t t' : Bool)
    (h : frameClass k k' t t' = frameClass m m' t t') :
    ∃ σ : Equiv.Perm (Fin L), mapSlot σ k = m ∧ mapSlot σ k' = m' := by
  refine hc hL k k' m m' ?_
  simpa only [frameClass, Prod.mk.injEq, true_and] using h

end Frame

end CaoCollapse
end ChainDescent
