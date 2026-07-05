/-
# Generic 1-WL — colour refinement over an arbitrary finite vertex type

Phase 1 of the **no-rigid-Cameron** Lean attack (`docs/chain-descent-wl-visibility.md`).

The top-level `ChainDescent.lean` defines colour refinement (`signature`, `refineStep`,
`refineStep_iff`, `warmRefine`, `samePartition`) on `Fin n`, because the canonizer's
spine/direction invariants are stated there over `Fin n`. The rigid-Cameron rungs (R1,
R2) run 1-WL on graphs built from a finite *group* `Γ` (segments ⊕ product-tuples,
commuting graph), whose natural vertex type is not `Fin n`.

This module re-states the 1-WL primitives over an arbitrary `[Fintype V] [DecidableEq V]`
vertex type, so the rungs avoid all `Fin n` index-encoding. The definitions are the
verbatim generalization of the top-level ones (the originals already quantify over
`Finset.univ`); the only `Fin n`-specific datum, `warmRefine`'s iteration count `n`,
becomes `Fintype.card V`. The single lemma the rungs consume — `refineStep_iff` (same
refined colour ⟺ same old colour ∧ same signature) — is re-derived generically.

The canonizer's `Fin n` invariants are untouched: this module only *adds* a `V`-generic
copy; it reuses the top-level `POE` / `POE.toNat` / `encTuple` (so the encodings agree),
re-proving locally the two `private` injectivity lemmas.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent
import Mathlib.Data.Fintype.Card

namespace ChainDescent
namespace WLGeneric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Graphs and colourings over `V` -/

/-- A colouring assigns each vertex a natural-number colour. -/
def Colouring (V : Type*) := V → Nat

/-- A labelled graph on vertex type `V` (the generic analogue of `AdjMatrix n`'s
`adj` field). -/
abbrev GAdj (V : Type*) := V → V → Nat

/-- A partial-order matrix on `V` (the generic analogue of `PMatrix n`). Pass the
constant `fun _ _ => POE.unknown` for a plain graph. -/
abbrev GPOE (V : Type*) := V → V → POE

/-! ## Signatures -/

/-- The signature of vertex `v`: the multiset of `(neighbour-colour, adjacency-value,
P-relation)` tuples over all `u ≠ v`. Verbatim generalization of the top-level
`signature`; this is the object whose `Γ`-(in)dependence drives the rungs. -/
def signature (adj : GAdj V) (P : GPOE V) (χ : V → Nat) (v : V) :
    Multiset (Nat × Nat × POE) :=
  ((Finset.univ : Finset V).filter (· ≠ v)).val.map fun u => (χ u, adj v u, P v u)

/-! ## The canonical refinement key (local injectivity re-derivations) -/

private theorem toNat_injective : Function.Injective POE.toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem encTuple_injective : Function.Injective encTuple := by
  rintro ⟨c, a, p⟩ ⟨c', a', p'⟩ h
  simp only [encTuple, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl, hp⟩ := h
  obtain rfl := toNat_injective hp
  rfl

/-- The canonical refinement **key** of `v`: old colour, then the sorted (encoded)
signature multiset. Two vertices share a key iff same old colour and same signature. -/
def sigKey (adj : GAdj V) (P : GPOE V) (χ : V → Nat) (v : V) : List Nat :=
  χ v :: Multiset.sort ((signature adj P χ v).map encTuple) (· ≤ ·)

theorem sigKey_eq_iff (adj : GAdj V) (P : GPOE V) (χ : V → Nat) (v w : V) :
    sigKey adj P χ v = sigKey adj P χ w ↔
      χ v = χ w ∧ signature adj P χ v = signature adj P χ w := by
  unfold sigKey
  rw [List.cons.injEq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hsort
    have hmap : (signature adj P χ v).map encTuple
        = (signature adj P χ w).map encTuple := by
      have := congrArg (fun l : List Nat => (↑l : Multiset Nat)) hsort
      simpa only [Multiset.sort_eq] using this
    exact Multiset.map_injective encTuple_injective hmap
  · intro hsig; rw [hsig]

/-! ## Refinement -/

/-- One round of 1-WL refinement: recolour each vertex by the encoded canonical
`sigKey`. Generic analogue of the top-level `refineStep`. -/
def refineStep (adj : GAdj V) (P : GPOE V) (χ : V → Nat) : V → Nat :=
  fun v => Encodable.encode (sigKey adj P χ v)

/-- **The splitting lever.** Two vertices get the same refined colour iff they had
the same old colour AND the same signature. The rungs use only this: equal
signatures ⟹ no split (hideability), unequal ⟹ split (visibility). -/
theorem refineStep_iff (adj : GAdj V) (P : GPOE V) (χ : V → Nat) (v w : V) :
    refineStep adj P χ v = refineStep adj P χ w ↔
      χ v = χ w ∧ signature adj P χ v = signature adj P χ w := by
  show Encodable.encode (sigKey adj P χ v) = Encodable.encode (sigKey adj P χ w) ↔
      χ v = χ w ∧ signature adj P χ v = signature adj P χ w
  rw [Encodable.encode_injective.eq_iff]
  exact sigKey_eq_iff adj P χ v w

/-- Warm refinement: iterate `refineStep` `Fintype.card V` times (the generic
analogue of the top-level `n`-fold iterate; `card V` rounds always suffice since
each non-fixpoint round strictly refines the partition). -/
def warmRefine (adj : GAdj V) (P : GPOE V) (initial : V → Nat) : V → Nat :=
  ((refineStep adj P)^[Fintype.card V]) initial

/-! ## Partition equivalence -/

/-- Two colourings induce the same partition iff their equivalence classes coincide. -/
def samePartition (χ₁ χ₂ : V → Nat) : Prop :=
  ∀ i j : V, χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j

namespace samePartition

omit [Fintype V] [DecidableEq V]

theorem refl (χ : V → Nat) : samePartition χ χ := fun _ _ => Iff.rfl

theorem symm {χ₁ χ₂ : V → Nat} (h : samePartition χ₁ χ₂) :
    samePartition χ₂ χ₁ := fun i j => (h i j).symm

theorem trans {χ₁ χ₂ χ₃ : V → Nat}
    (h₁₂ : samePartition χ₁ χ₂) (h₂₃ : samePartition χ₂ χ₃) :
    samePartition χ₁ χ₃ := fun i j => Iff.trans (h₁₂ i j) (h₂₃ i j)

end samePartition

--#print axioms refineStep_iff
--#print axioms sigKey_eq_iff

end WLGeneric
end ChainDescent
