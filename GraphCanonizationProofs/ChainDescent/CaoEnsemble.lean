import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Common

/-!
# The gauge-ensemble CAO construction — the index-level skeleton

(`docs/chain-descent-cao-carrier-falsifiers.md` §3 and §6.  Read §0's two necessary conditions first.)

## What this file is, and what it deliberately is not

Construction C builds a graph out of three kinds of vertex — **payload copies**, a shared **frame**
of gauge cubes, and **central vertices** which *are* the gauge choices.  Everything that matters
about it is already visible at the level of the **index data**: a copy is a colouring `Col = Slot →
Bool`, a central vertex is a gauge `Col`, the gauge acts by pointwise `xor`, and the label group acts
through its induced permutation of slots.  This file formalizes that layer and nothing else.

**It is a skeleton, not the construction.**  There is no graph, no adjacency and no WL refinement
here.  What it does buy is that the two facts every measurement silently rests on become theorems
rather than hand-arguments, and the propagation target acquires a statement:

| | fact | here |
|---|---|---|
| **T1** | the copies are a **single gauge orbit** ⟹ the CAO start is coarse ⟹ the hypothesis is satisfiable | `gact_transitive` |
| **T2⁻** | the gauge part of the stabilizer of the base point is **trivial**, and the label group is **inside** it | `gact_eq_self_iff`, `lact_base` |
| **T2⁺** | `Aut_m` is *exactly* the label group | ⛔ **not here** — needs `Aut(T(n)) = Sym n` and the graph |
| **T3** | after individualization the frame's cells are the position classes | ⛔ **not here** — needs the refiner |
| **T5** | two copies with non-isomorphic payloads share a WL cell | ⛔ the open content; `Propagates` states it |

⚠ **`Propagates` is the target *stated*, not proved.**  Per this project's standing steer, a pinned
statement nobody has tried to prove can be false — this one is pinned so the measurements have
something to instantiate, and `not_propagates_of_merge` is the only bridge between them.

## ★ Why the base point is `fun _ => false` and why that is the whole gadget reduction

The reduction verified on 2026-08-12 (`scratchpad/probe_cao_gadget_variants.py`) halves the frame
from two cubes per slot to one, by attaching **both** payload endpoints to **both** corners of the
pair.  Its content, in this file's language, is exactly `lact_base`: a label permutation fixes the
base gauge, hence fixes the individualized central vertex, hence survives into the stabilizer.  The
measured failure mode (`ordered1`: one cube, ordered attachment, `m` holding one corner) is precisely
a shape where that fails — the transposition is not an automorphism at all.  So the reduction is not
a convenience: `lact_base` is what it buys, and `lact_base` is what `T4` needs.
-/

namespace ChainDescent
namespace CaoEnsemble

variable {Slot : Type*}

/-- A payload copy, and equally a gauge choice: a type assignment to every slot.  `Bool` is the
binary rung; the construction's cubes give a larger alphabet, and nothing below uses the size. -/
abbrev Col (Slot : Type*) : Type _ := Slot → Bool

/-- The gauge action: flip the type of every slot where `h` says so.  One cube's gauge move is the
`h` supported on that slot. -/
def gact (h c : Col Slot) : Col Slot := fun s => xor (h s) (c s)

/-- The base gauge — the central vertex that gets individualized. -/
def base (Slot : Type*) : Col Slot := fun _ => false

/-- The label group acts on copies through its induced permutation of slots. -/
def lact (σ : Equiv.Perm Slot) (c : Col Slot) : Col Slot := fun s => c (σ.symm s)

/-- Two copies are *label-equivalent* when a relabelling carries one to the other.  After the base
point is individualized these classes are the stabilizer-orbits, so at the payload they are the
isomorphism classes of the decoded structure. -/
def LabelEquiv (c c' : Col Slot) : Prop := ∃ σ : Equiv.Perm Slot, lact σ c = c'

section Gauge

/-- **T1 — the copies are one gauge orbit.**  Every colouring is reachable from every other, so
before individualization the whole payload is a single `Aut`-orbit and the CAO start is maximally
coarse.  This is what makes the CAO hypothesis *satisfiable* for the construction; without it the
start colouring already separates the copies and nothing is being tested. -/
theorem gact_transitive (c c' : Col Slot) :
    gact (fun s => xor (c s) (c' s)) c = c' := by
  funext s
  simp only [gact]
  cases c s <;> cases c' s <;> rfl

/-- The gauge acts *freely*: only the trivial gauge fixes a colouring.  Hence individualizing one
central vertex kills the gauge entirely, which is what turns "which corner" into an absolute type. -/
theorem gact_eq_self_iff (h c : Col Slot) :
    gact h c = c ↔ h = base Slot := by
  constructor
  · intro hh
    funext s
    have := congrFun hh s
    simp only [gact, base] at this ⊢
    cases hs : h s <;> cases c s <;> simp [hs] at this ⊢
  · rintro rfl
    funext s
    simp [gact, base]

end Gauge

section Label

/-- **The gadget reduction's payoff.**  A relabelling fixes the base gauge, so it fixes the
individualized central vertex and survives into the stabilizer.  This is the property the
one-cube/both-endpoints frame has and the one-cube/ordered frame does not. -/
@[simp] theorem lact_base (σ : Equiv.Perm Slot) : lact σ (base Slot) = base Slot := rfl

@[simp] theorem lact_one (c : Col Slot) : lact (Equiv.refl Slot) c = c := rfl

/-- ⚠ the composition order is `τ.trans σ`, not `σ.trans τ`: `lact` reindexes by `σ.symm`, and
`(τ.trans σ).symm = σ.symm ≫ τ.symm`. Getting this backwards is a silent `funext` failure. -/
theorem lact_trans (σ τ : Equiv.Perm Slot) (c : Col Slot) :
    lact σ (lact τ c) = lact (τ.trans σ) c := rfl

theorem labelEquiv_refl (c : Col Slot) : LabelEquiv c c :=
  ⟨Equiv.refl Slot, lact_one c⟩

theorem labelEquiv_symm {c c' : Col Slot} (h : LabelEquiv c c') : LabelEquiv c' c := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, ?_⟩
  subst hσ
  funext s
  simp [lact]

end Label

section Propagation

variable {κ : Type*}

/-- A partition of the copies that a refiner could produce: any isomorphism-invariant colouring is
constant on label-orbits, because a relabelling is an automorphism fixing the base point. -/
def LabelInvariant (P : Col Slot → κ) : Prop := ∀ (σ : Equiv.Perm Slot) (c : Col Slot),
  P (lact σ c) = P c

/-- **Cells are unions of orbits — the direction that is free.**  Every WL-style invariant merges at
least the label-equivalent copies.  A CAO failure is therefore always a *strict* coarsening, never a
disagreement in the other direction. -/
theorem eq_of_labelEquiv {P : Col Slot → κ} (hP : LabelInvariant P)
    {c c' : Col Slot} (h : LabelEquiv c c') : P c = P c' := by
  obtain ⟨σ, hσ⟩ := h
  subst hσ
  exact (hP σ c).symm

/-- **The target.**  CAO propagates at `P` exactly when its cells are no coarser than the
label-orbits — i.e. when `P` is a complete isomorphism invariant of the decoded payload. -/
def Propagates (P : Col Slot → κ) : Prop := ∀ c c' : Col Slot, P c = P c' → LabelEquiv c c'

/-- **The bridge the probes instantiate.**  One merged pair of copies that are not label-equivalent
refutes propagation.  Every mixed-cell count on record — 4 for Construction B, 100 for the rung-1
ensemble — is an instance of exactly this. -/
theorem not_propagates_of_merge {P : Col Slot → κ} {c c' : Col Slot}
    (hmerge : P c = P c') (hne : ¬ LabelEquiv c c') : ¬ Propagates P :=
  fun hp => hne (hp c c' hmerge)

/-- …and the converse packaging: propagation is precisely "no mixed cell exists". -/
theorem propagates_iff_no_merge {P : Col Slot → κ} :
    Propagates P ↔ ¬ ∃ c c' : Col Slot, P c = P c' ∧ ¬ LabelEquiv c c' := by
  constructor
  · rintro hp ⟨c, c', hm, hne⟩
    exact hne (hp c c' hm)
  · intro h c c' hm
    by_contra hne
    exact h ⟨c, c', hm, hne⟩

end Propagation

end CaoEnsemble
end ChainDescent
