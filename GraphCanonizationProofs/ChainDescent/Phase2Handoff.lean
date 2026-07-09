import ChainDescent.Cascade

/-!
# Phase-2 handoff — the rigid-residue interface

The Seal Phase (Algorithm A / confinement) consumes symmetry and hands **Phase 2** (the rigid solver —
Algorithm R / the IR-blind-spot solver) a *rigid, iso-invariant residue* `R(G) = rigidResidue adj`
(`Cascade`, brick 2 of the RRU phase-transfer): a **base** of the `P₀`-preserving automorphism group,
so ALL residual symmetry has already been consumed. This file gives Phase 2 a **clean typed object to
work from** — the input, the guarantees it may assume, and the correctness contract a rigid canonizer
must meet — WITHOUT yet building the solver (Algorithm R is a future witness of `Sound`/`IsoInvariant`).

Why the handoff is clean: at `R(G)` the orbit relation is *equality*
(`orbitPartition_handoff_iff_eq`), so Phase 2 is a genuinely **rigid** search — a lex-min over
labellings with no hidden symmetry to collapse. The sole remaining obstruction is IR-stickiness
(refinement failing to discretize — the multipede / IR-blind-spot), which Phase 2 flags
(`Showcase.residueRigidObstruction`, the D2 disjunct of `Publication.UnhandledResidue`).

Scope note: `rigidResidue` individualizes the *whole* residual support (choice-free ⟹ iso-invariant,
CORRECT for the handoff interface); the efficiency-optimal one-representative-per-orbit base is smaller
and is the open *recovery* layer (`docs/chain-descent-remaining-work.md` item 6), not needed here.
-/

namespace ChainDescent
namespace Phase2

variable {n : ℕ}

/-- The trivial order `P₀` the RRU handoff runs at: every permutation preserves it, so the residual
group is the full automorphism group `Aut(adj)`. -/
abbrev trivialP (n : ℕ) : PMatrix n := fun _ _ => POE.unknown

/-- **The handoff base** `R(G)` handed to Phase 2 — the RRU rigid residue (`Cascade.rigidResidue`). -/
noncomputable def handoffBase (adj : AdjMatrix n) : Finset (Fin n) := rigidResidue adj

/-- **The handoff is rigid.** `R(G)` is a base of `Aut^{P₀}(adj)` — the residual automorphism group
fixing it pointwise is trivial. The guarantee Phase 2 may assume, for EVERY input (unconditional). -/
theorem handoff_isRigid (adj : AdjMatrix n) :
    IsBase adj (trivialP n) (handoffBase adj) := by
  unfold handoffBase
  exact rigidResidue_isBase adj

/-- **No residual symmetry at the handoff.** At `R(G)` the orbit relation is *equality*: every
`P₀`-preserving automorphism fixing the residue pointwise is the identity. This is precisely what
makes Phase 2 a rigid search — there is no symmetry left to collapse. -/
theorem orbitPartition_handoff_iff_eq (adj : AdjMatrix n) (v w : Fin n) :
    OrbitPartition adj (trivialP n) (handoffBase adj) v w ↔ v = w := by
  refine ⟨handoff_isRigid adj v w, ?_⟩
  rintro rfl
  exact OrbitPartition.refl _

/-- **The handoff is iso-invariant.** Relabelling the graph relabels its handoff base correspondingly
(`relabelAdj σ adj` is an isomorphic copy of `adj`). So Phase 2's input is a well-defined function of
the isomorphism class — the basis for making a rigid canonizer iso-invariant. -/
theorem handoffBase_relabel (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    handoffBase (relabelAdj σ adj) = (handoffBase adj).image σ := by
  unfold handoffBase
  exact rigidResidue_relabel σ adj

/-! ## The Phase-2 rigid-canonizer contract

A **Phase-2 solver** consumes a graph whose RRU residue is rigid (`handoff_isRigid`) and returns a
canonical labelled adjacency, or flags (`none`) an IR-stickiness residue it cannot certify. The two
predicates below are what a solver must satisfy for the composed canonizer to be correct; Algorithm R
is their future witness. They are stated in the `labelledAdj` / `relabelAdj` shapes so they compose
directly with the `Publication` obligations (①a soundness, ①b/①c iso-invariance). -/

/-- A candidate Phase-2 rigid canonizer: a canonical labelled adjacency, or an honest flag (`none`). -/
def Solver (n : ℕ) : Type := AdjMatrix n → Option (Fin n → Fin n → Nat)

/-- **Soundness.** Any answer is a genuine relabelling of the input — so equal answers ⟹ isomorphic
inputs. This is `Publication` ①a specialised to the rigid residue. -/
def Sound (sol : Solver n) : Prop :=
  ∀ (adj : AdjMatrix n) (c : Fin n → Fin n → Nat),
    sol adj = some c → ∃ π : Equiv.Perm (Fin n), c = labelledAdj π adj

/-- **Iso-invariance.** Relabelling the input leaves the answer unchanged — a canonical form, so
isomorphic inputs get equal forms and flag together. This is `Publication` ①b/①c specialised to the
rigid residue; the handoff-side ingredient it builds on is `handoffBase_relabel`. -/
def IsoInvariant (sol : Solver n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n), sol (relabelAdj σ adj) = sol adj

end Phase2
end ChainDescent
