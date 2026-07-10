import ChainDescent.Cascade

/-!
# The Phase-1 → Phase-2 seam — RRU handoff + rigid-residue interface

This module carries **both sides of the phase boundary**: the `RRU` namespace (the Phase-1 deliverable
— "Reaches Rigid Unconditionally", stated as a reduction to named obligations) and the `Phase2`
namespace (the rigid solver's input object + correctness contract). They meet at `rigidResidue adj` =
`R(G)`, the object `canonForm? = phase2 ∘ phase1` factors through.

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

/-! ## RRU — Reaches Rigid Unconditionally (the Phase-1 deliverable, skeleton)

The Phase-1 half of the endgame, as the proposed central object: `canonForm? = phase2 ∘ phase1`, with
`phase1` the deferral descent that consumes symmetry and stops at the rigid residue `R(G)`. The three
RRU guarantees — **reaches rigid** (nothing non-`IsBase` remains for Phase 1; the ③-side), **poly / no
Phase-1 flag** (②-side), **iso-invariant** (①b/①c-side) — are stated here and **reduced to two named
obligations**, mirroring how the confinement capstones reduce to citations. The statements are
axiom-clean NOW: they are the *reduction*, not the discharge.

  · `ComputesResidue p1` — the deferral descent's handoff base **is** the iso-invariant `rigidResidue`.
    THE open recovery/confinement content (`movedSet_eq_nonsingletonCells_of_recoverable` is its
    recoverable-node half; the intended `phase1` = "individualize the visible support"). Note
    `rigidResidue adj = Phase2.handoffBase adj`, so `RRU.reachesRigid` ≡ `Phase2.handoff_isRigid` and
    `RRU.isoInvariant` ≡ `Phase2.handoffBase_relabel` — the two sides of the seam are the same facts.
  · `Poly p1 cost` — the descent reaches the handoff within a polynomial node budget (witness:
    `Spine.defaultSpineChain_reaches_leaf` ≤ n; per-node work: `CanonForm.descentCost_le` ≤ n⁴).

**NEXT (separate brick):** discharge `ComputesResidue` for a concrete `phase1` (the recovery theorem),
and factor `canonForm? = phase2 ∘ phase1`. -/

namespace RRU

variable {n : ℕ}

/-- A **Phase-1 canonizer**: maps a graph to the base its deferral descent reaches — the rigid residue
it hands to Phase 2. (Data-only skeleton; a concrete `phase1` is the next brick.) -/
abbrev Phase1 (n : ℕ) : Type := AdjMatrix n → Finset (Fin n)

/-- **The Phase-1 recovery obligation** — the ONE open input RRU-correctness reduces to: the deferral
descent's handoff base is the iso-invariant rigid residue `R(G) = rigidResidue adj`. The refinement-
recovery content (gated on confinement); `movedSet_eq_nonsingletonCells_of_recoverable` is its
recoverable-node half. -/
def ComputesResidue (p1 : Phase1 n) : Prop := ∀ adj : AdjMatrix n, p1 adj = rigidResidue adj

/-- **The Phase-1 cost obligation**: the descent reaches the handoff within a polynomial node budget
(`cost` is the phase-1 descent's cost function). Witness: `defaultSpineChain_reaches_leaf` (≤ n
levels). -/
def Poly (cost : AdjMatrix n → ℕ) : Prop := ∀ adj : AdjMatrix n, cost adj ≤ n

/-- **RRU — reaches rigid (the ③-side: nothing non-`IsBase` remains after Phase 1).** Reduces to
`ComputesResidue` + `rigidResidue_isBase`. -/
theorem reachesRigid (p1 : Phase1 n) (h : ComputesResidue p1) (adj : AdjMatrix n) :
    IsBase adj (fun _ _ => POE.unknown) (p1 adj) := by
  rw [h adj]; exact rigidResidue_isBase adj

/-- **RRU — iso-invariant (the ①b/①c-side).** The handoff residue transports under relabelling, so
Phase 2's input — hence the canonical form — is iso-invariant. Reduces to `ComputesResidue` +
`rigidResidue_relabel`. -/
theorem isoInvariant (p1 : Phase1 n) (h : ComputesResidue p1) (σ : Equiv.Perm (Fin n))
    (adj : AdjMatrix n) : p1 (relabelAdj σ adj) = (p1 adj).image σ := by
  rw [h (relabelAdj σ adj), h adj]; exact rigidResidue_relabel σ adj

/-- **RRU — Reaches Rigid Unconditionally (the Phase-1 deliverable).** Given the recovery obligation
(`ComputesResidue`) and the cost obligation (`Poly`), Phase 1 on EVERY input reaches a rigid
(`IsBase`) residue, within budget, iso-invariantly. The Phase-1 half of the endgame, reduced to the
two named obligations — the skeleton the discharge bricks fill in. -/
theorem rru (p1 : Phase1 n) (cost : AdjMatrix n → ℕ)
    (hrec : ComputesResidue p1) (hpoly : Poly cost) :
    (∀ adj, IsBase adj (fun _ _ => POE.unknown) (p1 adj))
      ∧ (∀ adj, cost adj ≤ n)
      ∧ (∀ (σ : Equiv.Perm (Fin n)) adj, p1 (relabelAdj σ adj) = (p1 adj).image σ) :=
  ⟨fun adj => reachesRigid p1 hrec adj, hpoly, fun σ adj => isoInvariant p1 hrec σ adj⟩

/-! ### First discharge of `ComputesResidue` — the root (single-shot) Phase-1

The first, degenerate (`k = 0`) instance of the recovery obligation: a concrete `phase1` that
individualizes the *visible support at the root* — the union of the non-singleton 1-WL cells of the
initial colouring — and the theorem that its `ComputesResidue` **reduces to the project's existing
recovery predicate** `OrbitRecoverableAt … ∅`. This establishes the reduction pattern and inhabits the
RRU interface, on the WL-dimension-1-recoverable domain.

Honest scope: `∀ adj, OrbitRecoverableAt adj P₀ ∅` is the strong WL-1 condition — it FAILS at node 4 /
CFI / multipedes (where 1-WL cells are coarser than orbits). There `phase1Root` over-approximates the
support, and the *iterative* descent (individualize–refine–repeat, with per-level recovery backed by
the confinement lemma) is required — the next brick. This root case is that story's base level. -/

open Classical in
/-- **The root Phase-1 (single-shot).** Individualize the visible support at the root: the non-singleton
1-WL cells of the initial colouring. Refinement-computable (polynomial). -/
noncomputable def phase1Root (adj : AdjMatrix n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ w, w ≠ v ∧
    warmRefine adj (fun _ _ => POE.unknown) (individualizedColouring n ∅) v =
      warmRefine adj (fun _ _ => POE.unknown) (individualizedColouring n ∅) w)

/-- **`ComputesResidue` for the root Phase-1, reduced to root recoverability.** If 1-WL at the root
recovers the automorphism orbits (`OrbitRecoverableAt adj P₀ ∅`, the WL-dimension-1 condition), the
visible support IS `R(G) = rigidResidue adj`, so `phase1Root` satisfies the RRU recovery obligation.
Via `movedSet_eq_nonsingletonCells_of_recoverable` (`rigidResidue = movedSet` at `∅`). The residual
gap (recoverability fails at CFI) is exactly where the iterative descent + confinement enter. -/
theorem computesResidue_phase1Root_of_recoverable
    (hrec : ∀ adj : AdjMatrix n, OrbitRecoverableAt adj (fun _ _ => POE.unknown) ∅) :
    ComputesResidue (phase1Root (n := n)) := by
  intro adj
  have hms : rigidResidue adj = movedSet adj (fun _ _ => POE.unknown) ∅ := by
    unfold rigidResidue forcedNode; rw [Finset.empty_union]
  rw [hms]
  ext v
  rw [mem_movedSet_iff_nonsingleton_cell_of_recoverable ∅ (hrec adj)]
  unfold phase1Root
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **Payoff (root domain): `phase1Root` reaches rigid.** Under root recoverability, the root Phase-1
always lands on a rigid (`IsBase`) residue. -/
theorem phase1Root_reachesRigid_of_recoverable
    (hrec : ∀ adj : AdjMatrix n, OrbitRecoverableAt adj (fun _ _ => POE.unknown) ∅)
    (adj : AdjMatrix n) :
    IsBase adj (fun _ _ => POE.unknown) (phase1Root adj) :=
  reachesRigid _ (computesResidue_phase1Root_of_recoverable hrec) adj

/-- **Payoff (root domain): `phase1Root` is iso-invariant.** Under root recoverability, the root
Phase-1's handoff transports under relabelling. -/
theorem phase1Root_isoInvariant_of_recoverable
    (hrec : ∀ adj : AdjMatrix n, OrbitRecoverableAt adj (fun _ _ => POE.unknown) ∅)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    phase1Root (relabelAdj σ adj) = (phase1Root adj).image σ :=
  isoInvariant _ (computesResidue_phase1Root_of_recoverable hrec) σ adj

end RRU
end ChainDescent
