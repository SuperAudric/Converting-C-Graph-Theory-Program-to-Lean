import ChainDescent.DeepenTinhofer

/-!
# Route (a), scoped — deepen's **orbit completeness**, and where `Tinhofer` is really consumed

## What this file is

A scoping module for the residual `①c` obligation (`R1`). It contains no new mathematics: it
**re-plumbs** what `DeepenTinhofer` already proves so that the open question is visible in a theorem
statement rather than buried inside a proof, and it pins the exact implication chain

> `OrbitComplete` (globally) ⟹ deepen's branch-orbit relation transports ⟹ `①c` for the **raw**
> `deepenSupply` ⟹ `R1`, hence the computable guard, hence a single executable object carrying
> `①`+`②`+`③` with Tinhofer coverage.

so that anyone attacking `R1` knows precisely which statement to attack.

## The target — "guaranteed success when possible"

`Consume.verified` already gives the failsafe half unconditionally: every emitted generator is a
genuine `IsColAut`, so `WordReach ⟹ same orbit` (`wordReach_imp_isColAut`) on **every** input. The
open half is the converse — that deepen *finds* an automorphism whenever one exists:

  `OrbitComplete adj χ` : for every branch-cell `u` and every `ρ ∈ IsColAut adj χ`,
                          deepen's verified generators connect `u` to `ρ u`.

With both halves the relation **is** the `IsColAut`-orbit relation, which is manifestly
relabelling-invariant, and `①c` follows by the conjugation argument already written for the
`Tinhofer`-conditional case.

## ★ Where `Tinhofer` is actually consumed — a per-ANCHOR condition, not a global one

`exec_recovers_cell_orbits` (`DeepenTinhofer` §2b′) already carries
`hAmen : TinhoferPath adj χ n (step adj χ r₁)` — the Schurianity of the deepening path of the **single
anchor** `r₁`. The global `Tinhofer adj χ` enters only in the wrapper
`exec_recovers_refgen_on_cell`, which instantiates it as `hAmen x hx`. §1 below exposes the
per-anchor form (`GoodAnchor`), and §2 records that `Tinhofer` is *definitionally* "every anchor is
good" — so nothing is lost or gained, only made visible.

Everything else in deepen's pipeline is already **structural** and carries no hypothesis:
`deepen_succeeds` (fuel adequacy), `deepen_discrete` (whole-graph discretization ⟹ the leaf is
discrete), `gate_of_discrete` (`K` non-empty + `allSingletonsK`). In particular, because the leaf is
discrete, `K = coupled χ leaf` is exactly the union of the **non-singleton `χ`-cells**, so every
`IsColAut adj χ` is automatically the identity off `K` — the twist's support is not a side condition.

## ⛔ What this route CANNOT deliver, and why the gap is where it is

`OrbitComplete` at `u` is delivered by `GoodAnchor u` (§3). Recovering the whole relation needs it at
every `u`, i.e. exactly `Tinhofer` — **this induction does not weaken below `Tinhofer`.** The single
failure mode is sharp and is worth stating in one sentence:

> at some level of the anchor's deepening the chosen sub-cell is not a single stabilizer-orbit, and
> then `deepen`'s lowest-index pick can diverge from every automorphism's image of the anchor's pick.

⚠ **But the measured evidence says the truth extends beyond `Tinhofer`.** The `G8` falsifier
(`DeepenSupply` doc-block) is a *partially* firing witness — so some cell on its descent is not a
single orbit and `G8` is not `Tinhofer` — yet the **all-anchors** relation there was measured stable
across five relabellings (profile `[2,2,2,2,4,4,4,4]`), where the single-anchor relation was measured
unstable. The repair that all-anchors performs is invisible to the induction below, which reasons one
anchor at a time. ⟹ the open question is not "is `Tinhofer` needed" but:

> **is deepen's all-anchors branch-cell partition equal to the exact `Aut`-orbit partition at
> partially-firing (non-`Tinhofer`) nodes?**

If yes, `OrbitComplete` is true beyond `Tinhofer` and wants a different proof (a union argument, not
a per-anchor induction). If no — the partition is strictly finer but still invariant — then the
target is not `OrbitComplete` at all but the invariance of a *partial* relation, a different and
harder theorem. That question is decidable by measurement on the four recorded partially-firing
witnesses plus the VT non-`Tinhofer` ones, and is the probe this scoping hands over.
⚠ Use an exact group computation for the reference partition: `probe_orbit_oracle` is recorded as
**wrong** (it errs by merging).

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The per-anchor condition -/

/-- **A GOOD ANCHOR** — `x`'s own canonical deepening individualizes only single-orbit cells. This is
the hypothesis `exec_recovers_cell_orbits` actually consumes; `Tinhofer` is its universal closure over
the branch cell. -/
def GoodAnchor (adj : AdjMatrix n) (χ : Colouring n) (x : Fin n) : Prop :=
  TinhoferPath adj χ n (step adj χ x)

/-- `Tinhofer` **is** "every anchor of the branch cell is good" — definitionally. Recorded so the
per-anchor form below is visibly a weakening of the wrapper, not a different statement. -/
theorem tinhofer_iff_forall_goodAnchor (adj : AdjMatrix n) (χ : Colouring n) :
    Tinhofer adj χ ↔ ∀ x ∈ Descend.branches χ, GoodAnchor adj χ x := Iff.rfl

/-! ## 2. The per-anchor recovery theorem

`exec_recovers_refgen_on_cell` with the global `Tinhofer adj χ` replaced by `GoodAnchor adj χ x`.
The proof is its proof; the only change is that `hAmen x hx` becomes the hypothesis itself. -/

/-- **★★ A GOOD ANCHOR RECOVERS ITS WHOLE ORBIT.** For `x` in the branch cell whose own deepening
path is Schurian, deepen's verified generators connect `x` to `ρ x` for **every** colour-automorphism
`ρ` — no condition on any other anchor, and none on the rest of the graph. -/
theorem exec_recovers_refgen_at (adj : AdjMatrix n) (χ : Colouring n)
    {ρ : Equiv.Perm (Fin n)} (hρaut : IsColAut adj χ ρ)
    {x : Fin n} (hx : x ∈ Descend.branches χ) (hgood : GoodAnchor adj χ x) :
    Consume.WordReach (Consume.verified deepenSupply adj χ) x (ρ x) := by
  by_cases hfix : ρ x = x
  · rw [hfix]; exact Consume.WordReach.refl x
  · have hρx : ρ x ∈ Descend.branches χ := isColAut_mem_branches hρaut hx
    have hne : (ρ x == x) = false := by rw [beq_eq_false_iff_ne]; exact hfix
    obtain ⟨c, hc, hxc⟩ := Consume.exists_targetColour_of_mem hx
    have hρxc : χ (ρ x) = c := by
      obtain ⟨c', hc', hρxc'⟩ := Consume.exists_targetColour_of_mem hρx
      rw [hc'] at hc; cases hc; exact hρxc'
    have hxeq : χ x = χ (ρ x) := by rw [hxc, hρxc]
    obtain ⟨d1, seq, hd⟩ := deepen_succeeds adj χ x
    have hDisc : Discrete d1.col := deepen_discrete adj χ n (step adj χ x) [] d1 seq hd
    have hg : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false :=
      gate_of_discrete hxeq (fun h => hfix h.symm) hDisc
    exact exec_recovers_cell_orbits adj χ hx hρx hne hρaut rfl hd hg hgood hDisc

/-- The branch-orbit characterization **at one good anchor**: soundness is unconditional, and
completeness at `u` needs only `u`'s own path. -/
theorem branch_orbit_iff_aut_at (adj : AdjMatrix n) (χ : Colouring n)
    {u : Fin n} (hu : u ∈ Descend.branches χ) (hgood : GoodAnchor adj χ u) {w : Fin n} :
    Consume.WordReach (Consume.verified deepenSupply adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w :=
  ⟨wordReach_imp_isColAut, by rintro ⟨β, hβ, rfl⟩; exact exec_recovers_refgen_at adj χ hβ hu hgood⟩

/-! ## 3. ★ THE TARGET — orbit completeness, stated as a predicate

This is the user-facing statement *"deepen succeeds whenever success is possible"*. It is what the
failsafe `Consume.verified` check complements: verification never lets a wrong generator through, and
`OrbitComplete` would say nothing right is ever missed. -/

/-- **`OrbitComplete`** — deepen's verified generators realise the *whole* `IsColAut`-orbit relation on
the branch cell. The open half of `deepen_branch_orbit_iff_aut`; the other half
(`wordReach_imp_isColAut`) holds on every input already. -/
def OrbitComplete (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ Descend.branches χ, ∀ ρ : Equiv.Perm (Fin n), IsColAut adj χ ρ →
    Consume.WordReach (Consume.verified deepenSupply adj χ) u (ρ u)

/-- What §2 buys: `Tinhofer` ⟹ `OrbitComplete`. ⚠ This is the *only* sufficient condition this route
supplies, and it is not a weakening — see the module doc-block. -/
theorem orbitComplete_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n} (h : Tinhofer adj χ) :
    OrbitComplete adj χ :=
  fun u hu _ρ hρ => exec_recovers_refgen_at adj χ hρ hu (h u hu)

/-- Under `OrbitComplete` the relation **is** the orbit relation — the unconditional form of
`deepen_branch_orbit_iff_aut`. -/
theorem branch_orbit_iff_aut_of_orbitComplete {adj : AdjMatrix n} {χ : Colouring n}
    (h : OrbitComplete adj χ) {u : Fin n} (hu : u ∈ Descend.branches χ) {w : Fin n} :
    Consume.WordReach (Consume.verified deepenSupply adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w :=
  ⟨wordReach_imp_isColAut, by rintro ⟨β, hβ, rfl⟩; exact h u hu β hβ⟩

/-! ## 4. ★★★ THE PAYOFF CHAIN — `OrbitComplete` ⟹ transport ⟹ `①c` for the RAW supply

These mirror `deepen_branchOrbit_transport` / `deepenSupply_guarded_canonizer_direct` with `Tinhofer`
replaced by `OrbitComplete`. They are what makes §3's predicate the right thing to attack: proving it
(globally) closes `R1` outright, with no guard, no reference supply, and nothing `noncomputable`. -/

/-- **deepen's branch-orbit relation TRANSPORTS under `OrbitComplete`.** Both sides equal the
`IsColAut`-orbit relation, which conjugates (`isColAut_conj_iff`). -/
theorem branchOrbit_transport_of_orbitComplete
    (hOC : ∀ (adj : AdjMatrix n) (χ : Colouring n), OrbitComplete adj χ)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n)
    (ha : a ∈ Descend.branches χ) (_hb : b ∈ Descend.branches χ) :
    Consume.WordReach
        (Consume.verified deepenSupply (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
      ↔ Consume.WordReach (Consume.verified deepenSupply adj χ) a b := by
  have hσa : σ a ∈ Descend.branches (transportColouring σ χ) :=
    (Descend.branches_transport_perm σ χ).mem_iff.mpr (List.mem_map_of_mem ha)
  rw [branch_orbit_iff_aut_of_orbitComplete (hOC _ _) hσa,
      branch_orbit_iff_aut_of_orbitComplete (hOC _ _) ha]
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

/-- **★★★ `①c` FOR THE RAW `deepenSupply`, FROM `OrbitComplete` ALONE.** No guard, no reference
supply, nothing `noncomputable`: this is the shape `R1` was always asking for, with the whole
obligation now concentrated in §3's single predicate. -/
theorem deepenSupply_canonizer_of_orbitComplete
    (hOC : ∀ (adj : AdjMatrix n) (χ : Colouring n), OrbitComplete adj χ) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupply (n := n))))) :=
  Residue.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport
      Force.keyEquivariant_lookahead (branchOrbit_transport_of_orbitComplete hOC))

end Deepen
end ChainDescent
