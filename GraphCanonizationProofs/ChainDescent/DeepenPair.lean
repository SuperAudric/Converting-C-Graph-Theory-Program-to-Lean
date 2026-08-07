import ChainDescent.DeepenGuardComplete

/-!
# `pairStep` — the depth-2 step, and why it needs NO new interface

The user's Q2 proposal (2026-08-06) is to stop running *one* descent and replaying it cellwise on the
compared vertex, and instead couple the two compared vertices — using the pair information to reach
**finer cells** than 1-WL sees. Every variant of that proposal (see the fork in the session record)
individualizes a *second* vertex before descending. This file supplies the object they all share and
establishes that it costs nothing structurally.

## ★★ THE POINT: `pairStep` IS `step ∘ step`, SO THE WHOLE `step` INTERFACE IS INHERITED

`project_cao_is_a_2wl_design_probe_2026-07-30` records that `step` is consumed through a small lemma
interface (`step_transport` / `step_aut` / `step_isColAut` for equivariance, `step_refines` for
monotonicity, `ncol_lt_step_of_partner` for progress), and that swapping it is therefore an
*interface* swap across ~13 modules. **A depth-2 step does not even need that.** Because
`pairStep adj χ u v := step adj (step adj χ u).col v` is literally two `step`s, every interface lemma
follows by applying the existing one twice — no abstraction, no re-proof downstream, no blast radius.

That is the cheap half of the user's *"stronger than 1-WL without a polynomial time cost increase"*:
strictly finer cells (a second individualization strictly refines whenever it individualizes a
non-singleton), at one extra `step` per level.

## ⚠⚠ WHAT THIS FILE DELIBERATELY DOES NOT DO

It does **not** yet build a supply. Which supply to build is a genuine design fork the user's sketch
does not settle, and the recorded measurements bear on it hard:

* ⛔ `probe_step2.py` (S4, 2026-07-31): swapping `Deepen.step` **alone** for a 2-WL step buys
  **nothing** at the CFI m=8 witness — identical verdicts, gen counts and level counts, partitions
  identical at every level on 4/4 anchors. **"The swap that pays is the DESCENT's refiner"**, a larger
  unscoped project.
* ✅ But `scratchpad/probe_pairrefine.py` (2026-08-06) measures a *different* axis — individualization
  **depth**, not WL **dimension** — and there CFI cubic m=10 is repaired **4/4**. The rigid multipede
  `V=12 W=8` is repaired **0/4**, as every WL-flavoured mechanism is on that family.
  ⚠ That probe individualizes **both** compared vertices, which is an **upper bound** on a
  joint-colouring mechanism (the joint colouring is coarser than individualizing both).

So depth-2 is measured to buy something 2-WL-in-the-step did not. What it costs is that a good *pair*
descent computes the pair **stabilizer**, while the twist construction needs a map `a ↦ b` — the
wiring is the open design question, not the refinement.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-- **The depth-2 step**: individualize `u`, refine, individualize `v`, refine. Deliberately defined
as two `step`s so that every `step` lemma applies twice. -/
def pairStep (adj : AdjMatrix n) (χ : Colouring n) (u v : Fin n) : Refine.ColData n :=
  step adj (step adj χ u).col v

/-! ## 1. The interface, inherited -/

/-- **★ EQUIVARIANCE** — `step_transport`, twice. -/
theorem pairStep_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u v : Fin n) :
    (pairStep (relabelAdj σ adj) (transportColouring σ χ) (σ u) (σ v)).col
      = transportColouring σ ((pairStep adj χ u v).col) := by
  unfold pairStep
  rw [show (step (relabelAdj σ adj) (transportColouring σ χ) (σ u)).col
        = transportColouring σ ((step adj χ u).col) from step_transport σ adj χ u]
  exact step_transport σ adj (step adj χ u).col v

/-- **★ `Aut`-STABILITY** — the automorphism version, for spreading arguments. -/
theorem pairStep_isColAut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsColAut adj χ ρ) (u v : Fin n) :
    (pairStep adj χ (ρ u) (ρ v)).col = transportColouring ρ ((pairStep adj χ u v).col) := by
  have h := pairStep_transport ρ adj χ u v
  rwa [hρ.relabel, transportColouring_isColAut hρ] at h

/-- **★ PROGRESS, AND IT IS STRICTLY FASTER THAN `step`.** A descent only ever individualizes a
non-singleton cell, so both levels have a partner and `ncol` rises **twice** per `pairStep`. That is
`ncol_lt_step_of_partner` applied at each level — again, no new lemma. Fuel-adequacy arguments
(`tinhoferPath_fuel_lift`) consume exactly this, so a depth-2 descent needs *less* fuel, not more. -/
theorem ncol_lt_pairStep_of_partners (adj : AdjMatrix n) {χ : Colouring n} {u v : Fin n}
    (hu : ∃ w, w ≠ u ∧ χ w = χ u)
    (hv : ∃ w, w ≠ v ∧ (step adj χ u).col w = (step adj χ u).col v) :
    Descend.ncol χ + 1 < Descend.ncol (pairStep adj χ u v).col := by
  have h1 : Descend.ncol χ < Descend.ncol (step adj χ u).col := ncol_lt_step_of_partner adj hu
  have h2 : Descend.ncol (step adj χ u).col
      < Descend.ncol (step adj (step adj χ u).col v).col := ncol_lt_step_of_partner adj hv
  show Descend.ncol χ + 1 < Descend.ncol (step adj (step adj χ u).col v).col
  omega

/-- **★ MONOTONICITY** — `pairStep` refines `step`, which refines `χ`: same-colour after is
same-colour before, at both levels. So a `pairStep` cell is a **subset** of the corresponding `step`
cell, which is the whole point of the proposal (finer cells ⟹ `CellSingleOrbit` easier to satisfy). -/
theorem pairStep_refines (adj : AdjMatrix n) (χ : Colouring n) (u v : Fin n) {x y : Fin n}
    (h : (pairStep adj χ u v).col x = (pairStep adj χ u v).col y) : χ x = χ y :=
  step_refines adj χ u (step_refines adj (step adj χ u).col v h)

/-- The second individualization never *coarsens*: a `pairStep` cell sits inside a `step` cell. -/
theorem pairStep_refines_step (adj : AdjMatrix n) (χ : Colouring n) (u v : Fin n) {x y : Fin n}
    (h : (pairStep adj χ u v).col x = (pairStep adj χ u v).col y) :
    (step adj χ u).col x = (step adj χ u).col y :=
  step_refines adj (step adj χ u).col v h

end Deepen
end ChainDescent
