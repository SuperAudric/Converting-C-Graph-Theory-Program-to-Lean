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

## ★★★ THE "TWIN REFINEMENT" IS `pairStep` — the fork is closed (2026-08-06)

The user's mechanism is a modification of the **1-WL**, not of the selector: two branches are two
colourings of the same vertex set, a vertex's *twin* is the vertex of the same index in the other
branch, and whether a vertex's twin followed it into a new cell is a structural signal that — unlike
intersecting two *stable* colourings — **propagates** to neighbours. Write

* `TWIN` = 1-WL run on the joint colouring `v ↦ (χ_a v, χ_b v)` (the mechanism),
* `BOTH` = refine after individualizing `a` **and** `b` (i.e. `pairStep`).

**They are the same partition.** Both inclusions hold:
* `BOTH` refines `TWIN` — `BOTH`'s initial colouring refines `χ_a` and `χ_b`, hence determines the
  joint colour, and refinement is monotone in its initial colouring.
* `TWIN` refines `BOTH` — the joint colouring already refines `χ_a` and already gives `b` a unique
  colour, hence refines `indiv (χ_a) b`.

✅ **Measured 168/168** (`scratchpad/probe_twinrefine.py`): `TWIN == BOTH` on every (bad anchor,
partner) pair of `rand multipede V=12 W=8` (12/12) and `CFI cubic m=10` (156/156); **zero** cases of
`TWIN < BOTH`.

⟹ **No separate joint-colouring object is needed: `pairStep` below IS the twin refinement**, and its
power is therefore fully characterised by `probe_pairrefine`'s numbers — CFI cubic m=10 repaired
**4/4** (confirmed here by `TWIN` alone), rigid multipede `V=12 W=8` **0/4**.

### ★ `C₆` — the mechanism at its smallest, run against this file's own `pairStep`

`C₆` is 2-regular, so 1-WL merges the root into a single 6-cell. Then (measured, `#eval`):

| object | colouring | verdict |
|---|---|---|
| root `warmRefineVec` | `[0,0,0,0,0,0]` | one 6-cell — 1-WL sees nothing |
| `step C₆ · 0` | `[5,0,3,2,3,0]` | cells `{1,5}`, `{2,4}` — `chooseIdK = some 0`, **a decision is pending** |
| `pairStep C₆ · 0 2` | `[5,0,4,2,3,1]` | all six distinct — `chooseIdK = none`, **DISCRETE, zero decisions** |
| `pairStep C₆ · 0 1` | `[5,1,3,2,4,0]` | likewise discrete |

★ **So `pairStep` is strictly stronger than `step` here**, and by the largest possible margin: the
descent from a single anchor must branch, the pair descent has *no* decision to make.

★ The shared-cell reading checks out exactly: `χ₀`'s cell at `1` is `{1,5}`, `χ₁`'s cell at `0` is
`{0,2}`, `χ₂`'s cell at `1` is `{1,3}`. Adjacent roots `0,1` **share nothing** (`{1,5} ∩ {0,2} = ∅`);
distance-2 roots `0,2` **share exactly the vertex between them** (`{1,5} ∩ {1,3} = {1}`), which
individualizes a third vertex and discretizes after propagation.
⚠ But note the adjacent pair discretizes **too**, with an empty intersection — so the discretizing
power is the *joint colouring*, and "a shared vertex" is one visible symptom of it rather than the
mechanism itself.

⚠⚠ **The sense in which this is "stronger than 1-WL" is individualization DEPTH, not WL DIMENSION.**
It is 1-WL with one more individualization, so nothing that defeats bounded-individualization-plus-1-WL
falls to it — which is exactly why the rigid multipede stays at `0/4` while CFI m=10 goes to `4/4`.
⚠ The `|cell|²` figure is a *naive* schedule, not intrinsic: the twin lookup is `O(1)` per vertex on a
precomputed cell table, and only vertices that changed cell need re-examination. The real cost
question is that **`step` is not billed at all** (`certPathCost` prices `n⁴ + supplyCost` per level and
nothing for `step`) — that is the gap to close, and it is pre-existing rather than introduced here. -/

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
