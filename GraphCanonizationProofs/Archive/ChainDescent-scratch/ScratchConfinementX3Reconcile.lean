/- ARCHIVED 2026-07-09 — DEAD END, not ported, not built. References modules that were
   removed/renamed during the 2026-07-09 confinement port (see Archive README). Kept as a
   failure/substrate record only. -/

/-
# ScratchConfinementX3Reconcile.lean — X3 step (ii), the confinement reconciliation (WIP, NOT in build.sh)

**Goal.** Discharge `hrec` in `ScratchConfinementX3.ifCanon_iso_invariant_of_reconcile`: for `H = π·G`, the index-free
one-step descent picks on `H` are the `π`-image of `G`'s, up to an `H`-automorphism `b`. That reconciling `b` comes
from confinement (`ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt` ⟹ `SelectedCellIsOrbit`).

**The obstacle this file clears first (ii-a).** Confinement's `SelectedCellIsOrbit` / `OrbitPartition`
(`NodeCountBridge`) are stated over **set-individualization** `warmRefine adj P (individualizedColouring n S)`, but the
one-step descent (`ConfinementX3Spine.oneStepSpineChain`) refines the **one-at-a-time** `oneStepColouring`. To invoke
confinement on the one-step descent's selected cells we need: **same one-step cell ⟹ same set-individualization cell**,
i.e. `Refines (warmRefine (oneStepColouring k)) (warmRefine (individualizedColouring (oneStepD k)))`.

This is the EASY direction (1-WL from the committed set is at least as fine as the one-at-a-time colouring): it follows
from `DescentTrace.singletons` (committed vertices are `oneStepColouring`-singletons) + the existing
`warmRefine_refines_initial` (monotonicity). The hard direction (full `samePartition`) is NOT needed for the
reconciliation — only this one implication, which turns a one-step cell coincidence into a set-individualization one.

--------------------------------------------------------------------------------------------------------------------
## ★★ SUPERSEDED (2026-07-08 later) — the CONVERGENCE/C2 handoff below is a DEAD END. READ THIS FIRST.

**Do NOT build C2/confluence.** The route is the **W-plan**: `ScratchConfinementX3Sel.lean` (W1),
`ScratchConfinementX3Recon.lean` (W3), and the colouring-generalized confinement chain (W2). Summary:
  · **W1** — equivariant `ConfinementX3Sel.selCell` (min-colour-VALUE cell) + `selCell_transport` + `selCellRep_both_in_target`.
  · **W2** — confinement's cell-selection colouring is now an abstract `χ`/`χsel` parameter (`NodeCountBridge.SelectedCellIsOrbit`
    etc.), instantiated at the descent's OWN colouring ⟹ no set-indiv/oneStep bridge needed. **This makes the ii-a lemma
    below (`oneStep_cell_refines_setIndiv`) no longer load-bearing** (kept for reference).
  · **W3** — `ConfinementX3Recon.descentPicks` (selCell-driven picks) + `reconcile_extend` (the single-`b` accumulation
    crux) → the per-level McKay induction producing `b` for `ifCanon_iso_invariant_of_reconcile`'s `hrec`.
Authoritative: [[project_confinement_lemma_2026-07-07]] SESSION UPDATE block + route-c-plan §7c "STEP (ii-b) RESOLVED".
Everything from here down is the OLD (superseded) framing — kept only as a dead-route record.

--------------------------------------------------------------------------------------------------------------------
## ii-b HANDOFF (2026-07-08) — the reconciliation was REFRAMED to CONVERGENCE. [SUPERSEDED — see banner above.]

**The reframe (user correction).** The initial plan — make the per-step target-cell *selection* iso-invariant and
reconcile the two descents step-by-step — is the WRONG shape. The correct property is iso-**convergence**, NOT
iso-invariance: **the selection need not be iso-invariant; different orders of consuming symmetry CONVERGE to the same
state once all symmetry is consumed.** `canonForm` is the *consistent output of a fixed process*, not a global lex-min
(the C# confirms this: enabling deferral CHANGES the canonical form yet each schedule is *"still a valid iso-invariant
canonical, just not the same lex-min"* — `ChainDescent.cs:158-161`). The C# selects the **lowest cell-id non-singleton
cell** ("cell ids are iso-invariant") — colour/cell-id based, not vertex-index.

**The target splits into two:**
  · **(C1) leaf → canonForm is `Aut(G)`-invariant** — leaves in one `Aut(G)`-orbit give the same canonical form.
    NEAR-DONE: `ScratchConfinementX3.labelledAdj_rankPerm_cross` + `Spine.labelledAdj_eq_of_isAut` already handle the
    automorphism relabel; needs only packaging.
  · **(C2) CONFLUENCE — the MISSING CORE PIECE.** Any two full-individualization descents (any consumption order, in
    the orbit/assume-VT regime where every selected cell is a `Stab`-orbit) reach discrete leaves in the SAME
    `Aut(G)`-orbit. Scoped to the confined/symmetric domain (rigid graphs flag in Phase 2, out of scope). Natural
    route: a **local diamond** (individualize orbit-cell `A` then `B` ≈ `B` then `A`, up to an automorphism, because
    consuming one orbit-cell preserves the other's orbit structure) → confluence → C2. Cross-graph ①b→ is then
    `C1 + C2 + π`-transport (`H = π·G`'s leaves are the π-image of `G`'s leaf-orbit).

**★ OPEN QUESTION gating C2's proof shape (asked, UNANSWERED).** Does "reach the same state" mean (a) the two leaves
are related by an `Aut(G)` element (leaf-orbit confluence, C2 as stated) — OR (b) a harvest-level reframe (read
`canonForm` off the recovered `Stab`-chain / the C# `Automorphisms` group, not off a single leaf)? Resolve this FIRST;
(a) ⟹ build the diamond/confluence lemma, (b) ⟹ reframe `canonForm` around the harvested group.

**DEAD ENDS — do NOT re-walk (all established this session):**
  · **`ifCanon_iso_invariant_of_reconcile` (single global `b`, `ScratchConfinementX3`) only covers SAME-ORDER
    consumption.** A single automorphism maps a cell to a same-colour cell, so it cannot relate two pick-lists that
    consumed cells in different orders. Kept as the same-order building block; NOT the general reconciliation.
  · **NO-GO: an equivariant *single-vertex* selector can only pick from singleton cells** (any within-block symmetry
    `σ` of the colouring has `χ∘σ⁻¹ = χ`, so equivariance forces `σ(sel χ) = sel χ` ⟹ `sel χ` singleton). So no
    single-vertex selector gives cross-graph cell-correspondence; the committed vertex inherently differs (confinement
    handles the within-cell rep). Cell/Finset selectors escape the no-go but hit canonical tie-breaking.
  · **PI-vs-equivariant tension:** no selector is both partition-invariant (needed to match confinement's
    set-individualization) and equivariant (needed for cross-graph): value-based = equivariant-not-PI, index-based =
    PI-not-equivariant. This is why per-step reconciliation via a fixed selector stalls — superseded by convergence.
  · **`CellsAreOrbits` (all cells orbits — would dissolve everything) = the WL-dim WALL for the confined residue.
    UNAVAILABLE.** Confinement gives only `SelectedCellIsOrbit` (the selected cell). ii-a bridges the CELL refinement
    one direction; the full `samePartition` confluence bridge (hard direction `Refines (warmRefine indiv) oneStepColouring`,
    via monotonicity + `warmRefine_refineStep_samePartition` idempotence + a sandwich) is deferred, needed only if C2
    routes through confinement's set-individualization cells.

**BUILT SUBSTRATE (all axiom-clean, scratch, NOT in build.sh) — inventory for the pickup:**
  · `ScratchConfinementX3.lean` — the index-free cut P1–P6 (`indivOne`/`indivStep1` + LITERAL equivariance,
    `descentColouring_transport` cross-graph, `labelledAdj_rankPerm_cross` value-lift, `ifCanon_iso_invariant_of_reconcile`
    [same-order]). ①a transfers (seed-agnostic).
  · `ScratchConfinementX3Spine.lean` — X3 step (i): `oneStepSpineChain` (the index-free `SpineChain` via `indivStepOne`
    + `pickOne`), `oneStepSpineChain_reaches_leaf` (termination TRANSFERRED from `defaultSpineChain_reaches_leaf`),
    `oneStep_canonForm_isLabelledAdj` (①a for free). NB `pickOne` here is min-vertex-index — for C2 the selector likely
    changes to cell-id/colour-based (per the C#), but the SpineChain plumbing + termination-transfer pattern reuses.
  · THIS FILE — ii-a `oneStep_cell_refines_setIndiv` (same one-step cell ⟹ same set-individualization cell).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Spine
import ChainDescent.Cascade

namespace ChainDescent.ConfinementX3Reconcile

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Spine
open ChainDescent.CanonSound

variable {n : Nat}

/-- **The one-step colouring refines the set-individualization of its committed set.**
`Refines (oneStepColouring k) (individualizedColouring (oneStepD k))`: if two vertices share an `oneStepColouring`
colour, neither is committed (committed vertices are `oneStepColouring`-singletons, `DescentTrace.singletons`), so both
lie outside `oneStepD k` and get `individualizedColouring = 0`. A seed-level refinement fact, discharged from the
trace's singleton invariant — no colour-value bookkeeping. -/
theorem oneStepColouring_refines_indiv (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (k : Nat) :
    Refines (oneStepColouring adj P₀ χι₀ k)
      (individualizedColouring n (oneStepD adj P₀ χι₀ k)) := by
  intro a b hab
  have hsing := DescentTrace.singletons (oneStepTrace adj P₀ χι₀ k)
  by_cases haD : a ∈ oneStepD adj P₀ χι₀ k
  · -- a committed ⟹ singleton ⟹ b = a
    by_cases hba : b = a
    · rw [hba]
    · exact absurd hab.symm (hsing a haD b hba)
  · by_cases hbD : b ∈ oneStepD adj P₀ χι₀ k
    · -- b committed, a not ⟹ a ≠ b ⟹ colours differ, contradicting hab
      exact absurd hab (hsing b hbD a (fun h => haD (h ▸ hbD)))
    · -- both uncommitted ⟹ both get individualizedColouring = 0
      simp only [individualizedColouring, if_neg haD, if_neg hbD]

/-- **★ ii-a — the confinement bridge: same one-step cell ⟹ same set-individualization cell.**
`Refines (warmRefine (oneStepColouring k)) (warmRefine (individualizedColouring (oneStepD k)))`. Monotonicity
(`warmRefine_refines_initial`) applied to the seed refinement above. This is the implication that lets confinement's
`SelectedCellIsOrbit`/`OrbitPartition` (set-individualization-based) speak about the index-free one-step descent's
selected cells: two vertices the one-step descent leaves in one cell are in one set-individualization cell, whence
(confinement) one `Stab`-orbit. -/
theorem oneStep_cell_refines_setIndiv (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (k : Nat) :
    Refines (warmRefine adj P₀ (oneStepColouring adj P₀ χι₀ k))
      (warmRefine adj P₀ (individualizedColouring n (oneStepD adj P₀ χι₀ k))) :=
  warmRefine_refines_initial (oneStepColouring_refines_indiv adj P₀ χι₀ k)

end ChainDescent.ConfinementX3Reconcile
