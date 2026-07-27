import ChainDescent.DeepenCertified

/-!
# Workstream C — LOCATING the rigid obstruction a consume failure exposes

**The gap this closes.** `not_amenablePath_imp_rigidObstruction` (`DeepenAmenable`) ends at
`∃ χc cid, RigidObstructionAt adj χc cid` — an obstruction *somewhere*, at an unnamed colouring, with
no statement that the colouring is one the canonizer ever visits. Force cannot act on that: `forceBy`
fires at a **node**, so it needs the obstruction to sit at the branch cell of a colouring reachable by
the descent's own individualizations.

`DeepenCertified` §4 supplies the located form, but only under `Certified`
(`rigidObstructionAt_branch_of_certified`). **That hypothesis is necessary, not an artefact** — the
unguarded statement is FALSE, and the counterexample is measured (`scratchpad/probe_orbit_oracle.py`,
scoping doc §13/§14.0): on the CFI graph over a random cubic base with `m = 8` there is a node whose
branch cell has 16 vertices forming a *single* `Aut`-orbit — so `RigidObstructionAt` at that cell is
false — while `¬ Consume.CellIsOrbit deepenSupply adj χ` nevertheless holds, because the all-anchor
harvest splits the cell 8 + 8. (An explicit verified `IsColAut σ` with `σ 24 = 26` crosses the split.)
At that node force provably cannot fire either, by `Force.forceBy_no_narrowing_on_orbit`. So no theorem
of the shape *"consume fails at `χ` ⟹ force can act at `χ`"* can hold, and the obstruction must be
relocated to a **deeper reachable node**.

That is what this file does, in two steps.

* **§2 `not_amenablePath_located` (L2)** — the obstruction is at a colouring `ψ` reachable from the
  starting state by `DescentReach`, and it is at `ψ`'s **branch cell** (`Descend.targetColour`, via the
  landed selector identity `chooseIdK_eq_targetColour`). This is a strengthening of
  `not_amenablePath_imp_rigidObstruction`: the same induction, keeping the two facts it discarded.
* **§3 `not_amenable_deepest` (L3)** — the *deepest* such failure is reached, and there the node is
  **also `Amenable`**. So one node carries both hypotheses at once: consume is exact below it (which is
  what an orbit-separating equivariant key needs, scoping doc §14.2/§14.3) and force has a genuine
  rigid decision at its branch cell. Termination is the colour-count measure `Descend.ncol`, exactly
  the one `deepen_succeeds` uses.

**What this is for.** `not_amenable_deepest` is the hook point workstream A/B build on: at `ψ` the
guarded cert key is equivariant *and* non-constant on the branch cell, so `Force.forceBy_narrows_of_key_ne`
applies. Nothing here needs a key, so this file stands alone.

**Measured shape of the located node** (scoping doc §13.5, two witnesses traced level by level): the
descent stays aligned through every single-orbit cell and breaks at the **first** cell that is not a
single stabiliser orbit — Chang-B at level 0 (a 12-cell with 4 stabiliser orbits), CFI cubic `m = 8` at
level 3 (a 4-cell with 2). `not_amenablePath_located` is the proof-side statement of that trace.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. `DescentReach` — the colourings the descent can actually stand on

A step individualizes a vertex **that has a same-colour partner** and re-refines. The partner
hypothesis is not decoration: it is what makes each step strictly raise the colour count (§3's
termination), and it is the same shape `Descend.ncol_lt_indivOne_of_partner` and `Select.NodeProper`
already carry. -/

/-- `ψ` is reachable from `χ` by a chain of *proper* descent steps (individualize a vertex with a
same-colour partner, then warm-refine). Every colouring `deepen` visits is reachable in this sense —
`chooseIdK` only ever selects a cell with at least two members (`chooseIdK_mem`). -/
inductive DescentReach (adj : AdjMatrix n) : Colouring n → Colouring n → Prop where
  | refl (χ : Colouring n) : DescentReach adj χ χ
  | cons {χ ψ : Colouring n} (v : Fin n) (hp : ∃ u, u ≠ v ∧ χ u = χ v) :
      DescentReach adj (step adj χ v).col ψ → DescentReach adj χ ψ

theorem DescentReach.trans {adj : AdjMatrix n} {χ ψ ω : Colouring n}
    (h₁ : DescentReach adj χ ψ) (h₂ : DescentReach adj ψ ω) : DescentReach adj χ ω := by
  induction h₁ with
  | refl _ => exact h₂
  | cons v hp _ ih => exact DescentReach.cons v hp (ih h₂)

/-- **One proper step strictly raises the colour count.** `indivOne` splits a non-singleton cell
(`ncol_lt_indivOne_of_partner`) and the warm refinement never merges (`ncol_le_refine`). This is the
measure `deepen_succeeds` uses, isolated so §3 can reuse it. -/
theorem ncol_lt_step_of_partner (adj : AdjMatrix n) {χ : Colouring n} {v : Fin n}
    (hp : ∃ u, u ≠ v ∧ χ u = χ v) :
    Descend.ncol χ < Descend.ncol (step adj χ v).col := by
  have h1 : Descend.ncol χ < Descend.ncol (Descend.indivOne χ v) :=
    Descend.ncol_lt_indivOne_of_partner hp
  have h2 : Descend.ncol (Descend.indivOne χ v) ≤ Descend.ncol (step adj χ v).col := by
    show _ ≤ Descend.ncol (Refine.warmRefineVec adj (Descend.indivOne χ v)).col
    rw [Refine.warmRefineVec_col_eq, ← Refine.refineV_encodeFreeFast]
    exact Descend.ncol_le_refine Refine.refineSplits_encodeFreeFast adj (Descend.indivOne χ v)
  omega

/-- Reachability never lowers the colour count. -/
theorem ncol_le_of_descentReach {adj : AdjMatrix n} {χ ψ : Colouring n}
    (h : DescentReach adj χ ψ) : Descend.ncol χ ≤ Descend.ncol ψ := by
  induction h with
  | refl _ => exact le_refl _
  | cons v hp _ ih => exact le_trans (le_of_lt (ncol_lt_step_of_partner adj hp)) ih

/-- A `deepen` level's chosen cell has a second member, so the pick `w` has a partner — the hypothesis
`DescentReach.cons` needs. Extracted from `chooseIdK_mem` the way `deepen_succeeds` does it. -/
theorem partner_of_chooseIdK {χ : Colouring n} {cid : Nat} {w : Fin n} {rest : List (Fin n)}
    (hco : chooseIdK (List.finRange n) χ = some cid)
    (hcell : cidCell χ cid = w :: rest) :
    ∃ u, u ≠ w ∧ χ u = χ w := by
  have hlen : 2 ≤ (cidCell χ cid).length := chooseIdK_mem _ _ hco
  have hwcid : χ w = cid := by
    have : w ∈ cidCell χ cid := by rw [hcell]; exact List.mem_cons_self ..
    exact (mem_cidCell_iff _ _ _).mp this
  -- a second member of the cell
  obtain ⟨u, rest', hrest⟩ : ∃ u rest', rest = u :: rest' := by
    rw [hcell] at hlen
    cases rest with
    | nil => simp at hlen
    | cons u rest' => exact ⟨u, rest', rfl⟩
  have hucid : χ u = cid := by
    have : u ∈ cidCell χ cid := by rw [hcell, hrest]; simp
    exact (mem_cidCell_iff _ _ _).mp this
  have hnd : (cidCell χ cid).Nodup := cidCell_nodup χ cid
  rw [hcell, hrest] at hnd
  simp only [List.nodup_cons, List.mem_cons] at hnd
  exact ⟨u, fun heq => hnd.1 (Or.inl heq.symm), by rw [hucid, hwcid]⟩

/-! ## 2. L2 — the obstruction is at a REACHABLE node's BRANCH CELL

`not_amenablePath_imp_rigidObstruction` walks the path to the first level whose cell is not a single
orbit and returns `⟨cur.col, cid, …⟩`. It then throws away (a) that `cur.col` is reachable and (b) that
`cid` is the *branch* colour there. Both are already in hand at that point; this keeps them. -/

/-- **★★ L2 — LOCATED FAILURE.** A non-`AmenablePath` state exposes a rigid obstruction at the **branch
cell** of a colouring the descent can **reach** from it. Compare
`not_amenablePath_imp_rigidObstruction`, whose `∃ χc cid` names no reachable node and no branch cell. -/
theorem not_amenablePath_located (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), ¬ AmenablePath adj χp fuel cur →
      ∃ ψ : Colouring n, DescentReach adj cur.col ψ ∧
        ∃ cid : Nat, Descend.targetColour ψ = some cid ∧ RigidObstructionAt adj ψ cid := by
  intro fuel
  induction fuel with
  | zero => intro cur h; exact absurd trivial h
  | succ fuel ih =>
      intro cur h
      unfold AmenablePath at h
      dsimp only at h
      -- `chooseIdK` decides the level; `none` means the path already ended (vacuously amenable).
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => rw [hco] at h; exact absurd trivial h
      | some cid =>
          rw [hco] at h
          dsimp only at h
          rw [not_and_or] at h
          rcases h with hcso | htail
          · -- THE FAILING LEVEL IS HERE: stay put, and name the cell as the branch cell (T3).
            refine ⟨cur.col, DescentReach.refl _, cid, ?_, ?_⟩
            · rw [← chooseIdK_eq_targetColour]; exact hco
            · exact rigidObstruction_of_not_cellSingleOrbit adj cur.col cid hcso
          · -- the level is fine; recurse into the tail and prepend this step
            cases hcell : cidCell cur.col cid with
            | nil =>
                exfalso
                have hlen : 2 ≤ (cidCell cur.col cid).length := chooseIdK_mem _ _ hco
                rw [hcell] at hlen; simp at hlen
            | cons w rest =>
                have hfl : (List.finRange n).filter (fun v => cur.col v == cid) = w :: rest := hcell
                rw [hfl] at htail
                dsimp only at htail
                obtain ⟨ψ, hreach, cid', hct, hrig⟩ := ih (step adj cur.col w) htail
                exact ⟨ψ, DescentReach.cons w (partner_of_chooseIdK hco hcell) hreach,
                       cid', hct, hrig⟩

/-! ## 3. L3 — the DEEPEST failure: one node carrying BOTH hypotheses

L2 gives a reachable obstructed node, but says nothing about the descent *below* it — and a key that
separates the cell's orbits needs exactly that (`Amenable` at the node). Iterating L2 fixes this: keep
descending while the located node is itself non-`Amenable`. The colour count strictly rises at every
step and is bounded by `n`, so the iteration stops, and it can only stop at a node that **is**
`Amenable` — while still carrying the obstruction L2 put at its branch cell. -/

/-- Fuelled form (the induction). `k` bounds the remaining colour deficit `n - ncol χ`. -/
theorem not_amenable_deepest_aux (adj : AdjMatrix n) :
    ∀ (k : Nat) (χ : Colouring n), n - Descend.ncol χ ≤ k → ¬ Amenable adj χ →
      ∃ ψ : Colouring n, DescentReach adj χ ψ ∧ Amenable adj ψ ∧
        ∃ cid : Nat, Descend.targetColour ψ = some cid ∧ RigidObstructionAt adj ψ cid := by
  intro k
  induction k with
  | zero =>
      -- `¬Amenable` produces a branch vertex, hence a partner, hence `ncol χ < n`: the deficit is ≥ 1.
      intro χ hk hnA
      exfalso
      unfold Amenable at hnA
      push Not at hnA
      obtain ⟨r, hr, _⟩ := hnA
      have hlt : Descend.ncol χ < Descend.ncol (step adj χ r).col :=
        ncol_lt_step_of_partner adj (Descend.exists_partner_of_mem_branches hr)
      have hle : Descend.ncol (step adj χ r).col ≤ n := Descend.ncol_le _
      omega
  | succ k ih =>
      intro χ hk hnA
      unfold Amenable at hnA
      push Not at hnA
      obtain ⟨r, hr, hpath⟩ := hnA
      -- L2 at the failing anchor, then prepend the anchor's own step
      obtain ⟨ψ₀, hreach₀, cid, hct, hrig⟩ := not_amenablePath_located adj χ n (step adj χ r) hpath
      have hstep : DescentReach adj χ ψ₀ :=
        DescentReach.cons r (Descend.exists_partner_of_mem_branches hr) hreach₀
      by_cases hA : Amenable adj ψ₀
      · exact ⟨ψ₀, hstep, hA, cid, hct, hrig⟩
      · -- strictly deeper, so the deficit dropped: recurse
        have h1 : Descend.ncol χ < Descend.ncol (step adj χ r).col :=
          ncol_lt_step_of_partner adj (Descend.exists_partner_of_mem_branches hr)
        have h2 : Descend.ncol (step adj χ r).col ≤ Descend.ncol ψ₀ :=
          ncol_le_of_descentReach hreach₀
        have h3 : Descend.ncol ψ₀ ≤ n := Descend.ncol_le _
        obtain ⟨ψ, hreach, hA', hobs⟩ := ih ψ₀ (by omega) hA
        exact ⟨ψ, hstep.trans hreach, hA', hobs⟩

/-- **★★★ L3 — THE HOOK POINT.** If the deepening is not `Amenable` at `χ`, then the descent reaches a
colouring `ψ` at which

* **consume is exact below** — `Amenable adj ψ`, so the harvest's branch-orbit relation *is* the
  `IsColAut`-orbit relation there (`deepen_branch_orbit_iff_aut`), and an orbit-separating equivariant
  key is available (scoping doc §14.2); and
* **force has a real decision** — `RigidObstructionAt adj ψ cid` at `ψ`'s own **branch cell**
  (`Descend.targetColour ψ = some cid`), so the cell carries ≥ 2 orbits and
  `Force.forceBy_no_narrowing_on_orbit`'s ceiling does not block firing.

Both resolvers' hypotheses hold at the **same, named, reachable** node. This is the statement
`not_amenablePath_imp_rigidObstruction` was reaching for; note §14.0 — it cannot be improved to "at `χ`
itself", since that is refuted by a measured witness. -/
theorem not_amenable_deepest (adj : AdjMatrix n) {χ : Colouring n} (h : ¬ Amenable adj χ) :
    ∃ ψ : Colouring n, DescentReach adj χ ψ ∧ Amenable adj ψ ∧
      ∃ cid : Nat, Descend.targetColour ψ = some cid ∧ RigidObstructionAt adj ψ cid :=
  not_amenable_deepest_aux adj (n - Descend.ncol χ) χ (le_refl _) h

/-- The `Amenable` form of `consume_fail_gives_real_decision`. `DeepenCertified` states it over
`Certified`, which is *strictly stronger* (`amenable_of_certified` goes only one way); the underlying
exactness theorem `deepen_branch_orbit_iff_aut` already takes `Amenable`, so nothing is lost. -/
theorem consume_fail_real_decision_of_amenable {adj : AdjMatrix n} {χ : Colouring n}
    (hA : Amenable adj χ) (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    ∃ u ∈ Descend.branches χ, ∃ w ∈ Descend.branches χ,
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w := by
  by_contra hcon
  push Not at hcon
  refine hfail (fun u hu w hw => ?_)
  obtain ⟨σ, hσ, hσu⟩ := hcon u hu w hw
  exact (deepen_branch_orbit_iff_aut adj χ hA hu).mpr ⟨σ, hσ, hσu⟩

/-- The same, as a `RigidObstructionAt` at the branch cell. -/
theorem rigidObstructionAt_branch_of_amenable {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c) (hA : Amenable adj χ)
    (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    RigidObstructionAt adj χ c := by
  obtain ⟨u, hu, w, hw, hrig⟩ := consume_fail_real_decision_of_amenable hA hfail
  exact ⟨u, w, (Descend.mem_branches_iff hc u).mp hu, (Descend.mem_branches_iff hc w).mp hw, hrig⟩

/-- **★★★ THE CONSUME-SIDE ENTRY POINT — every consume failure is LOCATED.** Either the node is
`Amenable`, and then the failure is a rigid decision in **this** branch cell; or it is not, and then a
reachable deeper node carries *both* hypotheses (`not_amenable_deepest`). Neither disjunct is an
unanchored existential, which is the whole improvement over
`not_amenablePath_imp_rigidObstruction`. -/
theorem consume_fail_locates (adj : AdjMatrix n) {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c)
    (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    RigidObstructionAt adj χ c ∨
      ∃ ψ : Colouring n, DescentReach adj χ ψ ∧ Amenable adj ψ ∧
        ∃ cid : Nat, Descend.targetColour ψ = some cid ∧ RigidObstructionAt adj ψ cid := by
  by_cases hA : Amenable adj χ
  · exact Or.inl (rigidObstructionAt_branch_of_amenable hc hA hfail)
  · exact Or.inr (not_amenable_deepest adj hA)

end Deepen
end ChainDescent
