import ChainDescent.DeepenGuard
import ChainDescent.DeepenComplete

/-!
# ★★★ THE POLY GUARD IS **EXACTLY** `Tinhofer` — `Tinhofer ↔ CertifiedG deepenSupply`

`DeepenGuard` §3 proves the guard SOUND (`tinhofer_of_certifiedG`: the checked cell-orbit certificate
implies the real single-orbit condition). This file proves the **converse**, for `deepenSupply`
specifically, and with it the transport that `DeepenGuard` §4 could only get from
`SupplyEquivariant` — a hypothesis `deepenSupply` provably lacks.

## ⛔⛔ THIS REFUTES `DeepenCertified` §7's RECORDED BLOCKER (2026-08-04). Read that note, then this.

§7 says, verbatim:

> `CertPath` walks **one** `chooseIdK`/`finRange`-head path, but each of its levels demands
> `CellIsOrbit deepenSupply adj ψ` — deepen connecting *every pair* of ψ's branch cell.
> `exec_recovers_refgen_on_cell` supplies one pair from `hAmen x hx`, i.e. **one anchor's path**, so a
> level needs `TinhoferPath` from **every** anchor of ψ = the full `Tinhofer adj ψ`. Path-local
> `Tinhofer adj χ` says nothing about a *deeper* ψ's other anchors ⟹
> **`Tinhofer adj χ → CertifiedG deepenSupply adj χ` is not available**.

**The last implication is false.** Path-local `Tinhofer` says a great deal about ψ's other anchors,
because the level *immediately above* ψ asserts `CellSingleOrbit adj ψ.parent cid` — and by
`DeepenComplete.goodAnchor_transport` goodness is an **orbit property**. So the single path the
certificate walks reaches one anchor of the cell, and the cell being one orbit spreads that anchor's
whole path to **every** member of the cell. "One anchor's path" and "every anchor's path" coincide
exactly where `TinhoferPath` holds, which is exactly where they are needed.

`goodAnchor_transport` was landed 2026-08-04, *after* §7's note was written; §7 is provenance, and its
⛔ bullet is superseded by `certifiedG_of_tinhofer` below. The CLOSURE-hypothesis version
(`RestrictedTransport.certifiedG_deepenSupply_of_tinhoferGraph`) is subsumed: no `TinhoferGraph`.

## The chain (§ numbers below)

1. **§1 fuel adequacy** — `TinhoferPath` at fuel `f` lifts to *any* fuel once `n ≤ f + ncol cur.col`.
   The invariant is self-maintaining: it holds at the root (`f = n`) and each level trades one fuel for
   one strictly-larger `ncol` (`ncol_lt_step_of_partner`). This is what lets a depth-`d` tail, which
   carries fuel `n - d`, be re-read as the fuel-`n` `GoodAnchor` that `deepen` actually runs.
2. **§2 spreading** — `CellSingleOrbit adj ψ cid` moves a `TinhoferPath` from one cell member to any
   other. `goodAnchor_transport` at general fuel.
3. **§3 path-local ⟹ all-anchors** — §1 + §2 give `Tinhofer adj cur.col` from `TinhoferPath` at
   `cur`. **This is the step §7 declared unavailable.**
4. **§4** — `Tinhofer adj ψ` + `CellSingleOrbit` ⟹ `CellIsOrbit deepenSupply adj ψ`, via
   `DeepenComplete.orbitComplete_of_tinhofer`.
5. **§5** — the induction: `TinhoferPath ⟹ CertPath deepenSupply`, hence
   `Tinhofer ↔ CertifiedG deepenSupply`.
6. **§6** — `CertifiedG deepenSupply` **transports**, with no `SupplyEquivariant`: route the transport
   through `Tinhofer`, which is already known invariant (`tinhofer_transport_iff`).
7. **§7** — the payoff: `deepenSupplyCert`, a **computable** supply whose guard is the `Tinhofer`
   guard, and `①` for it with **no hypothesis** — `deepenSupplyGuarded_canonizer` transferred along a
   definitional equality. `DeepenCertified`'s "`deepenSupplyGuarded` … is `noncomputable` by
   construction. Making it executable is `R1`, not a wiring step" is thereby answered: it *is* a
   wiring step, once the guard is known complete.

## What this does NOT give

`OrbitComplete` globally (= `R1`) is still open, and this file does not touch it. What it gives is
that the *guard* costs nothing in coverage: it is open on precisely the `Tinhofer` nodes, so the
residue of the guarded object is exactly `¬ Tinhofer` and not something weaker.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut Supply verified CellIsOrbit WordReach)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 0. `TinhoferPath` equation lemmas

The `CertPath` recipe (`DeepenGuard` §5): reduce only through these, never by unfolding in place and
then `cases`-ing on `chooseIdK`, which descends into its internal `foldl`. -/

theorem tinhoferPath_none {adj : AdjMatrix n} {χp : Colouring n} {fuel : Nat}
    {cur : Refine.ColData n} (h : chooseIdK (List.finRange n) cur.col = none) :
    TinhoferPath adj χp (fuel + 1) cur ↔ True := by
  simp only [TinhoferPath, h]

theorem tinhoferPath_cons {adj : AdjMatrix n} {χp : Colouring n} {fuel : Nat}
    {cur : Refine.ColData n} {cid : Nat} {w : Fin n} {rest : List (Fin n)}
    (h : chooseIdK (List.finRange n) cur.col = some cid)
    (hf : (List.finRange n).filter (fun v => cur.col v == cid) = w :: rest) :
    TinhoferPath adj χp (fuel + 1) cur ↔
      (CellSingleOrbit adj cur.col cid ∧ TinhoferPath adj χp fuel (step adj cur.col w)) := by
  simp only [TinhoferPath, h, hf]

/-- A level that selects a cell always finds it non-empty (`chooseIdK` only names cells of size ≥ 2). -/
theorem cidCell_ne_nil {χ : Colouring n} {cid : Nat}
    (hco : chooseIdK (List.finRange n) χ = some cid) :
    ∃ w rest, (List.finRange n).filter (fun v => χ v == cid) = w :: rest := by
  have hlen : 2 ≤ (cidCell χ cid).length := chooseIdK_mem _ _ hco
  cases hc : (List.finRange n).filter (fun v => χ v == cid) with
  | nil =>
      exfalso
      have hnil : cidCell χ cid = [] := hc
      rw [hnil] at hlen; simp at hlen
  | cons a l => exact ⟨a, l, rfl⟩

/-! ## 1. Fuel adequacy — a tail's fuel is as good as `n`

`TinhoferPath`'s fuel is a *bound* on the levels still to come, and once the colour deficit is covered
the recursion has already bottomed out at `chooseIdK = none`. So below the deficit the fuel is
irrelevant and any two fuels agree. -/

/-- A discrete colouring has no non-singleton cell for `chooseIdK` to name. The converse of
`discrete_of_chooseIdK_none`. -/
theorem chooseIdK_none_of_discrete {χ : Colouring n} (h : Discrete χ) :
    chooseIdK (List.finRange n) χ = none := by
  cases hco : chooseIdK (List.finRange n) χ with
  | none => rfl
  | some cid =>
      exfalso
      obtain ⟨w, rest, hcell⟩ := cidCell_ne_nil hco
      obtain ⟨u, hu, huw⟩ := partner_of_chooseIdK hco hcell
      exact hu (h u w huw)

/-- **★ FUEL ADEQUACY.** Once `fuel` covers the colour deficit `n - ncol cur.col`, `TinhoferPath` at
that fuel gives it at **every** fuel. The measure is `deepen_isSome`'s and `leafOf_discrete`'s. -/
theorem tinhoferPath_fuel_lift (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), n ≤ fuel + Descend.ncol cur.col →
      TinhoferPath adj χp fuel cur → ∀ m : Nat, TinhoferPath adj χp m cur := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur hmeas _ m
      have hd : Discrete cur.col :=
        Descend.discrete_of_ncol_eq (le_antisymm (Descend.ncol_le _) (by omega))
      cases m with
      | zero => trivial
      | succ m => rw [tinhoferPath_none (chooseIdK_none_of_discrete hd)]; trivial
  | succ fuel ih =>
      intro cur hmeas hT m
      cases m with
      | zero => trivial
      | succ m =>
          cases hco : chooseIdK (List.finRange n) cur.col with
          | none => rw [tinhoferPath_none hco]; trivial
          | some cid =>
              obtain ⟨w, rest, hfl⟩ := cidCell_ne_nil hco
              rw [tinhoferPath_cons hco hfl] at hT
              rw [tinhoferPath_cons hco hfl]
              refine ⟨hT.1, ih (step adj cur.col w) ?_ hT.2 m⟩
              have hlt := ncol_lt_step_of_partner adj (partner_of_chooseIdK hco hfl)
              omega

/-! ## 2. Spreading — goodness is an ORBIT property, at every fuel

`DeepenComplete.goodAnchor_transport` with the fuel left free. This is the ingredient §7's note
predates. -/

/-- **★★ A `TinhoferPath` SPREADS ACROSS A SINGLE-ORBIT CELL.** If the cell is one orbit of
`IsColAut adj ψ`, the path from one member is the path from every member — the stabilizer element
carrying `w` to `x` relabels the whole descent and fixes `(adj, ψ)`. -/
theorem tinhoferPath_spread (adj : AdjMatrix n) (χp χq : Colouring n) {ψ : Colouring n} {cid : Nat}
    (hso : CellSingleOrbit adj ψ cid) {w x : Fin n} (hw : ψ w = cid) (hx : ψ x = cid)
    {fuel : Nat} (h : TinhoferPath adj χp fuel (step adj ψ w)) :
    TinhoferPath adj χq fuel (step adj ψ x) := by
  obtain ⟨ρ, hρ, hρw⟩ := hso w x hw hx
  have hrel : (step adj ψ x).col = transportColouring ρ ((step adj ψ w).col) := by
    have hs := step_isColAut hρ ψ w
    rw [transportColouring_isColAut hρ, hρw] at hs
    exact hs
  have ht := tinhoferPath_transport adj χp χq fuel (step adj ψ w) (step adj ψ x) ρ hrel h
  rwa [hρ.relabel] at ht

/-! ## 3. ★★★ PATH-LOCAL ⟹ ALL-ANCHORS — the step `DeepenCertified` §7 declared unavailable -/

/-- **★★★ A `TinhoferPath` AT A NODE GIVES THE FULL `Tinhofer` AT THAT NODE.** The level asserts its
own cell is a single orbit (`CellSingleOrbit`), and `chooseIdK`'s cell **is** `Descend.branches`'
cell (`chooseIdK_eq_targetColour`); so §2 spreads the single recorded tail to every anchor and §1
restores the fuel `Tinhofer` asks for. -/
theorem tinhofer_of_tinhoferPath (adj : AdjMatrix n) (χp : Colouring n) {fuel : Nat}
    {cur : Refine.ColData n} (hmeas : n ≤ (fuel + 1) + Descend.ncol cur.col)
    {cid : Nat} (hco : chooseIdK (List.finRange n) cur.col = some cid)
    (h : TinhoferPath adj χp (fuel + 1) cur) :
    Tinhofer adj cur.col := by
  have htc : Descend.targetColour cur.col = some cid := by
    rw [← chooseIdK_eq_targetColour]; exact hco
  obtain ⟨w, rest, hfl⟩ := cidCell_ne_nil hco
  rw [tinhoferPath_cons hco hfl] at h
  obtain ⟨hso, htail⟩ := h
  have hwcid : cur.col w = cid := by
    have hwm : w ∈ cidCell cur.col cid := by rw [show cidCell cur.col cid = w :: rest from hfl]; simp
    exact (mem_cidCell_iff _ _ _).mp hwm
  intro r hr
  have hrcid : cur.col r = cid := (Descend.mem_branches_iff htc r).mp hr
  have hspread : TinhoferPath adj cur.col fuel (step adj cur.col r) :=
    tinhoferPath_spread adj χp cur.col hso hwcid hrcid htail
  refine tinhoferPath_fuel_lift adj cur.col fuel (step adj cur.col r) ?_ hspread n
  have hlt := ncol_lt_step_of_partner adj (Descend.exists_partner_of_mem_branches hr)
  omega

/-! ## 4. `Tinhofer` at a node makes deepen certify that node's cell -/

/-- `Tinhofer adj ψ` ⟹ deepen recovers every orbit (`orbitComplete_of_tinhofer`); with the cell a
single orbit, that is exactly `CellIsOrbit`. -/
theorem cellIsOrbit_deepenSupply_of_tinhofer {adj : AdjMatrix n} {ψ : Colouring n} {cid : Nat}
    (htc : Descend.targetColour ψ = some cid) (hso : CellSingleOrbit adj ψ cid)
    (hT : Tinhofer adj ψ) :
    CellIsOrbit deepenSupply adj ψ := by
  intro u hu w hw
  have hu' : ψ u = cid := (Descend.mem_branches_iff htc u).mp hu
  have hw' : ψ w = cid := (Descend.mem_branches_iff htc w).mp hw
  obtain ⟨ρ, hρ, hρuw⟩ := hso u w hu' hw'
  have hreach := orbitComplete_of_tinhofer hT u hu ρ hρ
  rwa [hρuw] at hreach

/-! ## 5. ★★★ COMPLETENESS OF THE GUARD -/

/-- **★★★ `TinhoferPath` ⟹ `CertPath deepenSupply`.** The converse of `tinhoferPath_of_certPath`,
for the deepen supply. Each level's `CellIsOrbit` obligation is discharged by §4 from the `Tinhofer`
that §3 extracts from the level itself. -/
theorem certPath_of_tinhoferPath (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), n ≤ fuel + Descend.ncol cur.col →
      TinhoferPath adj χp fuel cur → CertPath deepenSupply adj fuel cur := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; trivial
  | succ fuel ih =>
      intro cur hmeas hT
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => rw [certPath_none hco]; trivial
      | some cid =>
          have htc : Descend.targetColour cur.col = some cid := by
            rw [← chooseIdK_eq_targetColour]; exact hco
          obtain ⟨w, rest, hfl⟩ := cidCell_ne_nil hco
          have hTnode : Tinhofer adj cur.col := tinhofer_of_tinhoferPath adj χp hmeas hco hT
          rw [tinhoferPath_cons hco hfl] at hT
          obtain ⟨hso, htail⟩ := hT
          rw [certPath_cons hco hfl]
          refine ⟨cellIsOrbit_deepenSupply_of_tinhofer htc hso hTnode, ?_⟩
          refine ih (step adj cur.col w) ?_ htail
          have hlt := ncol_lt_step_of_partner adj (partner_of_chooseIdK hco hfl)
          omega

/-- **★★★ THE GUARD IS COMPLETE.** Where `Tinhofer` holds, deepen's own poly certificate is open. -/
theorem certifiedG_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n} (h : Tinhofer adj χ) :
    CertifiedG deepenSupply adj χ := fun r hr =>
  certPath_of_tinhoferPath adj χ n (step adj χ r) (Nat.le_add_right n _) (h r hr)

/-- **★★★ THE POLY GUARD IS EXACTLY `Tinhofer`.** Sound (`DeepenGuard` §3) and complete (§5). -/
theorem tinhofer_iff_certifiedG {adj : AdjMatrix n} {χ : Colouring n} :
    Tinhofer adj χ ↔ CertifiedG deepenSupply adj χ :=
  ⟨certifiedG_of_tinhofer, tinhofer_of_certifiedG⟩

/-! ## 6. ★★★ THE GUARD TRANSPORTS — WITHOUT `SupplyEquivariant`

`DeepenGuard.certPath_transport` needs `SupplyEquivariant S`, which `deepenSupply` lacks (its greedy
descent breaks ties by vertex index). §5 routes around it entirely: the guard is *equal* to a
predicate already known relabelling-invariant, so it inherits that invariance. -/

theorem certifiedG_transport {adj : AdjMatrix n} {χ : Colouring n} (σ : Equiv.Perm (Fin n))
    (h : CertifiedG deepenSupply adj χ) :
    CertifiedG deepenSupply (relabelAdj σ adj) (transportColouring σ χ) :=
  certifiedG_of_tinhofer (tinhofer_transport σ (tinhofer_of_certifiedG h))

theorem certifiedG_transport_iff {adj : AdjMatrix n} {χ : Colouring n} (σ : Equiv.Perm (Fin n)) :
    CertifiedG deepenSupply (relabelAdj σ adj) (transportColouring σ χ)
      ↔ CertifiedG deepenSupply adj χ := by
  rw [← tinhofer_iff_certifiedG, ← tinhofer_iff_certifiedG]
  exact tinhofer_transport_iff σ

/-! ## 7. ★★★ THE PAYOFF — a COMPUTABLE supply carrying the `Tinhofer` guard -/

instance instDecidableCertifiedG (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    Decidable (CertifiedG S adj χ) :=
  inferInstanceAs (Decidable (∀ r ∈ Descend.branches χ, CertPath S adj n (step adj χ r)))

/-- **★★★ THE EXECUTABLE GUARDED DEEPEN SUPPLY.** `deepenSupplyGuarded` with its `Prop`-valued
`Tinhofer` test replaced by the decidable certificate. By §5 the two tests are the same predicate, so
this is `deepenSupplyGuarded` — computably. -/
def deepenSupplyCert : Supply n := fun adj χ =>
  if CertifiedG deepenSupply adj χ then deepenSupply adj χ else ([], n * n * n * n * n * n)

theorem deepenSupplyCert_eq_guarded : (deepenSupplyCert (n := n)) = deepenSupplyGuarded := by
  funext adj χ
  unfold deepenSupplyCert deepenSupplyGuarded
  by_cases h : Tinhofer adj χ
  · rw [if_pos h, if_pos (certifiedG_of_tinhofer h)]
  · rw [if_neg h, if_neg (fun hc => h (tinhofer_of_certifiedG hc))]

/-- **★★★ `①` FOR A COMPUTABLE OBJECT, WITH NO HYPOTHESIS.** `deepenSupplyGuarded_canonizer`'s
hypothesis-free `①c` transferred along §7's equality. This is the statement `DeepenCertified` §7
called "`R1`, not a wiring step". -/
theorem deepenSupplyCert_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupplyCert (n := n))))) := by
  rw [deepenSupplyCert_eq_guarded]
  exact deepenSupplyGuarded_canonizer

/-- The guard's residue, named: where the executable supply defers, `Tinhofer` genuinely fails — so
the deferral is a `RigidObstructionAt` somewhere below (`rigidObstruction_of_not_cellSingleOrbit`),
never an artefact of the index-picked descent. -/
theorem not_tinhofer_of_deepenSupplyCert_defers {adj : AdjMatrix n} {χ : Colouring n}
    (h : Consume.gens (deepenSupplyCert (n := n)) adj χ = []) (hne : deepenGens adj χ ≠ []) :
    ¬ Tinhofer adj χ := by
  intro hT
  apply hne
  unfold Consume.gens deepenSupplyCert at h
  rw [if_pos (certifiedG_of_tinhofer hT)] at h
  exact h

end Deepen
end ChainDescent
