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

/-! ## 8. ★★ A SECONDARY GUARD — per-anchor, strictly weaker than `Tinhofer`

`CertifiedG` is a conjunction over the whole cell, so it shuts as soon as **one** level of **one**
anchor's path meets a mixed cell. But `①` never needed `Tinhofer`: it needs `OrbitComplete`
(`DeepenComplete.deepenSupply_canonizer_of_orbitComplete`), and `DeepenComplete` §5's *good-or-rigid*
already implies that while being strictly weaker — a vertex no automorphism moves needs no good path.

What blocked using it was decidability of the first disjunct. §5's implications are stated **per
path**, not per graph, so they compose to a per-anchor equivalence, and goodness becomes decidable one
anchor at a time. The second disjunct (`OrbitTrivial`) is *not* decidable — it quantifies over `Aut` —
but any relabelling-invariant computable vertex invariant that isolates `u` inside its cell implies
it, soundly.

⚠ **The invariance bar is the real constraint on any secondary guard**, and it is why the guard is
built from `GoodAnchor`/`OrbitTrivial` (intrinsic, transport-stable) rather than from deepen's output:
`DeepenGuard`'s header records a measured CFI falsifier where deepen's own certificate is one orbit
under some labellings and `8 + 8` under others. §5 escaped that only because `CertifiedG` turned out
to *equal* the intrinsic `Tinhofer`. Anything read off `deepenGens` alone inherits the falsifier. -/

/-- **★★ GOODNESS IS DECIDABLE, ONE ANCHOR AT A TIME.** The per-anchor form of §5. -/
theorem goodAnchor_iff_certPath {adj : AdjMatrix n} {χ : Colouring n} {u : Fin n} :
    GoodAnchor adj χ u ↔ CertPath deepenSupply adj n (step adj χ u) :=
  ⟨fun h => certPath_of_tinhoferPath adj χ n (step adj χ u) (Nat.le_add_right n _) h,
   fun h => tinhoferPath_of_certPath deepenSupply adj χ n _ h⟩

instance instDecidableGoodAnchor (adj : AdjMatrix n) (χ : Colouring n) (u : Fin n) :
    Decidable (GoodAnchor adj χ u) :=
  decidable_of_iff _ goodAnchor_iff_certPath.symm

/-- `u` is **isolated** by a vertex invariant `inv`: no other member of its branch cell shares its
value. Decidable, unlike `OrbitTrivial`. -/
def IsolatedBy (inv : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (u : Fin n) : Prop :=
  ∀ w ∈ Descend.branches χ, w ≠ u → inv adj χ w ≠ inv adj χ u

instance instDecidableIsolatedBy (inv : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (u : Fin n) : Decidable (IsolatedBy inv adj χ u) :=
  inferInstanceAs (Decidable (∀ w ∈ Descend.branches χ, w ≠ u → inv adj χ w ≠ inv adj χ u))

/-- An `Aut`-invariant vertex invariant that isolates `u` in its cell proves `u` is fixed by every
colour-automorphism — the decidable stand-in for `OrbitTrivial`. -/
theorem orbitTrivial_of_isolatedBy {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : ∀ (adj : AdjMatrix n) (χ : Colouring n) (ρ : Equiv.Perm (Fin n)), IsColAut adj χ ρ →
      ∀ u, inv adj χ (ρ u) = inv adj χ u)
    {adj : AdjMatrix n} {χ : Colouring n} {u : Fin n} (hu : u ∈ Descend.branches χ)
    (h : IsolatedBy inv adj χ u) : OrbitTrivial adj χ u := by
  intro ρ hρ
  by_contra hne
  exact h (ρ u) (isColAut_mem_branches hρ hu) hne (hinv adj χ ρ hρ u)

/-- **★★ THE SECONDARY GUARD.** Every anchor is either good (decidable by
`goodAnchor_iff_certPath`) or isolated by `inv` (decidable). Strictly weaker than `CertifiedG`: it
tolerates mixed cells wherever the mixture is visible to `inv`. -/
def GoodOrIsolated (inv : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ Descend.branches χ, GoodAnchor adj χ u ∨ IsolatedBy inv adj χ u

instance instDecidableGoodOrIsolated (inv : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Decidable (GoodOrIsolated inv adj χ) :=
  inferInstanceAs (Decidable (∀ u ∈ Descend.branches χ,
    GoodAnchor adj χ u ∨ IsolatedBy inv adj χ u))

/-- **★★ THE SECONDARY GUARD IS SOUND FOR `①`** — it delivers `OrbitComplete`, which is all
`deepenSupply_canonizer_of_orbitComplete` ever asked for. -/
theorem orbitComplete_of_goodOrIsolated {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : ∀ (adj : AdjMatrix n) (χ : Colouring n) (ρ : Equiv.Perm (Fin n)), IsColAut adj χ ρ →
      ∀ u, inv adj χ (ρ u) = inv adj χ u)
    {adj : AdjMatrix n} {χ : Colouring n} (h : GoodOrIsolated inv adj χ) : OrbitComplete adj χ :=
  orbitComplete_of_good_or_trivial
    (fun u hu => (h u hu).imp id (orbitTrivial_of_isolatedBy hinv hu))

/-- `CertifiedG` ⟹ the secondary guard, for any `inv`: the primary guard is the special case where
every anchor takes the *left* disjunct. Records that §8 is a genuine weakening, not a variant. -/
theorem goodOrIsolated_of_certifiedG {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    {adj : AdjMatrix n} {χ : Colouring n} (h : CertifiedG deepenSupply adj χ) :
    GoodOrIsolated inv adj χ :=
  fun u hu => Or.inl (tinhofer_of_certifiedG h u hu)

/-! ## 9. ★★★ THE SECONDARY GUARD **IS** RELABELLING-EQUIVARIANT

§8 left this open ("it hasn't been proven relabelling-equivariant yet"). It is — and the reason it
looked doubtful is worth recording, because it is a hypothesis bug rather than a mathematical
obstruction.

**Both disjuncts transport, but for different reasons, and only one of them was hypothesised.**

* `GoodAnchor` transports **outright**, with no side condition: `tinhoferPath_transport` is already
  stated cross-graph (at `relabelAdj σ adj`), so `goodAnchor_relabel` below is a one-liner. §8's
  `goodAnchor_transport` is the *automorphism* specialisation; the relabelling version is the more
  general statement and was always available.
* `IsolatedBy inv` transports **iff `inv` does**. §8 assumes only that `inv` is `Aut`-**invariant**
  (`hinv`), which is exactly what `orbitTrivial_of_isolatedBy` needs for *soundness* and is strictly
  too weak for *transport*: an `Aut`-invariant `inv` may take unrelated values at `(adj, χ, u)` and at
  `(σ adj, σ χ, σ u)`, and then a vertex isolated before relabelling need not be isolated after.

So the fix is to strengthen `hinv` from `Aut`-invariance to relabelling-**equivariance**
(`InvEquivariant`). That is not a new burden: it is what any *computed* vertex invariant satisfies by
construction, and it **implies** the `Aut`-invariance §8 already assumes
(`autInvariant_of_invEquivariant`), so it replaces `hinv` rather than adding to it.

⟹ `deepenSupplyGI`, a computable supply guarded by the **strictly weaker** §8 condition, with `①`
carrying no hypothesis beyond `InvEquivariant inv` — which is discharged once, per invariant.
⚠ Coverage is weakly larger than `deepenSupplyCert`'s (`goodOrIsolated_of_certifiedG`), so the
residue is a *subset* of `¬ Tinhofer` and `③` composes unchanged. ⚠ `②` carries the same unbilled-guard
gap as §7 — see the module notes there; nothing here bills the `IsolatedBy` scan.

## ✅✅★★★ THE SECONDARY GUARD **STRICTLY BEATS** `CertifiedG` — CONFIRMED EXHAUSTIVELY 2026-08-06

**`scratchpad/probe_strictwin.py` + `probe_strictwin_verify.py`. 2 strict wins in 60 random cubic
graphs**, and the smallest is verified with **no orbit oracle, no `canon`, no generator harvesting** —
`probe_strictwin_verify.py` enumerates all `10!` permutations directly.

> **The `n = 10` witness.** Cubic, `|Aut(G, χ_1WL)| = 2`, 1-WL does **not** discretize (one 10-cell).
> True orbits inside that cell: `[0,8] [1,4] [2,5] [3] [6,9] [7]`. Vertex **7** is the **only** bad
> anchor, it is **`Aut`-rigid**, and `stepSum` **isolates** it. Hence
> **`CertifiedG` (= `Tinhofer`) SHUT, `GoodOrIsolated` OPEN** — and every isolated vertex is genuinely
> rigid, so `orbitTrivial_of_isolatedBy` is applied soundly.
> `adj` rows: `0000010011 0001100001 0000000111 0100100100 0101001000 1000001100 0000110010
> 0011010000 1010001000 1110000000`.

★ **Where such witnesses live, and why the first two attempts missed them.** A strict win needs a cell
whose **bad** anchors are all `Aut`-**rigid** and `inv`-isolable. The user's `C₃`/`C₄` witness had bad
anchors that were *twins* (not rigid ⟹ not soundly isolable); the `C₈` witness had **no** bad anchors.
Generic rigid-ish regular graphs supply both conditions at once, and the earlier 11-witness sweep
contained none — it was all multipedes and CFI, which are *built* to defeat WL-computable invariants.

⚠ **The earlier "worth nothing" reading of this section (isol = 0 on 11/11) was a POPULATION artefact
and is retracted.** `IsolatedBy` is non-vacuous, `GoodOrIsolated` strictly extends the handled class
beyond `Tinhofer`, and §9 may be cited as coverage. The superseded measurement follows.

## ⚠ SUPERSEDED — the original 11-witness sweep (kept as provenance)

`scratchpad/probe_goodorisolated.py` + `probe_isolpower.py`, 11 witnesses (4 rigid multipedes,
`MIXED`, `circ(5)`, `mp7`, CFI over cubic bases m = 8/10 plain and twisted), root branch cell:

> **`isol = 0` on 11/11, for THREE escalating equivariant invariants** — `stepSum`, the full sorted
> colour **multiset** after individualizing `u`, and a **two-step** (individualize `u`, then each `w`)
> refinement signature. **Strict wins (secondary guard open where the primary is shut): 0/11.**

It fails precisely where it was designed to win: `rand multipede V=12 W=8` has cell 4 with **four
singleton orbits** — every anchor is `Aut`-rigid, so `OrbitTrivial` holds for all four and
`DeepenComplete` §5 would open — yet no refinement-computable invariant separates them, so
`IsolatedBy` is false and the guard shuts anyway.

★ **On that population this is not a weak choice of `inv`** — multipedes and CFI graphs are *built* so
that WL-computable invariants cannot separate their orbits, which is the `KEY_scoping.md` *"rich /
invariant / poly = pick two"* wall. ⚠ But it does **not** generalise: those families are the hard
core, not the typical input, and the block above exhibits ordinary cubic graphs where `IsolatedBy`
fires and the guard strictly wins. **Read this sweep as "the wall families defeat it", not as "it buys
nothing".** -/

/-- A vertex invariant is **relabelling-equivariant** when relabelling the graph carries its value
along. This is the property `IsolatedBy` needs and the one §8's `hinv` was missing. -/
def InvEquivariant (inv : AdjMatrix n → Colouring n → Fin n → Nat) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (u : Fin n),
    inv (relabelAdj σ adj) (Descend.transportColouring σ χ) (σ u) = inv adj χ u

/-- Equivariance **implies** §8's `Aut`-invariance: an automorphism fixes both the graph and the
colouring, so the general statement collapses to the special one. -/
theorem autInvariant_of_invEquivariant {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (h : InvEquivariant inv) (adj : AdjMatrix n) (χ : Colouring n) (ρ : Equiv.Perm (Fin n))
    (hρ : IsColAut adj χ ρ) (u : Fin n) : inv adj χ (ρ u) = inv adj χ u := by
  have hg := h ρ adj χ u
  rwa [hρ.relabel, transportColouring_isColAut hρ] at hg

/-- **★ `GoodAnchor` TRANSPORTS ACROSS A RELABELLING** — unconditionally. `tinhoferPath_transport` is
already cross-graph; this just feeds it `step_transport`. -/
theorem goodAnchor_relabel (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n} {u : Fin n}
    (h : GoodAnchor adj χ u) :
    GoodAnchor (relabelAdj σ adj) (Descend.transportColouring σ χ) (σ u) :=
  tinhoferPath_transport adj χ (Descend.transportColouring σ χ) n (step adj χ u)
    (step (relabelAdj σ adj) (Descend.transportColouring σ χ) (σ u)) σ (step_transport σ adj χ u) h

/-- **★ `IsolatedBy` TRANSPORTS EXACTLY WHEN `inv` DOES.** -/
theorem isolatedBy_transport {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : InvEquivariant inv) (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n}
    {u : Fin n} (h : IsolatedBy inv adj χ u) :
    IsolatedBy inv (relabelAdj σ adj) (Descend.transportColouring σ χ) (σ u) := by
  intro w' hw' hne
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Descend.branches χ, σ w = w' := by
    rw [(Descend.branches_transport_perm σ χ).mem_iff, List.mem_map] at hw'; exact hw'
  rw [hinv σ adj χ w, hinv σ adj χ u]
  exact h w hw (fun heq => hne (congrArg σ heq))

/-- **★★★ THE SECONDARY GUARD TRANSPORTS.** -/
theorem goodOrIsolated_transport {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : InvEquivariant inv) (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n}
    (h : GoodOrIsolated inv adj χ) :
    GoodOrIsolated inv (relabelAdj σ adj) (Descend.transportColouring σ χ) := by
  intro u' hu'
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ Descend.branches χ, σ u = u' := by
    rw [(Descend.branches_transport_perm σ χ).mem_iff, List.mem_map] at hu'; exact hu'
  exact (h u hu).imp (goodAnchor_relabel σ) (isolatedBy_transport hinv σ)

/-- The guard's verdict is relabelling-**invariant**, both directions. -/
theorem goodOrIsolated_transport_iff {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : InvEquivariant inv) (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n} :
    GoodOrIsolated inv (relabelAdj σ adj) (Descend.transportColouring σ χ)
      ↔ GoodOrIsolated inv adj χ := by
  refine ⟨fun h => ?_, goodOrIsolated_transport hinv σ⟩
  have h' := goodOrIsolated_transport hinv σ⁻¹ h
  rwa [← relabelAdj_mul, transportColouring_comp, inv_mul_cancel, relabelAdj_one,
       transportColouring_one] at h'

/-! ### 9a. The supply it guards, and `①` for it -/

/-- **★★ THE SECONDARY-GUARDED DEEPEN SUPPLY.** `deepenSupplyCert` with the strictly weaker §8
guard. Computable: both disjuncts are decidable (`instDecidableGoodOrIsolated`). -/
def deepenSupplyGI (inv : AdjMatrix n → Colouring n → Fin n → Nat) : Consume.Supply n := fun adj χ =>
  if GoodOrIsolated inv adj χ then deepenSupply adj χ else ([], n * n * n * n * n * n)

theorem verified_GI_of_open {inv : AdjMatrix n → Colouring n → Fin n → Nat} {adj : AdjMatrix n}
    {χ : Colouring n} (h : GoodOrIsolated inv adj χ) :
    Consume.verified (deepenSupplyGI inv) adj χ = Consume.verified deepenSupply adj χ := by
  unfold Consume.verified Consume.gens deepenSupplyGI
  rw [if_pos h]

theorem verified_GI_of_shut {inv : AdjMatrix n → Colouring n → Fin n → Nat} {adj : AdjMatrix n}
    {χ : Colouring n} (h : ¬ GoodOrIsolated inv adj χ) :
    Consume.verified (deepenSupplyGI inv) adj χ = [] := by
  unfold Consume.verified Consume.gens deepenSupplyGI
  rw [if_neg h]; rfl

/-- **★★ THE BRANCH-ORBIT RELATION TRANSPORTS.** Open side: §8's `orbitComplete_of_goodOrIsolated`
makes the relation *equal* the `IsColAut`-orbit relation, which conjugates. Shut side: both are `[]`.
Same two-case shape as `deepenSupplyGuarded`'s, with §9 supplying the guard's own invariance. -/
theorem deepen_branchOrbit_transport_GI {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : InvEquivariant inv) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b : Fin n) (ha : a ∈ Descend.branches χ) (_hb : b ∈ Descend.branches χ) :
    Consume.WordReach
        (Consume.verified (deepenSupplyGI inv) (relabelAdj σ adj)
          (Descend.transportColouring σ χ)) (σ a) (σ b)
      ↔ Consume.WordReach (Consume.verified (deepenSupplyGI inv) adj χ) a b := by
  have hAut := autInvariant_of_invEquivariant hinv
  by_cases hA : GoodOrIsolated inv adj χ
  · have hA' := goodOrIsolated_transport hinv σ hA
    rw [verified_GI_of_open hA', verified_GI_of_open hA]
    have hσa : σ a ∈ Descend.branches (Descend.transportColouring σ χ) :=
      (Descend.branches_transport_perm σ χ).mem_iff.mpr (List.mem_map_of_mem ha)
    rw [branch_orbit_iff_aut_of_orbitComplete (orbitComplete_of_goodOrIsolated hAut hA') hσa,
        branch_orbit_iff_aut_of_orbitComplete (orbitComplete_of_goodOrIsolated hAut hA) ha]
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
  · have hA' : ¬ GoodOrIsolated inv (relabelAdj σ adj) (Descend.transportColouring σ χ) :=
      fun h => hA ((goodOrIsolated_transport_iff hinv σ).mp h)
    rw [verified_GI_of_shut hA', verified_GI_of_shut hA, wordReach_nil_iff, wordReach_nil_iff]
    exact ⟨fun h => σ.injective h, fun h => congrArg σ h⟩

/-- **★★★ `①` FOR THE SECONDARY-GUARDED SUPPLY — no hypothesis but `InvEquivariant inv`.** -/
theorem deepenSupplyGI_canonizer {inv : AdjMatrix n → Colouring n → Fin n → Nat}
    (hinv : InvEquivariant inv) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupplyGI (n := n) inv)))) :=
  Residue.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport
      Force.keyEquivariant_lookahead (deepen_branchOrbit_transport_GI hinv))

/-! ### 9b. `InvEquivariant` is INHABITED by a computable, discriminating invariant

Without this §9a would be conditional on a hypothesis nothing satisfies. `stepSum` is the total of the
refined colour ranks after individualizing `u` — deepen's own first step, read as a number. It is
equivariant because `step` is (`step_transport`) and because `transportColouring` **permutes positions
without touching values**, so any symmetric aggregate of a colouring survives it. -/

/-- The colour-rank total of `u`'s individualize-and-refine. Computable, `O(n³)`, and a genuine
vertex invariant: any aggregate of the refined colouring works, this is the cheapest. -/
def stepSum (adj : AdjMatrix n) (χ : Colouring n) (u : Fin n) : Nat :=
  ∑ v : Fin n, (step adj χ u).col v

/-- A transported colouring has the same colour **multiset**, hence the same sum. -/
theorem sum_transportColouring (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) :
    ∑ v : Fin n, Descend.transportColouring σ ψ v = ∑ v : Fin n, ψ v :=
  Equiv.sum_comp σ.symm ψ

theorem invEquivariant_stepSum : InvEquivariant (stepSum (n := n)) := by
  intro σ adj χ u
  unfold stepSum
  rw [show (step (relabelAdj σ adj) (Descend.transportColouring σ χ) (σ u)).col
        = Descend.transportColouring σ ((step adj χ u).col) from step_transport σ adj χ u]
  exact sum_transportColouring σ _

/-- **★★★ A CONCRETE COMPUTABLE CANONIZER AT THE SECONDARY GUARD.** `①`, no hypothesis at all. -/
theorem deepenSupplyGI_stepSum_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupplyGI (n := n) stepSum)))) :=
  deepenSupplyGI_canonizer invEquivariant_stepSum

end Deepen
end ChainDescent
