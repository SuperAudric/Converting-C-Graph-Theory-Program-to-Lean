import ChainDescent.DeepenExact

/-!
# A POLY, RELABELLING-INVARIANT GUARD for `orbKey`

`orbKey`'s guard is `AmenablePath`, which is *decidable* but only by an `n!` search — so `orbKey` is
`noncomputable` and cannot enter `Publication.canonForm?`. This file replaces the guard by one that is
**poly, sound and invariant**, parameterised by any supply that already transports.

**Why not deepen's own certificate.** `Certified` / `CertifiedPath` (`DeepenCertified` T1/T2) is poly
and sound, and the obvious plan was to prove *it* invariant. **That is measured FALSE**
(`scratchpad/probe_guard_invariance.py`, scoping doc §7.1): on the CFI graph over a random cubic base
with `m = 8` there is a node whose branch cell the all-anchor harvest certifies as **one orbit under
some labellings** and splits **8 + 8 under others**. The certificate is computed *by* the index-picked
descent, so it inherits exactly that descent's labelling dependence. A guard built from it would break
`KeyEquivariant` through its own `if`.

**What works instead.** Guard each level by `Consume.CellIsOrbit S` for a supply `S` that is already
**`SupplyEquivariant`** — i.e. whose *verified* generator list transports as `σ`-conjugates. Then:

* **SOUND** (§3) — `S`'s generators are verified `IsColAut` and `WordReach` composes, so
  `CellIsOrbit S` at a level gives that level's `CellSingleOrbit`, hence `CertPath S ⟹ AmenablePath`.
  This is `DeepenCertified`'s T1 with `deepenSupply` generalised away.
* **INVARIANT** (§2, §4) — `CellIsOrbit S` transports (`cellIsOrbit_transport`, from
  `SupplyEquivariant` + `branches_transport_perm`), and the per-level index-pick mismatch is absorbed
  exactly as in `amenablePath_transport`, with SOUND supplying the stabiliser element.
* **POLY** — if `S` is.

Five supplies already carry `GensEquivariant` (hence `SupplyEquivariant` via
`supplyEquivariant_of_gensEquivariant`): `deckSupply`, `deck2Supply`, `foldSupply`, `foldSupplyFast`,
`Consume.matchSupply`. This file is parametric in `S`, so it applies to each and to any future one.

## ⚠ What this costs — read before using it in place of `orbKey`

`CertPath S ⟹ AmenablePath`, never the converse. So `orbKeyG S` is a **restriction** of `orbKey`: it
agrees wherever it is defined and defers more often. Consequently

> the unconditional theorem **`consume_fail_force_fires` (`DeepenExact`) is stated for `orbKey` and
> stays there.** For `orbKeyG S` the localization half is unchanged — a consume failure still reaches a
> node that is `Amenable` and carries a `RigidObstructionAt` — but the *firing* half becomes
> conditional on the poly guard being open at that node (`forceBy_orbKeyG_narrows`).

That is a firing loss, not a soundness loss: where the guard is shut the key is constant, force simply
does not act, and `①` is untouched. Measured (`scratchpad/probe_eqsupply_guard.py`, a **depth-0 lower
bound** for the deck family): the guard opens at **24/24** hook nodes on Chang-B and **96/108** on
Chang-A, and at **none** of the hook nodes on the disjoint-cycle and MIXED witnesses. So the two keys
are meant to coexist — `orbKey` carries the theory, `orbKeyG S` is the executable.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut Supply verified CellIsOrbit WordReach)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. `WordReach` over a verified list is an automorphism — for ANY supply

`DeepenAmenable.wordReach_imp_isColAut` is stated for `deepenSupply`; its proof uses only that every
member of the list is a verified `IsColAut`. Restated at that generality. -/

theorem wordReach_isColAut {adj : AdjMatrix n} {χ : Colouring n}
    {G : List (Equiv.Perm (Fin n))} (hG : ∀ g ∈ G, IsColAut adj χ g) {u w : Fin n}
    (h : WordReach G u w) : ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w := by
  induction h with
  | refl => exact ⟨1, IsColAut.one adj χ, rfl⟩
  | @step m _ g hg ih =>
      obtain ⟨β, hβ, hβu⟩ := ih
      exact ⟨g * β, IsColAut.comp (hG g hg) hβ, by
        show g (β u) = g m
        rw [hβu]⟩

theorem wordReach_isColAut_verified {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (h : WordReach (verified S adj χ) u w) :
    ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w :=
  wordReach_isColAut (fun _ hg => Consume.isColAut_of_mem_verified hg) h

/-- **`CellIsOrbit` for ANY supply gives the branch cell's `CellSingleOrbit`.** The generalisation of
`DeepenCertified`'s T1 chain (`certifiedOrbit_of_cellIsOrbit` ∘ `cellSingleOrbit_of_certifiedOrbit`). -/
theorem cellSingleOrbit_of_cellIsOrbit {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c) (h : CellIsOrbit S adj χ) :
    CellSingleOrbit adj χ c := by
  intro u w hu hw
  exact wordReach_isColAut_verified
    (h u ((Descend.mem_branches_iff hc u).mpr hu) w ((Descend.mem_branches_iff hc w).mpr hw))

/-! ## 2. `CellIsOrbit S` TRANSPORTS when `S` does

The one lemma the design was missing. `WordReach` transports because `SupplyEquivariant` says the
relabelled verified list is exactly the set of `σ`-conjugates, and `(σ g σ⁻¹) (σ m) = σ (g m)`. -/

theorem wordReach_transport {S : Supply n} (hS : SupplyEquivariant S)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) {u w : Fin n}
    (h : WordReach (verified S adj χ) u w) :
    WordReach (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ u) (σ w) := by
  induction h with
  | refl => exact WordReach.refl _
  | @step m _ g hg ih =>
      have hmem : σ * g * σ⁻¹ ∈ verified S (relabelAdj σ adj) (transportColouring σ χ) :=
        (hS σ adj χ (σ * g * σ⁻¹)).mpr ⟨g, hg, rfl⟩
      have := WordReach.step ih hmem
      have heq : (σ * g * σ⁻¹) (σ m) = σ (g m) := by
        simp [Equiv.Perm.mul_apply]
      rwa [heq] at this

theorem cellIsOrbit_transport {S : Supply n} (hS : SupplyEquivariant S)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (h : CellIsOrbit S adj χ) :
    CellIsOrbit S (relabelAdj σ adj) (transportColouring σ χ) := by
  intro u' hu' w' hw'
  rw [(Descend.branches_transport_perm σ χ).mem_iff, List.mem_map] at hu' hw'
  obtain ⟨u, hu, rfl⟩ := hu'
  obtain ⟨w, hw, rfl⟩ := hw'
  exact wordReach_transport hS σ adj χ (h u hu w hw)

/-! ## 3. `CertPath` — the guard, and its soundness

The recursion is `AmenablePath`'s verbatim, with the *observable* `CellIsOrbit S` in place of the
unobservable `CellSingleOrbit`. Note it is stated at the level's own colouring: by the landed selector
identity `chooseIdK_eq_targetColour`, the cell `chooseIdK` picks **is** `Descend.branches`' cell, so
`CellIsOrbit S` speaks about exactly the cell the level individualizes. -/

def CertPath (S : Supply n) (adj : AdjMatrix n) : Nat → Refine.ColData n → Prop
  | 0, _ => True
  | fuel + 1, cur =>
      match chooseIdK (List.finRange n) cur.col with
        | none => True
        | some cid =>
            CellIsOrbit S adj cur.col ∧
            (match (List.finRange n).filter (fun v => cur.col v == cid) with
             | [] => True
             | w :: _ => CertPath S adj fuel (step adj cur.col w))

/-- Every anchor's path is certified. The poly analogue of `Amenable`. -/
def CertifiedG (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ r ∈ Descend.branches χ, CertPath S adj n (step adj χ r)

/-- **★★ SOUND — the poly guard implies the real one.** Each level's `CellIsOrbit S` is a *checked*
transitivity of verified automorphisms, which is what `CellSingleOrbit` asks for. -/
theorem amenablePath_of_certPath (S : Supply n) (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n),
      CertPath S adj fuel cur → AmenablePath adj χp fuel cur := by
  intro fuel
  induction fuel with
  | zero => intro _ _; trivial
  | succ fuel ih =>
      intro cur h
      unfold CertPath at h
      unfold AmenablePath
      dsimp only            -- zeta-reduce the goal's `let χc := cur.col`
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => exact trivial
      | some cid =>
          rw [hco] at h
          obtain ⟨hcell, htail⟩ := h
          refine ⟨cellSingleOrbit_of_cellIsOrbit ?_ hcell, ?_⟩
          · rw [← chooseIdK_eq_targetColour]; exact hco
          · cases hfl : (List.finRange n).filter (fun v => cur.col v == cid) with
            | nil => trivial
            | cons w rest =>
                rw [hfl] at htail
                dsimp only at htail
                exact ih _ htail

theorem amenable_of_certifiedG {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (h : CertifiedG S adj χ) : Amenable adj χ :=
  fun r hr => amenablePath_of_certPath S adj χ n _ (h r hr)

/-! ## 4. ★★ THE GUARD TRANSPORTS

Same shape as `amenablePath_transport`: the level's cell is a single orbit (which §3 extracts from the
*observable* hypothesis), so a stabiliser element carries `σ w_a` to `w_b` and the relating isomorphism
accumulates. The only new ingredient is `cellIsOrbit_transport`. -/

theorem certPath_transport {S : Supply n} (hS : SupplyEquivariant S) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (cur_a cur_b : Refine.ColData n) (σ : Equiv.Perm (Fin n)),
      cur_b.col = transportColouring σ cur_a.col →
      CertPath S adj fuel cur_a →
      CertPath S (relabelAdj σ adj) fuel cur_b := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; trivial
  | succ fuel ih =>
      intro cur_a cur_b σ hrel hC
      unfold CertPath at hC
      unfold CertPath
      cases hco : chooseIdK (List.finRange n) cur_a.col with
      | none =>
          have hb : chooseIdK (List.finRange n) cur_b.col = none := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [hb]; exact trivial
      | some cid =>
          have hb : chooseIdK (List.finRange n) cur_b.col = some cid := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [hco] at hC
          rw [hb]
          obtain ⟨hcell_a, hCrec⟩ := hC
          have hcell_b : CellIsOrbit S (relabelAdj σ adj) cur_b.col := by
            rw [hrel]; exact cellIsOrbit_transport hS σ adj cur_a.col hcell_a
          refine ⟨hcell_b, ?_⟩
          -- the level really is a single orbit, which is what absorbs the index-pick mismatch
          have hso_a : CellSingleOrbit adj cur_a.col cid :=
            cellSingleOrbit_of_cellIsOrbit (by rw [← chooseIdK_eq_targetColour]; exact hco) hcell_a
          have hso_b : CellSingleOrbit (relabelAdj σ adj) cur_b.col cid := by
            rw [hrel]; exact cellSingleOrbit_transport_iso σ hso_a
          have hlen_a : 2 ≤ (cidCell cur_a.col cid).length := chooseIdK_mem _ _ hco
          have hlen_b : 2 ≤ (cidCell cur_b.col cid).length := by
            rw [hrel, cidCell_length_transport]; exact hlen_a
          cases hfl : (List.finRange n).filter (fun v => cur_a.col v == cid) with
          | nil =>
              exfalso
              have hnil : cidCell cur_a.col cid = [] := hfl
              rw [hnil] at hlen_a; simp at hlen_a
          | cons w_a rest_a =>
              rw [hfl] at hCrec
              dsimp only at hCrec
              cases hfb : (List.finRange n).filter (fun v => cur_b.col v == cid) with
              | nil =>
                  exfalso
                  have hnil : cidCell cur_b.col cid = [] := hfb
                  rw [hnil] at hlen_b; simp at hlen_b
              | cons w_b rest_b =>
                  have hwa_mem : w_a ∈ cidCell cur_a.col cid := by
                    show w_a ∈ (List.finRange n).filter (fun v => cur_a.col v == cid)
                    rw [hfl]; exact List.mem_cons_self ..
                  have hwb_mem : w_b ∈ cidCell cur_b.col cid := by
                    show w_b ∈ (List.finRange n).filter (fun v => cur_b.col v == cid)
                    rw [hfb]; exact List.mem_cons_self ..
                  have hσwa : cur_b.col (σ w_a) = cid := by
                    have hm : σ w_a ∈ cidCell cur_b.col cid := by
                      rw [hrel]; exact mem_cidCell_transport_apply σ cur_a.col cid w_a hwa_mem
                    exact (mem_cidCell_iff _ _ _).mp hm
                  have hwbcid : cur_b.col w_b = cid := (mem_cidCell_iff _ _ _).mp hwb_mem
                  obtain ⟨τ, hτ, hτeq⟩ := hso_b (σ w_a) w_b hσwa hwbcid
                  have hadj' : relabelAdj (τ * σ) adj = relabelAdj σ adj := by
                    rw [relabelAdj_mul]; exact hτ.relabel
                  have hcolb : transportColouring (τ * σ) cur_a.col = cur_b.col := by
                    rw [← transportColouring_comp, ← hrel]; exact hτ.transport
                  have hwab : (τ * σ) w_a = w_b := by
                    show τ (σ w_a) = w_b; exact hτeq
                  have hrel' : (step (relabelAdj σ adj) cur_b.col w_b).col
                      = transportColouring (τ * σ) ((step adj cur_a.col w_a).col) := by
                    have hst := step_transport (τ * σ) adj cur_a.col w_a
                    rw [hadj', hcolb, hwab] at hst
                    exact hst
                  have := ih (step adj cur_a.col w_a) (step (relabelAdj σ adj) cur_b.col w_b)
                    (τ * σ) hrel' hCrec
                  rwa [hadj'] at this

/-- The guard at a vertex, both directions. -/
theorem certPath_step_transport_iff {S : Supply n} (hS : SupplyEquivariant S)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    CertPath S (relabelAdj σ adj) n
        (step (relabelAdj σ adj) (transportColouring σ χ) (σ v))
      ↔ CertPath S adj n (step adj χ v) := by
  constructor
  · intro h
    have hinv := certPath_transport hS (relabelAdj σ adj) n
      (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) (step adj χ v) σ⁻¹ ?_ h
    · rwa [← relabelAdj_mul, inv_mul_cancel, relabelAdj_one] at hinv
    · rw [step_transport σ adj χ v, transportColouring_comp, inv_mul_cancel,
          transportColouring_one]
  · intro h
    exact certPath_transport hS adj n (step adj χ v)
      (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) σ (step_transport σ adj χ v) h

/-! ## 5. `orbKeyG` — the same read, the poly guard -/

/-- Registered once so `orbKeyG` and `keyV_orbKeyG` share the instance term (which is what makes the
projection lemma `rfl`). For a concrete poly `S` this is replaced by a genuine decision procedure —
`CellIsOrbit S` is a finite `WordReach` reachability test on the branch cell. -/
noncomputable instance instDecidableCertPath (S : Supply n) (adj : AdjMatrix n) (fuel : Nat)
    (cur : Refine.ColData n) : Decidable (CertPath S adj fuel cur) := Classical.dec _

/-- **★★★ THE GUARDED KEY.** Identical to `orbKey` except that the `if` tests the *observable*
`CertPath S` instead of `AmenablePath`. Computable whenever `CellIsOrbit S` is decidable and `S` is
poly; `Classical.dec` is used here only so the definition elaborates without committing to a decision
procedure for a general `S`. -/
noncomputable def orbKeyG (S : Supply n) : Force.Key n := fun adj χ v =>
  (if CertPath S adj n (step adj χ v)
     then readKey adj (Descend.indivOne χ v) (leafOf adj n (step adj χ v)).col
     else [],
   n * n * n * n)

@[simp] theorem keyV_orbKeyG (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    Force.keyV (orbKeyG S) adj χ v =
      if CertPath S adj n (step adj χ v)
        then readKey adj (Descend.indivOne χ v) (leafOf adj n (step adj χ v)).col
        else [] := rfl

/-- **★★★ `①` FOR THE POLY-GUARDED KEY.** The guard transports (§4) and the value transports along the
`AmenablePath` the guard implies (§3 + `leafOf_transport_of_amenablePath`). No hypothesis beyond `S`
being equivariant — which five landed supplies already are. -/
theorem keyEquivariant_orbKeyG {S : Supply n} (hS : SupplyEquivariant S) :
    Force.KeyEquivariant (orbKeyG S) := by
  intro σ adj χ v
  rw [keyV_orbKeyG, keyV_orbKeyG]
  by_cases hC : CertPath S adj n (step adj χ v)
  · rw [if_pos ((certPath_step_transport_iff hS σ adj χ v).mpr hC), if_pos hC]
    obtain ⟨ρ, hρadj, hρφ, hρleaf⟩ :=
      leafOf_transport_of_amenablePath adj χ n (step adj χ v)
        (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) σ (Descend.indivOne χ v)
        (step_transport σ adj χ v) (refines_step adj χ v)
        (amenablePath_of_certPath S adj χ n _ hC)
    rw [hρleaf, ← hρadj, Descend.indivOne_transport, ← hρφ, readKey_transport]
  · rw [if_neg (fun h => hC ((certPath_step_transport_iff hS σ adj χ v).mp h)), if_neg hC]

/-! ## 6. Firing — unchanged, because `B1` never used the guard

`isColAut_of_readKey_eq` (`DeepenExact`) is guard-agnostic: it is completeness of the *read*. So the
separation argument transfers verbatim; only the hypothesis that both guards are open changes. -/

theorem orbKeyG_ne_of_no_aut {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {u w : Fin n}
    (hCu : CertPath S adj n (step adj χ u)) (hCw : CertPath S adj n (step adj χ w))
    (hno : ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Force.keyV (orbKeyG S) adj χ u ≠ Force.keyV (orbKeyG S) adj χ w := by
  rw [keyV_orbKeyG, keyV_orbKeyG, if_pos hCu, if_pos hCw]
  intro hkey
  obtain ⟨ρ, hρ, hρu⟩ :=
    isColAut_of_readKey_eq (χ := χ) (u := u) (w := w)
      (leafOf_discrete_n adj (step adj χ u))
      (leafOf_lt adj n (step adj χ u) (fun x => step_col_lt adj χ u x))
      (leafOf_discrete_n adj (step adj χ w))
      (leafOf_lt adj n (step adj χ w) (fun x => step_col_lt adj χ w x))
      hkey
  exact hno ρ hρ hρu

/-- **★★★ FORCE FIRES UNDER THE POLY GUARD.** At a node the guard certifies, a rigid obstruction in the
branch cell makes `forceBy (orbKeyG S)` strictly narrow. Compare `forceBy_orbKey_narrows`: the only
change is `CertifiedG S` (poly, observable) in place of `Amenable` (an `n!` search). -/
theorem forceBy_orbKeyG_narrows {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c) (hG : CertifiedG S adj χ)
    (hobs : RigidObstructionAt adj χ c) :
    (Descend.narrow (Force.forceBy (orbKeyG S)) adj χ).length < (Descend.branches χ).length := by
  obtain ⟨u, w, hu, hw, hno⟩ := hobs
  have hub : u ∈ Descend.branches χ := (Descend.mem_branches_iff hc u).mpr hu
  have hwb : w ∈ Descend.branches χ := (Descend.mem_branches_iff hc w).mpr hw
  exact Force.forceBy_narrows_of_key_ne hub hwb
    (orbKeyG_ne_of_no_aut (hG u hub) (hG w hwb) hno)

/-- **★★ THE POLY-GUARDED HOOK.** A consume failure still *locates* a force-actionable node — that half
(`DeepenLocated.not_amenable_deepest`) does not depend on the guard at all. What the poly guard costs is
that firing there needs the guard to be open, which is why this is stated with `CertifiedG S ψ` as a
hypothesis rather than derived. The unconditional statement remains
`DeepenExact.consume_fail_force_fires`, over `orbKey`. -/
theorem consume_fail_force_fires_guarded (S : Supply n) (adj : AdjMatrix n) {χ : Colouring n}
    (hd : ¬ Discrete χ) (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    ∃ ψ : Colouring n, DescentReach adj χ ψ ∧ Amenable adj ψ ∧
      (∃ cid, Descend.targetColour ψ = some cid ∧ RigidObstructionAt adj ψ cid) ∧
      (CertifiedG S adj ψ →
        (Descend.narrow (Force.forceBy (orbKeyG S)) adj ψ).length < (Descend.branches ψ).length) := by
  obtain ⟨c, hc⟩ := exists_targetColour hd
  by_cases hA : Amenable adj χ
  · refine ⟨χ, DescentReach.refl _, hA,
      ⟨c, hc, rigidObstructionAt_branch_of_amenable hc hA hfail⟩, fun hG => ?_⟩
    exact forceBy_orbKeyG_narrows hc hG (rigidObstructionAt_branch_of_amenable hc hA hfail)
  · obtain ⟨ψ, hreach, hAψ, cid, hct, hobs⟩ := not_amenable_deepest adj hA
    exact ⟨ψ, hreach, hAψ, ⟨cid, hct, hobs⟩, fun hG => forceBy_orbKeyG_narrows hct hG hobs⟩

/-- Wherever the poly guard is open, it certifies the `Amenable`-guarded key's guard too, so the two
keys **agree**: `orbKeyG S` is a restriction of `orbKey`, never a different function. -/
theorem orbKeyG_eq_orbKey_of_certPath {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {v : Fin n} (h : CertPath S adj n (step adj χ v)) :
    Force.keyV (orbKeyG S) adj χ v = Force.keyV orbKey adj χ v := by
  rw [keyV_orbKeyG, keyV_orbKey, if_pos h, if_pos (amenablePath_of_certPath S adj χ n _ h)]

/-! ## 7. Concrete instantiations — the design is not vacuous

The file is parametric in `S`; these pin it to supplies that already carry the hypothesis, so the
theorems above are about real objects. `deck2Supply` seeds **two** vertices and chases forced
consequences, which is the shape §7.2 of the scoping doc measured (there at depth 0, a lower bound). -/

theorem keyEquivariant_orbKeyG_deck2 :
    Force.KeyEquivariant (orbKeyG (Deck2.deck2Supply (n := n))) :=
  keyEquivariant_orbKeyG Deck2.supplyEquivariant_deck2Supply

theorem keyEquivariant_orbKeyG_deck :
    Force.KeyEquivariant (orbKeyG (Deck.deckSupply (n := n))) :=
  keyEquivariant_orbKeyG Deck.supplyEquivariant_deckSupply

/-- **★★★ THE POLY-GUARDED FORCE CANONIZER.** `Force.force_canonizer`'s sole obligation is
`KeyEquivariant`, so this is `①a`/`①b`/`①c` plus totality for the `deck2`-guarded key, with **no
hypothesis at all**. -/
theorem force_canonizer_orbKeyG_deck2 :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFree (n := n))
          (Force.forceBy (orbKeyG (Deck2.deck2Supply (n := n)))))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFree (n := n))
          (Force.forceBy (orbKeyG (Deck2.deck2Supply (n := n)))) adj ≠ none :=
  Force.force_canonizer keyEquivariant_orbKeyG_deck2

end Deepen
end ChainDescent
