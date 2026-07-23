import ChainDescent.Force
import ChainDescent.SelectNode

/-!
# The rigid seal — R0a: force separates non-automorphic pairs on the discretizing regime

The clean, wall-free core of Algorithm R's Lean build. On the **discretizing regime** (individualizing a
branch vertex refines to a discrete colouring), an augmented force key **`leafColKey`** — recording the
canonical `(pin-rank, χ-in-rank-order, leaf-matrix)` — is a *complete* invariant of the coloured-pointed
graph, so two branch vertices attain equal keys **iff** a colour-automorphism carries one to the other. Hence
`leafColKey` separates exactly the non-automorphic pairs (`RigidResolved`), discharging `NodeResolved` on the
discretizing regime.

⚠ The plain `Force.lookaheadKey` (adjacency-only leaf matrix) is **insufficient**: equal keys give only a
*graph* automorphism, with no `σ u = w` (the pin is not at a canonical rank) and no χ-preservation. `leafColKey`
is the strictly-stronger, still-polynomial, still-equivariant upgrade the rigid-seal doc anticipates ("the
solver replaces `lookaheadKey` with a stronger key"). This is R0a's realigned target: it feeds `HandledS` via
`answersS_of_handledS` (`SelectNode.lean`).
-/

namespace ChainDescent
namespace RigidSeal

open ChainDescent.Descend
open ChainDescent.Force
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-! ## 1. The augmented force key -/

/-- **The coloured leaf key.** On the discretizing branch, rank `v` by the complete coloured-pointed invariant
`(pin-rank, χ-in-rank-order, leaf-matrix)`; otherwise fall back to the cell-size histogram (as `lookaheadKey`). -/
def leafColKey : Key n := fun adj χ v =>
  let ψ : Colouring n := (lookData adj χ v).col
  ((if Discrete ψ then
      1 :: (Colouring.vertexRank ψ v).val
        :: ((List.finRange n).map (fun i => χ (rankInv ψ i)) ++ flatten (leafMatrix adj ψ))
    else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)),
   CostModel.WarmRefine.warmRefineCost n + n * n)

@[simp] theorem keyV_leafColKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (leafColKey (n := n)) adj χ v =
      (let ψ : Colouring n := (lookData adj χ v).col
       if Discrete ψ then
         1 :: (Colouring.vertexRank ψ v).val
           :: ((List.finRange n).map (fun i => χ (rankInv ψ i)) ++ flatten (leafMatrix adj ψ))
       else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)) := rfl

/-- The look-ahead colouring's cost — one refinement plus `n²`, charged like `lookaheadKey`. -/
theorem keyCost_leafColKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (leafColKey (n := n)) adj χ v = CostModel.WarmRefine.warmRefineCost n + n * n := rfl

/-! ## 2. `rankInv` transports (the χ-in-rank-order equivariance atom) -/

/-- **`rankInv` transports**: the rank-`i` vertex of the relabelled discrete colouring is `σ` of the rank-`i`
vertex of the original. Direct from `vertexRank`-injectivity and `vertexRank_transport`. -/
theorem rankInv_transport (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) (h : Discrete ψ) (i : Fin n) :
    rankInv (transportColouring σ ψ) i = σ (rankInv ψ i) := by
  have h' : Discrete (transportColouring σ ψ) := (discrete_transport σ ψ).mpr h
  rw [rankInv_eq_symm (transportColouring σ ψ) h' i, rankInv_eq_symm ψ h i]
  apply (Colouring.rankPerm (transportColouring σ ψ) h').injective
  rw [Equiv.apply_symm_apply, Colouring.rankPerm_apply, vertexRank_transport,
      ← Colouring.rankPerm_apply ψ h, Equiv.apply_symm_apply]

/-! ## 3. R0a core — equal augmented keys ⟹ a colour-automorphism `u ↦ w` -/

/-- **R0a CORE.** Given discretizing pins for `u`, `w` plus the three component-equalities the augmented key
delivers — equal leaf matrix, equal pin-rank, equal χ-in-rank-order — there is a **colour-automorphism** of
`(adj, χ)` taking `u ↦ w`. -/
theorem r0a_core (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (hu : Discrete (lookData adj χ u).col) (hw : Discrete (lookData adj χ w).col)
    (hlm : leafMatrix adj (lookData adj χ u).col = leafMatrix adj (lookData adj χ w).col)
    (hpin : Colouring.rankPerm _ hu u = Colouring.rankPerm _ hw w)
    (hcol : ∀ i : Fin n,
      χ ((Colouring.rankPerm _ hu).symm i) = χ ((Colouring.rankPerm _ hw).symm i)) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  rw [leafMatrix_eq_labelledAdj adj _ hu, leafMatrix_eq_labelledAdj adj _ hw] at hlm
  set πu := Colouring.rankPerm (lookData adj χ u).col hu with hπu
  set πw := Colouring.rankPerm (lookData adj χ w).col hw with hπw
  refine ⟨πw⁻¹ * πu, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    have hEq := congrFun (congrFun hlm (πu i)) (πu j)
    simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
    change adj.adj (πw.symm (πu i)) (πw.symm (πu j)) = adj.adj i j
    exact hEq.symm
  · intro v
    change χ (πw.symm (πu v)) = χ v
    have := hcol (πu v)
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  · change πw.symm (πu u) = w
    rw [hpin, Equiv.symm_apply_apply]

/-! ## 4. `leafColKey` is equivariant -/

theorem keyEquivariant_leafColKey : KeyEquivariant (leafColKey (n := n)) := by
  intro σ adj χ v
  rw [keyV_leafColKey, keyV_leafColKey]
  simp only [lookData_col_transport σ adj χ v]
  by_cases hd : Discrete ((lookData adj χ v).col)
  · rw [if_pos ((discrete_transport σ _).mpr hd), if_pos hd]
    have hpin : Colouring.vertexRank (transportColouring σ (lookData adj χ v).col) (σ v)
        = Colouring.vertexRank (lookData adj χ v).col v := vertexRank_transport σ _ v
    have hcolord :
        (List.finRange n).map
            (fun i => transportColouring σ χ (rankInv (transportColouring σ (lookData adj χ v).col) i))
          = (List.finRange n).map (fun i => χ (rankInv (lookData adj χ v).col i)) := by
      apply List.map_congr_left
      intro i _
      rw [rankInv_transport σ _ hd i]
      show transportColouring σ χ (σ (rankInv (lookData adj χ v).col i))
        = χ (rankInv (lookData adj χ v).col i)
      simp [transportColouring]
    rw [hpin, hcolord, leafMatrix_transport σ adj _ hd]
  · rw [if_neg (fun hc => hd ((discrete_transport σ _).mp hc)), if_neg hd]
    exact congrArg (0 :: ·) (List.map_congr_left (fun c _ =>
      cellOf_card_transport σ ((lookData adj χ v).col) c.val))

/-! ## 5. The completeness step — equal `leafColKey` values ⟹ a colour-automorphism -/

/-- **★ EQUAL KEYS ⟹ AUTOMORPHIC (discretizing regime).** If `u` and `w` both discretize on individualization
and attain the same `leafColKey` value, a colour-automorphism of `(adj, χ)` carries `u ↦ w`. The three key
components decompose to exactly `r0a_core`'s hypotheses. -/
theorem colAut_of_leafColKey_eq (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (hu : Discrete (lookData adj χ u).col) (hw : Discrete (lookData adj χ w).col)
    (hkey : keyV (leafColKey (n := n)) adj χ u = keyV (leafColKey (n := n)) adj χ w) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  rw [keyV_leafColKey, keyV_leafColKey] at hkey
  simp only [if_pos hu, if_pos hw] at hkey
  obtain ⟨_, htail⟩ := List.cons.inj hkey
  obtain ⟨hrank, hrest⟩ := List.cons.inj htail
  have hlen : ((List.finRange n).map (fun i => χ (rankInv (lookData adj χ u).col i))).length
      = ((List.finRange n).map (fun i => χ (rankInv (lookData adj χ w).col i))).length := by simp
  obtain ⟨hχo, hflat⟩ := List.append_inj hrest hlen
  have hlm : leafMatrix adj (lookData adj χ u).col = leafMatrix adj (lookData adj χ w).col :=
    flatten_injective hflat
  have hpin : Colouring.rankPerm _ hu u = Colouring.rankPerm _ hw w := by
    rw [Colouring.rankPerm_apply, Colouring.rankPerm_apply]; exact Fin.ext hrank
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map] at hχo
  have hcolfun := List.ofFn_inj.mp hχo
  have hcol : ∀ i, χ ((Colouring.rankPerm _ hu).symm i) = χ ((Colouring.rankPerm _ hw).symm i) := by
    intro i
    rw [← rankInv_eq_symm _ hu, ← rankInv_eq_symm _ hw]
    exact congrFun hcolfun i
  exact r0a_core adj χ u w hu hw hlm hpin hcol

/-! ## 6. `RigidResolved` — force separates every non-automorphic branch pair -/

/-- **The rigid-seam predicate (§4).** *Force distinguishes every non-automorphic branch pair.* -/
def RigidResolved (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
    keyV key adj χ u ≠ keyV key adj χ w

/-- **★★ R0a — `leafColKey` DISCHARGES `RigidResolved` on the discretizing regime** (no wall). Contrapositive of
`colAut_of_leafColKey_eq`: equal keys would furnish the very colour-automorphism a non-automorphic pair rules
out. -/
theorem rigidResolved_leafColKey (adj : AdjMatrix n) (χ : Colouring n)
    (hdisc : ∀ v ∈ branches χ, Discrete (lookData adj χ v).col) :
    RigidResolved (leafColKey (n := n)) adj χ := by
  intro u hu w hw hrig hkey
  obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w (hdisc u hu) (hdisc w hw) hkey
  exact hrig σ hσ hσuw

/-! ## 7. Wiring to `NodeResolved` — a rigid discretizing cell is handled by force -/

/-- **★★★ R0a → `NodeResolved`.** On a **rigid discretizing** branch cell — every branch vertex discretizes on
individualization, and no two distinct branch vertices are colour-automorphic — `leafColKey` separates the whole
cell, so the fused node resolves (`Select.NodeResolved`). This is regime (1) rigid: it feeds `HandledS` via
`Select.answersS_of_handledS`, no wall. -/
theorem nodeResolved_leafColKey_of_rigid_discretizing (S : Consume.Supply n) (adj : AdjMatrix n)
    (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hdisc : ∀ v ∈ branches χ, Discrete (lookData adj χ v).col)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (leafColKey (n := n)) S adj χ := by
  refine Select.nodeResolved_of_cellResolved hnd (Or.inr ?_)
  intro u hu w hw hkey
  by_contra hne
  obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w (hdisc u hu) (hdisc w hw) hkey
  exact hrigid u hu w hw hne σ hσ hσuw

/-! ## 8. R0b — the leafColKey precursor (the non-discretizing regime)

R0a handles every non-automorphic pair whose *both* individualizations discretize, with **no wall**. The residual
is the **non-discretizing** regime: individualizing a branch vertex fails to refine to discrete (the IR-blind-spot
/ multipede residue), so `leafColKey` falls back to the weak cell-size histogram and may not separate a
non-automorphic pair. Separating those is the rigid **solver**'s job (P3).

⚠ **CORRECTION (2026-07-23, do-not-re-derive).** `SmallAutThinAt` below is **NOT** the scheme wall `hSmallAutThin`.
`hSmallAutThin` (`CascadeAffine.lean:1320`) is a **static predicate on a `SchurianScheme`** (the minMult-form of
Babai's SRG structure theorem) — a *symmetry-consumption* / Route-C artifact, and it is *false on consumable
cases* (e.g. a multipede with a small added symmetry, already reduced by consume before any rigid solver). The
canonizer's actual residue is the **dynamic** `¬Select.HandledS` (interleaved mutual stall), a different object;
the two are joined only by the unbuilt W1 bridge (a *one-directional* seal-transfer, not an equivalence). The
old "`SmallAutThinAt` = `hSmallAutThin` at the seam" identity is **retracted**. `SmallAutThinAt` is only the
*leafColKey-specialization* of the separation obligation — and it is **not dischargeable** (its non-discretizing
pairs are exactly where `leafColKey`'s histogram ties). The carried object of record is **`SolverSeparates` over
the composite key `compKey` (§9)**, which IS dischargeable — by the rigid solver's own soundness (P3), because it
is a property of an algorithm we build, not an SRG citation. R0b is kept as the leafColKey landmark; §9 supersedes
it. -/

/-- **The leafColKey-specialization of the separation obligation** (NOT the scheme wall `hSmallAutThin` — see the
§8 correction). On the non-discretizing regime, `leafColKey` still separates every non-automorphic branch pair.
Superseded as the carried object by `SolverSeparates`/`compKey` (§9), which the rigid solver (P3) can discharge.
Vacuously true on the discretizing regime (`smallAutThinAt_of_all_discretize`); it can only fail where
individualization does not discretize. -/
def SmallAutThinAt (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
    (¬ Discrete (lookData adj χ u).col ∨ ¬ Discrete (lookData adj χ w).col) →
    keyV (leafColKey (n := n)) adj χ u ≠ keyV (leafColKey (n := n)) adj χ w

/-- The wall is **vacuous on the discretizing regime** — the discharged instance (R0a needs no wall there). -/
theorem smallAutThinAt_of_all_discretize (adj : AdjMatrix n) (χ : Colouring n)
    (hdisc : ∀ v ∈ branches χ, Discrete (lookData adj χ v).col) :
    SmallAutThinAt adj χ := by
  intro u hu w hw _ hnd
  rcases hnd with h | h
  · exact absurd (hdisc u hu) h
  · exact absurd (hdisc w hw) h

/-- **★★ R0b — `RigidResolved ⟸ hSmallAutThin` (the honest `modulo {wall}` end-state).** The force key `leafColKey`
separates ALL non-automorphic branch pairs, modulo exactly the shared wall `SmallAutThinAt`: the discretizing
pairs go through R0a unconditionally, the non-discretizing residual is the wall. -/
theorem rigidResolved_of_smallAutThin (adj : AdjMatrix n) (χ : Colouring n)
    (hwall : SmallAutThinAt adj χ) :
    RigidResolved (leafColKey (n := n)) adj χ := by
  intro u hu w hw hrig hkey
  by_cases hdu : Discrete (lookData adj χ u).col
  · by_cases hdw : Discrete (lookData adj χ w).col
    · obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w hdu hdw hkey
      exact hrig σ hσ hσuw
    · exact hwall u hu w hw hrig (Or.inr hdw) hkey
  · exact hwall u hu w hw hrig (Or.inl hdu) hkey

/-- **★★★ R0b → `NodeResolved` on ANY rigid cell (modulo the wall).** Generalises
`nodeResolved_leafColKey_of_rigid_discretizing` off the discretizing regime: a rigid branch cell resolves via
`leafColKey` modulo exactly `SmallAutThinAt`. On discretizing rigid cells the wall is vacuous
(`smallAutThinAt_of_all_discretize`), recovering R0a with no wall. -/
theorem nodeResolved_leafColKey_of_rigid (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n)
    (hnd : ¬ Discrete χ) (hwall : SmallAutThinAt adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (leafColKey (n := n)) S adj χ := by
  refine Select.nodeResolved_of_cellResolved hnd (Or.inr ?_)
  intro u hu w hw hkey
  by_contra hne
  exact rigidResolved_of_smallAutThin adj χ hwall u hu w hw (hrigid u hu w hw hne) hkey

/-! ## 9. The composite force key — the dischargeable seam (`compKey`)

**The design principle (the user's core).** *When the consume-side resolver cannot fire, the force-side resolver
must* — and the connection must be stated in a **dischargeable** form. `hSmallAutThin` is not that form (static
SRG-scheme predicate, false on consumable cases). The dischargeable form is a property of the **force key** we
build: on the discretizing branch, `leafColKey`'s complete coloured-pointed invariant (R0a, unconditional); on
the *non*-discretizing rigid branch — exactly where `leafColKey`'s histogram ties — call the **rigid solver's
canonical form** (`sk`, the future P3 output). The composite `compKey sk` tags the two regimes disjointly
(`1 ::` vs `0 ::`), so mixed pairs separate for free; the only carried obligation is that the solver key separates
the *both-non-discretizing* rigid pairs — `SolverSeparates`, discharged by the solver's soundness (P3), NOT by an
SRG citation.

`sk : Key n` is abstract here (the solver is P3, unbuilt). Its `KeyEquivariant` obligation is P3's
`Phase2.IsoInvariant` lifted to a key; its `SolverSeparates` obligation is P3's `Phase2.Sound`. Both are stubbed
as hypotheses; everything structural about the composite is proved now, axiom-clean. -/

/-- **The composite force key.** Discretizing branch → `leafColKey` (R0a, tagged `1 ::`); non-discretizing branch
→ the solver key `sk`, tagged `0 ::`. The disjoint tags mean a discretizing vertex never ties a non-discretizing
one, so the only real separation obligation is *both-non-discretizing* (`SolverSeparates`). -/
def compKey (sk : Key n) : Key n := fun adj χ v =>
  let ψ : Colouring n := (lookData adj χ v).col
  if Discrete ψ then leafColKey adj χ v
  else (0 :: (sk adj χ v).1, (sk adj χ v).2)

@[simp] theorem keyV_compKey (sk : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (compKey sk) adj χ v =
      (if Discrete (lookData adj χ v).col then keyV (leafColKey (n := n)) adj χ v
       else 0 :: keyV sk adj χ v) := by
  by_cases h : Discrete (lookData adj χ v).col
  · simp only [compKey, keyV, if_pos h]
  · simp only [compKey, keyV, if_neg h]

theorem keyV_compKey_disc (sk : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n)
    (h : Discrete (lookData adj χ v).col) :
    keyV (compKey sk) adj χ v = keyV (leafColKey (n := n)) adj χ v := by
  rw [keyV_compKey, if_pos h]

theorem keyV_compKey_not_disc (sk : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n)
    (h : ¬ Discrete (lookData adj χ v).col) :
    keyV (compKey sk) adj χ v = 0 :: keyV sk adj χ v := by
  rw [keyV_compKey, if_neg h]

/-- On the discretizing branch `leafColKey` heads with tag `1` — the disjointness with the non-discretizing
tag `0`. -/
theorem keyV_leafColKey_disc_head (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n)
    (h : Discrete (lookData adj χ v).col) :
    ∃ t, keyV (leafColKey (n := n)) adj χ v = 1 :: t := by
  rw [keyV_leafColKey, if_pos h]; exact ⟨_, rfl⟩

/-- **The composite key is equivariant, given the solver key is** (its `KeyEquivariant` obligation = P3's
`Phase2.IsoInvariant`). Discretizing branch reuses `keyEquivariant_leafColKey`; non-discretizing branch is the
tagged `sk` value. This is the ① obligation of the composite — structural, no solver internals. -/
theorem keyEquivariant_compKey (sk : Key n) (hsk : KeyEquivariant sk) :
    KeyEquivariant (compKey sk) := by
  intro σ adj χ v
  rw [keyV_compKey, keyV_compKey]
  simp only [lookData_col_transport σ adj χ v]
  by_cases hd : Discrete ((lookData adj χ v).col)
  · rw [if_pos ((discrete_transport σ _).mpr hd), if_pos hd]
    exact keyEquivariant_leafColKey σ adj χ v
  · rw [if_neg (fun hc => hd ((discrete_transport σ _).mp hc)), if_neg hd]
    exact congrArg (0 :: ·) (hsk σ adj χ v)

/-- **The dischargeable carried obligation** (replaces `SmallAutThinAt`). *The solver key separates every
both-non-discretizing non-automorphic branch pair.* This is a property of the **rigid solver** (`sk`), discharged
by its soundness (P3: distinct canonical forms for non-isomorphic pointed residues; a flag = the honest
non-linear residue), **not** an SRG-scheme citation like `hSmallAutThin`. The discretizing pairs (R0a) and the
mixed pairs (the `0/1` tag) need no hypothesis. -/
def SolverSeparates (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
    ¬ Discrete (lookData adj χ u).col → ¬ Discrete (lookData adj χ w).col →
    keyV key adj χ u ≠ keyV key adj χ w

/-- **★★ The composite key discharges `RigidResolved` modulo exactly `SolverSeparates` (the dischargeable seam).**
Every non-automorphic branch pair is separated by `compKey sk`: discretizing pairs via R0a (unconditional), mixed
pairs via the disjoint `0/1` tag (unconditional), both-non-discretizing pairs via `SolverSeparates` (the solver's
job, P3). The carried residual is now a property of the algorithm — dischargeable — not the static scheme wall. -/
theorem rigidResolved_compKey (sk : Key n) (adj : AdjMatrix n) (χ : Colouring n)
    (hsep : SolverSeparates (compKey sk) adj χ) :
    RigidResolved (compKey sk) adj χ := by
  intro u hu w hw hrig hkey
  by_cases hdu : Discrete (lookData adj χ u).col
  · by_cases hdw : Discrete (lookData adj χ w).col
    · -- both discretize: `compKey = leafColKey`, apply R0a
      rw [keyV_compKey_disc sk adj χ u hdu, keyV_compKey_disc sk adj χ w hdw] at hkey
      obtain ⟨σ, hσ, hσuw⟩ := colAut_of_leafColKey_eq adj χ u w hdu hdw hkey
      exact hrig σ hσ hσuw
    · -- mixed: `1 :: …` (u disc) vs `0 :: …` (w non-disc) — disjoint tags contradict `hkey`
      rw [keyV_compKey_disc sk adj χ u hdu, keyV_compKey_not_disc sk adj χ w hdw] at hkey
      obtain ⟨t, ht⟩ := keyV_leafColKey_disc_head adj χ u hdu
      rw [ht] at hkey
      exact absurd (List.cons.inj hkey).1 (by decide)
  · by_cases hdw : Discrete (lookData adj χ w).col
    · -- mixed (symmetric)
      rw [keyV_compKey_not_disc sk adj χ u hdu, keyV_compKey_disc sk adj χ w hdw] at hkey
      obtain ⟨t, ht⟩ := keyV_leafColKey_disc_head adj χ w hdw
      rw [ht] at hkey
      exact absurd (List.cons.inj hkey).1 (by decide)
    · -- both non-discretize: the dischargeable seam
      exact hsep u hu w hw hrig hdu hdw hkey

/-- **★★★ `compKey` → `NodeResolved` on ANY rigid cell (modulo `SolverSeparates`).** The composite-key analog of
`nodeResolved_leafColKey_of_rigid`: a rigid branch cell resolves via `compKey sk`, carrying only the dischargeable
`SolverSeparates` (the solver, P3). This is the force half of the "consume-can't-fire ⟹ force-fires" seam; the
consume half is the untouched `cellIsOrbit` disjunct of `Select.NodeResolved`. -/
theorem nodeResolved_compKey_of_rigid (sk : Key n) (S : Consume.Supply n) (adj : AdjMatrix n)
    (χ : Colouring n) (hnd : ¬ Discrete χ) (hsep : SolverSeparates (compKey sk) adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey sk) S adj χ := by
  refine Select.nodeResolved_of_cellResolved hnd (Or.inr ?_)
  intro u hu w hw hkey
  by_contra hne
  exact rigidResolved_compKey sk adj χ hsep u hu w hw (hrigid u hu w hw hne) hkey

end RigidSeal
end ChainDescent
