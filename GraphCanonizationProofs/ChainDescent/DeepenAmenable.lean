import ChainDescent.DeepenR1
import ChainDescent.OrbitPrune

/-!
# `C3b` tranche 2, part VI — Layer 1 foundations for `Amenable ⟹ R1`

R1's crux FACTORS (see `DeepenR1` header): `R1 ⟸ (Amenable ⟹ R1) + Amenable`, where `Amenable` says
every deepening level's `chooseIdK` cell is a single orbit of the pointwise-stabilizer of the
individualized-so-far. **Layer 1** (`Amenable ⟹ R1`) is the mechanical **re-relating induction**:

> the deepen-from-`a` and replay-from-`b` descents (`a ~ b` via `σ ∈ Aut`) stay related by an
> automorphism `σₖ ∈ Aut(adj)` with `ψ_b^(k) = transportColouring σₖ ψ_a^(k)`.

Maintained per level: `chooseIdK` picks the same id, so the selected cells are `σₖ`-images; the cell
being single-orbit under `Stab` (= `Amenable`) yields `τ ∈ Stab(ψ_b)` fixing the lowest-index mismatch
`τ (σₖ u_a) = u_b`, and `σₖ₊₁ := τ σₖ` re-establishes the invariant. At discreteness the leaves are
`σ`-related, so `twistOf`'s colour-match IS `σ` on all of `K`, hence the exec twist verifies and
directly reaches `b`.

This file lands the **transport atoms** the induction runs on. The atom is `step_aut`: an automorphism
of the graph transports one individualize+refine step between `σ`-related colourings — the level-to-level
engine. `transportColouring_comp` composes the per-level `σₖ`. (The full induction and the residual
K-coverage obligation — `SameOrbits` is over all vertices, the induction gives the branch cell — build
on these.)
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-- **Transported colourings compose.** `transportColouring σ χ = χ ∘ σ.symm`, so applying `τ` then
`σ`'s transport is the transport by `τ * σ` — this composes the per-level automorphisms `σₖ` the
re-relating induction threads. -/
theorem transportColouring_comp (σ τ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    transportColouring τ (transportColouring σ χ) = transportColouring (τ * σ) χ := by
  funext u
  simp only [transportColouring, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  rfl

/-- **★ THE TRANSPORT ATOM — an automorphism transports one deepening step.** `step_transport`
specialised at a graph-automorphism `σ` (`relabelAdj σ adj = adj`): individualizing `σ v` in the
`σ`-transported colouring and refining equals the `σ`-image of individualizing `v` in `χ` and refining.
No colouring-preservation is needed — the colouring is transported explicitly — so this fires for the
`σₖ` relating the two descents at every level, whatever the current colouring. -/
theorem step_aut {adj : AdjMatrix n} {σ : Equiv.Perm (Fin n)}
    (hadj : relabelAdj σ adj = adj) (χ : Colouring n) (v : Fin n) :
    (step adj (transportColouring σ χ) (σ v)).col
      = transportColouring σ ((step adj χ v).col) := by
  have h := step_transport σ adj χ v
  rw [hadj] at h
  exact h

/-- An `IsColAut` automorphism is in particular a graph-automorphism, so it transports a step; the
current colouring is transported explicitly (this is `step_aut` with the `IsColAut` witness supplying
`relabelAdj σ adj = adj`). -/
theorem step_isColAut {adj : AdjMatrix n} {χ : Colouring n} {σ : Equiv.Perm (Fin n)}
    (hσ : IsColAut adj χ σ) (ψ : Colouring n) (v : Fin n) :
    (step adj (transportColouring σ ψ) (σ v)).col
      = transportColouring σ ((step adj ψ v).col) :=
  step_aut hσ.relabel ψ v

/-- **★ THE RE-RELATING STEP — the induction invariant is maintained across one level.** The two
descents are `σ`-related (`ψ_b = transportColouring σ ψ_a`, `relabelAdj σ adj = adj`); at this level the
`b`-descent individualizes `u_b = τ(σ u_a)` where `τ ∈ Stab(ψ_b)` is the automorphism `Amenable` supplies
to absorb the lowest-index mismatch (`τ` maps `σ`'s image of `a`'s pick onto `b`'s pick, both in the same
single-orbit cell). Then the next colourings are `(τσ)`-related. This is the whole engine of Layer 1;
what remains is threading it through `deepen`/`replay`'s fuel recursion and the `deepenRefGens` plumbing. -/
theorem step_rerelate {adj : AdjMatrix n} {σ τ : Equiv.Perm (Fin n)} (ψa : Colouring n) (ua : Fin n)
    (hσ : relabelAdj σ adj = adj) (hτ : IsColAut adj (transportColouring σ ψa) τ) :
    (step adj (transportColouring σ ψa) (τ (σ ua))).col
      = transportColouring (τ * σ) ((step adj ψa ua).col) := by
  have h1 := step_aut hτ.relabel (transportColouring σ ψa) (σ ua)
  rw [hτ.transport] at h1
  rw [h1, step_aut hσ ψa ua, transportColouring_comp]

/-! ## 1b. Cell-transport helpers for the fuel induction

`deepen`/`replay` individualize the head of the id-`cid` cell `(finRange n).filter (χc · == cid)`.
Under a graph-automorphism the two descents' cells correspond by `σ` (up to `List.Perm`, index order),
exactly as `classOf` does — these are the lemmas the joint induction reads. -/

/-- The id-`cid` cell — the vertices `deepen` picks the head of. -/
def cidCell (χc : Colouring n) (cid : Nat) : List (Fin n) :=
  (List.finRange n).filter (fun v => χc v == cid)

theorem mem_cidCell_iff (χc : Colouring n) (cid : Nat) (u : Fin n) :
    u ∈ cidCell χc cid ↔ χc u = cid := by
  unfold cidCell; simp [List.mem_filter, List.mem_finRange]

theorem cidCell_nodup (χc : Colouring n) (cid : Nat) : (cidCell χc cid).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange n)

theorem mem_cidCell_transport (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (cid : Nat) (u : Fin n) :
    u ∈ cidCell (transportColouring σ χc) cid ↔ σ.symm u ∈ cidCell χc cid := by
  rw [mem_cidCell_iff, mem_cidCell_iff, transport_apply' σ χc u]

/-- **The id-cell transports up to permutation** (index order — same shape as `classOf_perm_transport`). -/
theorem cidCell_perm_transport (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (cid : Nat) :
    (cidCell (transportColouring σ χc) cid).Perm ((cidCell χc cid).map σ) := by
  apply (List.perm_ext_iff_of_nodup (cidCell_nodup _ _)
    (List.Nodup.map σ.injective (cidCell_nodup _ _))).mpr
  intro u
  rw [mem_cidCell_transport σ χc cid u, List.mem_map]
  constructor
  · intro h; exact ⟨σ.symm u, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- The id-cell's **membership** is `σ`-image: `σ` maps `a`'s id-cell onto `b`'s. -/
theorem mem_cidCell_transport_apply (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (cid : Nat)
    (u : Fin n) (h : u ∈ cidCell χc cid) : σ u ∈ cidCell (transportColouring σ χc) cid := by
  rw [mem_cidCell_transport]; simpa using h

/-- The id-cell **length** is invariant — so `a`'s cell is nonempty iff `b`'s is (replay can follow). -/
theorem cidCell_length_transport (σ : Equiv.Perm (Fin n)) (χc : Colouring n) (cid : Nat) :
    (cidCell (transportColouring σ χc) cid).length = (cidCell χc cid).length := by
  rw [(cidCell_perm_transport σ χc cid).length_eq, List.length_map]

/-! ## 1c. Refinement monotonicity — piece 1 of the fuel induction

The `τ` that `Amenable` supplies stabilizes the CURRENT colouring `ψ` (a refinement of the parent `χ`).
For the joint induction's invariant `σ' ∈ IsColAut adj χ` to survive `σ' ↦ τσ'`, that `τ` must also
stabilize the PARENT. It does, because a step only ever refines: `ψ x = ψ y ⟹ χ x = χ y`, and `IsColAut`'s
colour clause is `∀ v, χ (α v) = χ v`, so refinement transfers stabilization down to any coarsening. -/

/-- **`indivOne` refines its input.** Equal marked-colours ⟹ equal original colours (off the pin by
`indivOne_refines_off`; at the pin by `indivOne_singleton`). -/
theorem indivOne_refines (χ : Colouring n) (v : Fin n) {x y : Fin n}
    (h : Descend.indivOne χ v x = Descend.indivOne χ v y) : χ x = χ y := by
  by_cases hx : x = v <;> by_cases hy : y = v
  · rw [hx, hy]
  · rw [hx] at h; exact absurd h.symm (Descend.indivOne_singleton χ v y hy)
  · rw [hy] at h; exact absurd h (Descend.indivOne_singleton χ v x hx)
  · exact (Descend.indivOne_refines_off χ v x y hx hy).mp h

/-- **★ ONE STEP REFINES THE PARENT.** `step = warmRefineVec ∘ indivOne`; the warm round refines
(`refineSplits_encodeFreeFast`) and `indivOne` refines, so the composite does. -/
theorem step_refines (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) {x y : Fin n}
    (h : (step adj χ v).col x = (step adj χ v).col y) : χ x = χ y := by
  unfold step at h
  rw [Refine.warmRefineVec_col_eq, ← Refine.refineV_encodeFreeFast] at h
  exact indivOne_refines χ v (Refine.refineSplits_encodeFreeFast adj (Descend.indivOne χ v) x y h)

/-- **★ STABILIZATION TRANSFERS DOWN A REFINEMENT.** If `ψ` refines `χ`, a colour-automorphism of `ψ`
is one of `χ` — the adjacency clause is shared, the colour clause follows pointwise from `refines`. This
is what keeps the running composite `σ' = τσ` in the PARENT-stabilizer through the induction. -/
theorem isColAut_parent_of_refines {adj : AdjMatrix n} {χ ψ : Colouring n}
    (hrefine : ∀ x y, ψ x = ψ y → χ x = χ y) {τ : Equiv.Perm (Fin n)}
    (hτ : IsColAut adj ψ τ) : IsColAut adj χ τ :=
  ⟨hτ.1, fun v => hrefine (τ v) v (hτ.2 v)⟩

/-! ## 2. `Amenable`, the rigid obstruction, and the G2 attribution

`Amenable` is the domain hypothesis of Layer 1: every level of the canonical deepening individualizes a
cell that is a single orbit of the pointwise-stabilizer of the vertices fixed so far. Its NEGATION at a
cell is precisely a **rigid (non-symmetric) obstruction** — two same-colour vertices that no stabilizer
automorphism links. That is the **G2 attribution** the user asked for: we do not prove the path avoids
rigid cells (a final objective), we prove that a `CellSingleOrbit` FAILURE *is* a rigid obstruction, so
any ①c failure is attributable to the rigid side (force/rigid-solver's domain) at this stage. -/

/-- A colour class (`χc`-colour `cid`) is a **single orbit** of the stabilizer `IsColAut adj χc` — the
per-level requirement of `Amenable`. -/
def CellSingleOrbit (adj : AdjMatrix n) (χc : Colouring n) (cid : Nat) : Prop :=
  ∀ u w : Fin n, χc u = cid → χc w = cid → ∃ σ, IsColAut adj χc σ ∧ σ u = w

/-- A **rigid (non-symmetric) WL-obstruction** in the cell: two same-colour vertices that NO stabilizer
automorphism links — a 1-WL-merged non-automorphic pair. This is exactly what force / the rigid solver
own (the linear part) or the wall (the non-linear part); `deepen` correctly emit-nothings here. -/
def RigidObstructionAt (adj : AdjMatrix n) (χc : Colouring n) (cid : Nat) : Prop :=
  ∃ u w : Fin n, χc u = cid ∧ χc w = cid ∧ ∀ σ, IsColAut adj χc σ → σ u ≠ w

/-- **★ THE G2 ATTRIBUTION (cell level).** A `CellSingleOrbit` failure *is* a rigid obstruction — the
negation is definitional (de Morgan). So an `Amenable` violation is never a mystery: it localises to a
same-colour non-automorphic pair = the rigid side's responsibility. -/
theorem rigidObstruction_of_not_cellSingleOrbit (adj : AdjMatrix n) (χc : Colouring n) (cid : Nat)
    (h : ¬ CellSingleOrbit adj χc cid) : RigidObstructionAt adj χc cid := by
  unfold CellSingleOrbit at h
  push_neg at h
  obtain ⟨u, w, hu, hw, hσ⟩ := h
  exact ⟨u, w, hu, hw, hσ⟩

/-- **`Amenable` along one anchor's deepening path.** Every level that individualizes a cell (`chooseIdK
= some cid`) requires that cell to be a single stabilizer-orbit. Mirrors `deepen`'s recursion exactly. -/
def AmenablePath (adj : AdjMatrix n) (χp : Colouring n) :
    Nat → Refine.ColData n → Prop
  | 0, _ => True
  | fuel + 1, cur =>
      let χc := cur.col
      let K := coupled χp χc
      if K.isEmpty then True
      else match chooseIdK K χc with
        | none => True
        | some cid =>
            CellSingleOrbit adj χc cid ∧
            (match (List.finRange n).filter (fun v => χc v == cid) with
             | [] => True
             | w :: _ => AmenablePath adj χp fuel (step adj χc w))

/-- **`Amenable`** — the Layer-1 domain hypothesis: every anchor's canonical deepening individualizes
only single-orbit cells. `Amenable ⟹ R1` is the re-relating induction (Layer 1, on `step_aut`); its
complement is a rigid obstruction (`rigidObstruction_of_not_cellSingleOrbit`). -/
def Amenable (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ r ∈ Descend.branches χ, AmenablePath adj χ n (step adj χ r)

/-- **★ `CellSingleOrbit` TRANSPORTS under an automorphism (piece 2a).** `b`'s id-cell is the σ-image
of `a`'s and its stabilizer is the σ-conjugate, so a single orbit stays a single orbit. This is why
`Amenable` (stated about the `a`-descent) delivers the `τ ∈ Stab(cur_b.col)` the re-relating step needs
on the `b`-descent. Uses `Consume.isColAut_conj_iff` (the verification check conjugates). -/
theorem cellSingleOrbit_transport {adj : AdjMatrix n} {χc : Colouring n} {σ : Equiv.Perm (Fin n)}
    (hσ : relabelAdj σ adj = adj) {cid : Nat} (h : CellSingleOrbit adj χc cid) :
    CellSingleOrbit adj (transportColouring σ χc) cid := by
  intro u' w' hu' hw'
  have hu : χc (σ.symm u') = cid := hu'
  have hw : χc (σ.symm w') = cid := hw'
  obtain ⟨ρ, hρ, hρuw⟩ := h (σ.symm u') (σ.symm w') hu hw
  refine ⟨σ * ρ * σ⁻¹, ?_, ?_⟩
  · have hc := (Consume.isColAut_conj_iff σ (adj := adj) (χ := χc) (α := ρ)).mpr hρ
    rwa [hσ] at hc
  · show σ (ρ (σ.symm u')) = w'
    rw [hρuw]; exact Equiv.apply_symm_apply σ w'

/-! ## 3. The capstone — `(R1 ∧ R2) → ①c`, and the `Amenable`-gated form

Mirrors `KernelTransport.kernelSupply_guarded_canonizer`: ①c for the executable `deepenSupply` is
`OrbitPrune.guarded_mixed_canonizer_of_sameOrbits` applied to `KeyEquivariant` (lookahead) + the
reference's equivariance (**R2**) + `SameOrbits` (**R1**, via `sameOrbits_of_core`). The two open links
enter as explicit hypotheses — exactly the project's gate-conditional pattern. **G1** (rigid ⟹ F_k, the
shared wall) is NOT a hypothesis here: ①c needs only `Amenable`; G1 lives at the totality layer (it says
the rigid cells `deepen` defers on are the rigid solver's, so the whole canonizer stays total). -/

/-- **★★ `(R1 ∧ R2) → ①c` for `deepenSupply`.** `hcore` is R1 (`DeepenRefInExec`, discharged from
`Amenable` by the Layer-1 induction); `hR2` is R2 (`deepenRefSupply` equivariant). No other assumption. -/
theorem deepenSupply_guarded_canonizer_of
    (hR2 : SupplyTransport.SupplyEquivariant (deepenRefSupply (n := n)))
    (hcore : ∀ (adj : AdjMatrix n) (χ : Colouring n), DeepenRefInExec adj χ) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupply (n := n))))) :=
  OrbitPrune.guarded_mixed_canonizer_of_sameOrbits Force.keyEquivariant_lookahead
    hR2 (sameOrbits_of_core hcore)

/-- **★★ The `Amenable`-gated form — `(Amenable ∧ L1 ∧ R2) → ①c`.** Factors R1 through the domain
hypothesis: `hL1` is the Layer-1 induction (`Amenable ⟹ R1`, on `step_aut`), `hAmen` the domain fact
(discharged by the WL-obstruction classification: rigid cells are force/rigid-solver's, per G1). -/
theorem deepenSupply_canonizer_of_amenable
    (hR2 : SupplyTransport.SupplyEquivariant (deepenRefSupply (n := n)))
    (hL1 : ∀ (adj : AdjMatrix n) (χ : Colouring n), Amenable adj χ → DeepenRefInExec adj χ)
    (hAmen : ∀ (adj : AdjMatrix n) (χ : Colouring n), Amenable adj χ) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupply (n := n))))) :=
  deepenSupply_guarded_canonizer_of hR2 (fun adj χ => hL1 adj χ (hAmen adj χ))

end Deepen
end ChainDescent
