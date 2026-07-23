import ChainDescent.DeepenCrux
import ChainDescent.SupplyTransport
import ChainDescent.Composite
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

/-- **★ ANCHOR ATOM — a colour-automorphism fixes a singleton-colour vertex.** If `v` is the unique
vertex of colour `ψ v`, any `IsColAut adj ψ τ` fixes `v` (`τ v` has the same colour, so `= v`). This is
the engine of anchor-tracking: the individualized rep stays put under every per-level `τ ∈ Stab`. -/
theorem isColAut_fixes_singleton {adj : AdjMatrix n} {ψ : Colouring n} {τ : Equiv.Perm (Fin n)}
    (hτ : IsColAut adj ψ τ) {v : Fin n} (hv : ∀ u, ψ u = ψ v → u = v) : τ v = v :=
  hv (τ v) (hτ.2 v)

/-- **★ ANCHOR ATOM — a step preserves a singleton.** `step` only refines, so a vertex that is the
unique carrier of its colour stays unique. Keeps the anchor a singleton through the deepening. -/
theorem step_preserves_singleton (adj : AdjMatrix n) (ψ : Colouring n) {v : Fin n}
    (hv : ∀ u, ψ u = ψ v → u = v) (w : Fin n) :
    ∀ u, (step adj ψ w).col u = (step adj ψ w).col v → u = v :=
  fun u h => hv u (step_refines adj ψ w h)

/-- **★ ANCHOR ATOM — the individualized vertex is a singleton after a step.** `step adj χ v`
individualizes `v` (a singleton by `indivOne_singleton`) then refines (which only splits), so `v` is the
unique carrier of its colour in `(step adj χ v).col`. This is the base of anchor-tracking: `step χ r`
makes the anchor `r` a protected singleton. -/
theorem step_indiv_singleton (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    ∀ u, (step adj χ v).col u = (step adj χ v).col v → u = v := by
  intro u h
  unfold step at h
  rw [Refine.warmRefineVec_col_eq, ← Refine.refineV_encodeFreeFast] at h
  have hi := Refine.refineSplits_encodeFreeFast adj (Descend.indivOne χ v) u v h
  by_contra hne
  exact absurd hi (Descend.indivOne_singleton χ v u hne)

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
      match chooseIdK (List.finRange n) χc with
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

/-! ## 2c. `deepen` structural lemmas for the joint fuel induction (piece 2b) -/

/-- **The accumulator only prefixes the output.** `deepen … acc` returns the same leaf as `deepen … []`
with `acc.reverse` prepended to the recorded id sequence. Lets the joint induction work at `acc = []`
(the recursion's `[cid]` accumulator becomes `cid ::` on the sequence). -/
theorem deepen_acc (adj : AdjMatrix n) (χp : Colouring n) (fuel : Nat) :
    ∀ (cur : Refine.ColData n) (acc : List Nat),
      deepen adj χp fuel cur acc
        = (deepen adj χp fuel cur []).map (fun p => (p.1, acc.reverse ++ p.2)) := by
  induction fuel with
  | zero => intro cur acc; rfl
  | succ fuel ih =>
      intro cur acc
      unfold deepen
      dsimp only
      generalize chooseIdK (List.finRange n) cur.col = co
      cases co with
      | none => simp
      | some cid =>
          dsimp only
          split
          · rfl
          · rename_i _ w _ _
            rw [ih (step adj cur.col w) (cid :: acc), ih (step adj cur.col w) [cid],
                Option.map_map]
            congr 1
            funext p
            simp [Function.comp, List.reverse_cons, List.append_assoc]

/-- The `chooseIdK` fold takes a `min` over `χc v` of the `classOf ≥ 2` cells, so its `some` result is
`χc v` for one such `v` (the argmin). A `foldl`-min "result is an element" lemma. -/
theorem foldl_min_mem (χc : Colouring n) {cid : Nat} :
    ∀ (L : List (Fin n)) (acc : Option Nat),
      (L.foldl (fun acc v => match acc with
        | none => some (χc v) | some m => some (min m (χc v))) acc = some cid) →
      acc = some cid ∨ ∃ v ∈ L, χc v = cid := by
  intro L
  induction L with
  | nil => intro acc h; left; simpa using h
  | cons v L ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with h' | ⟨w, hw, hwc⟩
      · cases acc with
        | none => right; exact ⟨v, List.mem_cons_self .., by simpa using h'⟩
        | some m =>
            simp only [Option.some.injEq] at h'
            rcases Nat.le_total m (χc v) with hle | hle
            · left; rw [Nat.min_eq_left hle] at h'; rw [h']
            · right; exact ⟨v, List.mem_cons_self .., by rw [Nat.min_eq_right hle] at h'; exact h'⟩
      · right; exact ⟨w, List.mem_cons_of_mem _ hw, hwc⟩

/-- **★ b1 — `chooseIdK` picks a `≥ 2` cell.** `chooseIdK K χc = some cid ⟹ (cidCell χc cid).length ≥ 2`.
So on the `b`-descent `replay`'s `mem.length < 2` guard passes (via `cidCell_length_transport`). -/
theorem chooseIdK_mem (K : List (Fin n)) (χc : Colouring n) {cid : Nat}
    (h : chooseIdK K χc = some cid) : 2 ≤ (cidCell χc cid).length := by
  unfold chooseIdK at h
  rcases foldl_min_mem χc _ none h with h' | ⟨v, hv, hvc⟩
  · exact absurd h' (by simp)
  · rw [List.mem_filter] at hv
    have hlen : 2 ≤ (classOf χc v).length := by simpa using hv.2
    have hcell : cidCell χc cid = classOf χc v := by
      unfold cidCell classOf; congr 1; funext u; rw [hvc]
    rw [hcell]; exact hlen

/-- **★★ b2 — THE JOINT RE-RELATING INDUCTION (canonical paths).** Under `Amenable`, the canonical
`deepen`-from-`a` and canonical `replay`-from-`b` (with `b`-state the `σ`-transport of `a`-state, `σ` a
parent-automorphism) reach leaves related by an automorphism `σ'` via the WHOLE-COLOURING transport
equation. So the emitted twist is a genuine graph-automorphism on all of `K` (K-coverage is subsumed —
the relation is over every vertex, validated 2026-07-22). Each level: `chooseIdK_mem`+
`cidCell_length_transport` pass replay's `≥2` guard; `cellSingleOrbit_transport`+`Amenable` supply
`τ ∈ Stab(cur_b.col)` absorbing the pick mismatch; `step_rerelate` carries the invariant; `step_refines`+
`isColAut_parent_of_refines` keep `τσ` in the parent-stabilizer. -/
theorem joint (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur_a cur_b : Refine.ColData n) (σ : Equiv.Perm (Fin n)) (a₀ : Fin n),
      IsColAut adj χp σ →
      cur_b.col = transportColouring σ cur_a.col →
      (∀ x y, cur_a.col x = cur_a.col y → χp x = χp y) →
      (∀ x y, cur_b.col x = cur_b.col y → χp x = χp y) →
      (∀ u, cur_b.col u = cur_b.col (σ a₀) → u = σ a₀) →
      AmenablePath adj χp fuel cur_a →
      ∀ (leaf_a : Refine.ColData n) (seq : List Nat),
        deepen adj χp fuel cur_a [] = some (leaf_a, seq) →
        ∃ (σ' : Equiv.Perm (Fin n)) (leaf_b : Refine.ColData n),
          IsColAut adj χp σ' ∧ replay adj seq cur_b = some leaf_b ∧
          leaf_b.col = transportColouring σ' leaf_a.col ∧ σ' a₀ = σ a₀ := by
  intro fuel
  induction fuel with
  | zero => intro cur_a cur_b σ a₀ _ _ _ _ _ _ leaf_a seq h; simp [deepen] at h
  | succ fuel ih =>
      intro cur_a cur_b σ a₀ hσ hrel hrefa hrefb hb0 hAmen leaf_a seq h
      -- reduce `deepen (fuel+1) cur_a []`
      unfold deepen at h
      dsimp only at h
      -- the id `chooseIdK` picks (over the WHOLE graph — track A: discretize everything)
      cases hco : chooseIdK (List.finRange n) cur_a.col with
      | none =>
          -- `chooseIdK = none` is the terminal LEAF (whole graph discrete)
          rw [hco] at h
          dsimp only at h
          simp only [List.reverse_nil, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨σ, cur_b, hσ, rfl, hrel, rfl⟩
      | some cid =>
          rw [hco] at h
          dsimp only at h
          -- `a`'s id-cell (= the deepen/AmenablePath filter, defeq `cidCell`)
          cases hfl : (List.finRange n).filter (fun v => cur_a.col v == cid) with
          | nil => rw [hfl] at h; simp at h
          | cons w_a rest_a =>
              rw [hfl] at h
              dsimp only at h
              -- deepen recurses on `step cur_a.col w_a` with accumulator `[cid]`
              rw [deepen_acc adj χp fuel (step adj cur_a.col w_a) [cid]] at h
              rw [Option.map_eq_some_iff] at h
              obtain ⟨⟨la, inner⟩, hinner, heq⟩ := h
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
                Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              -- so leaf_a = la, seq = cid :: inner
              -- `w_a` is the head of `a`'s id-cell
              have hwa_mem : w_a ∈ cidCell cur_a.col cid := by
                show w_a ∈ (List.finRange n).filter (fun v => cur_a.col v == cid)
                rw [hfl]; exact List.mem_cons_self ..
              -- `chooseIdK_mem`: `a`'s id-cell has ≥ 2, so does `b`'s
              have hlen_a : 2 ≤ (cidCell cur_a.col cid).length := chooseIdK_mem _ _ hco
              have hlen_b : 2 ≤ (cidCell cur_b.col cid).length := by
                rw [hrel, cidCell_length_transport]; exact hlen_a
              -- head `w_b` of `b`'s id-cell
              obtain ⟨w_b, rest_b, hmb⟩ :
                  ∃ w_b rest_b, cidCell cur_b.col cid = w_b :: rest_b := by
                cases hmb : cidCell cur_b.col cid with
                | nil => rw [hmb] at hlen_b; simp at hlen_b
                | cons w_b rest_b => exact ⟨w_b, rest_b, rfl⟩
              have hwb_mem : w_b ∈ cidCell cur_b.col cid := by rw [hmb]; exact List.mem_cons_self ..
              -- unpack `Amenable` at this level
              unfold AmenablePath at hAmen
              dsimp only at hAmen
              rw [hco] at hAmen
              dsimp only at hAmen
              rw [hfl] at hAmen
              dsimp only at hAmen
              obtain ⟨hcell_a, hAmen_rec⟩ := hAmen
              -- transport the single-orbit cell to `b`, get `τ`
              have hcell_b : CellSingleOrbit adj cur_b.col cid := by
                rw [hrel]; exact cellSingleOrbit_transport hσ.relabel hcell_a
              have hσwa : cur_b.col (σ w_a) = cid := by
                have : σ w_a ∈ cidCell cur_b.col cid := by
                  rw [hrel]; exact mem_cidCell_transport_apply σ cur_a.col cid w_a hwa_mem
                exact (mem_cidCell_iff _ _ _).mp this
              have hwbcid : cur_b.col w_b = cid := (mem_cidCell_iff _ _ _).mp hwb_mem
              obtain ⟨τ, hτ, hτeq⟩ := hcell_b (σ w_a) w_b hσwa hwbcid
              -- `τ ∈ Stab(cur_b.col)` transfers to the parent, and `τσ` is a parent-automorphism
              have hτp : IsColAut adj χp τ := isColAut_parent_of_refines hrefb hτ
              have hτσ : IsColAut adj χp (τ * σ) := hτp.comp hσ
              -- the invariant across this level (`step_rerelate`)
              have hτ' : IsColAut adj (transportColouring σ cur_a.col) τ := by rw [← hrel]; exact hτ
              have hstep_rel : (step adj cur_b.col w_b).col
                  = transportColouring (τ * σ) (step adj cur_a.col w_a).col := by
                have hr := step_rerelate cur_a.col w_a hσ.relabel hτ'
                rw [hτeq] at hr
                rw [hrel]; exact hr
              -- parent-refinement survives a step, both sides
              have hrefa' : ∀ x y, (step adj cur_a.col w_a).col x = (step adj cur_a.col w_a).col y
                  → χp x = χp y := fun x y hxy => hrefa x y (step_refines adj cur_a.col w_a hxy)
              have hrefb' : ∀ x y, (step adj cur_b.col w_b).col x = (step adj cur_b.col w_b).col y
                  → χp x = χp y := fun x y hxy => hrefb x y (step_refines adj cur_b.col w_b hxy)
              -- the recursive Amenable premise
              have hAmen' : AmenablePath adj χp fuel (step adj cur_a.col w_a) := hAmen_rec
              -- ANCHOR TRACKING: `τ` fixes the protected singleton `σ a₀`, so `(τσ) a₀ = σ a₀`,
              -- and it stays a singleton after the step
              have hτfix : τ (σ a₀) = σ a₀ := isColAut_fixes_singleton hτ hb0
              have hnew_a0 : (τ * σ) a₀ = σ a₀ := by rw [Equiv.Perm.mul_apply]; exact hτfix
              have hb0' : ∀ u, (step adj cur_b.col w_b).col u
                  = (step adj cur_b.col w_b).col ((τ * σ) a₀) → u = (τ * σ) a₀ := by
                rw [hnew_a0]; exact step_preserves_singleton adj cur_b.col hb0 w_b
              -- apply IH on the `b`-side head `w_b`
              obtain ⟨σ', leaf_b, hσ', hrepl, hleaf, ha0⟩ :=
                ih (step adj cur_a.col w_a) (step adj cur_b.col w_b) (τ * σ) a₀ hτσ
                  hstep_rel hrefa' hrefb' hb0' hAmen' la inner hinner
              -- reduce `replay (cid :: inner) cur_b` to the recursive replay on `w_b`
              refine ⟨σ', leaf_b, hσ', ?_, hleaf, ha0.trans hnew_a0⟩
              show replay adj (cid :: inner) cur_b = some leaf_b
              unfold replay
              dsimp only
              rw [show (List.finRange n).filter (fun v => cur_b.col v == cid) = w_b :: rest_b from hmb,
                  if_neg (by
                    have hle : ¬ (w_b :: rest_b).length < 2 := by
                      have hlift : (w_b :: rest_b).length = (cidCell cur_b.col cid).length := by rw [hmb]
                      rw [hlift]; exact Nat.not_lt.mpr hlen_b
                    exact hle)]
              exact hrepl

/-! ## 2d. Piece 3 — `twistOf` verifies from the σ-relation

`joint` delivers `χj = transportColouring σ_final χ1` with `σ_final ∈ IsColAut adj χ` (whole-colouring).
Piece 3 turns that into the exec generator: `twistOf` reconstructs `σ_final` on `K`. The `allSingletonsK`
gate makes each `χ1`-colour GLOBALLY unique (`classOf` length 1 over all `finRange`), so the colour-match
is forced; when `σ'` fixes off-`K` (empirically always — every measured witness has support `= K`), the
match IS `σ'` and `twistOf = some σ'`. -/

/-- **Gate ⟹ global colour-uniqueness.** For `v ∈ K` under the all-singletons gate, `χ1 v` is unique in
the WHOLE graph: `χ1 u = χ1 v ⟹ u = v`. (`classOf` filters `finRange`, so length 1 pins `v` globally.) -/
theorem gate_unique {χ1 : Colouring n} {K : List (Fin n)} (hgate : allSingletonsK K χ1 = true)
    {v : Fin n} (hv : v ∈ K) {u : Fin n} (hu : χ1 u = χ1 v) : u = v := by
  have h1 : (classOf χ1 v).length = 1 := by
    have hb : ((classOf χ1 v).length == 1) = true := List.all_eq_true.mp hgate v hv
    simpa using hb
  obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp h1
  have hmemv : v ∈ classOf χ1 v := by
    unfold classOf; simp [List.mem_filter, List.mem_finRange]
  have hmemu : u ∈ classOf χ1 v := by
    unfold classOf; simp [List.mem_filter, List.mem_finRange, hu]
  rw [hw, List.mem_singleton] at hmemv hmemu
  exact hmemu.trans hmemv.symm

/-- **★ Piece 3 — `twistOf` reconstructs `σ'`.** Under the gate, with `σ'` an `IsColAut` that fixes off
`K` (so it permutes `K`), `imgFun`'s colour-match against `transportColouring σ' χ1` IS `σ'`, so
`twistOf adj χ χ1 K (transportColouring σ' χ1) = some σ'`. The exec generator for the σ-related pair. -/
theorem twistOf_of_transport_fixing {adj : AdjMatrix n} {χ χ1 : Colouring n} {K : List (Fin n)}
    {σ' : Equiv.Perm (Fin n)} (hgate : allSingletonsK K χ1 = true)
    (hfix : ∀ v, K.contains v = false → σ' v = v) (hσ' : IsColAut adj χ σ') :
    twistOf adj χ χ1 K (transportColouring σ' χ1) = some σ' := by
  -- `σ'` maps `K` into `K` (its complement is fixed)
  have hKclosed : ∀ v, v ∈ K → σ' v ∈ K := by
    intro v hv
    by_contra hnv
    have hc : K.contains (σ' v) = false := by
      rw [List.contains_eq_mem]; exact decide_eq_false hnv
    have h1 : σ' (σ' v) = σ' v := hfix _ hc
    have h2 : σ' v = v := σ'.injective h1
    rw [h2] at hnv; exact hnv hv
  -- the colour-match image function equals `σ'`
  have himg : imgFun χ1 K (transportColouring σ' χ1) = fun v => σ' v := by
    funext v
    unfold imgFun
    by_cases hc : K.contains v
    · rw [if_pos hc]
      have hvK : v ∈ K := by
        have h := hc; rw [List.contains_eq_mem] at h; exact of_decide_eq_true h
      have hσvK : σ' v ∈ K := hKclosed v hvK
      -- `σ' v` satisfies the find? predicate, and is the unique such member
      have hpred : (transportColouring σ' χ1 (σ' v) == χ1 v) = true := by
        have : transportColouring σ' χ1 (σ' v) = χ1 v := by
          show χ1 (σ'.symm (σ' v)) = χ1 v; rw [Equiv.symm_apply_apply]
        simp [this]
      cases hf : K.find? (fun w => transportColouring σ' χ1 w == χ1 v) with
      | none =>
          exfalso
          have hsome : (K.find? (fun w => transportColouring σ' χ1 w == χ1 v)).isSome := by
            rw [List.find?_isSome]; exact ⟨σ' v, hσvK, hpred⟩
          rw [hf] at hsome; simp at hsome
      | some u =>
          have hupred : (transportColouring σ' χ1 u == χ1 v) = true := by
            have h := List.find?_some (p := fun w => transportColouring σ' χ1 w == χ1 v) hf
            simpa using h
          have hueq : χ1 (σ'.symm u) = χ1 v := by simpa [transportColouring] using hupred
          have : σ'.symm u = v := gate_unique hgate hvK hueq
          have : u = σ' v := by rw [← this]; exact (Equiv.apply_symm_apply σ' u).symm
          simp [this]
    · rw [if_neg hc]
      exact (hfix v (by simpa using hc)).symm
  -- `permOf` reads it back as `σ'`, and the `IsColAut` gate passes
  rw [twistOf_eq_imgFun, himg]
  have hpm : Deck2.permOf (fun v => (σ' : Fin n → Fin n) v) = some σ' :=
    Deck2.permOf_eq_some_of_eq (fun _ => rfl)
  rw [hpm]
  simp [hσ']

/-! ## 2e. Reference-gen bridge infrastructure (the `hL1 ⟸ ORBIT_K` reduction, §9.1.1)

Clean, `hfix`-independent pieces the bridge reduction runs on: reference gens are `IsColAut` (so a ref
gen's action is an automorphism), and `twistOf` is the identity off `K` (so `∀ x` is `refl` off `K`,
leaving only `x ∈ K`). -/

/-- `permOf` forward: if it gates to `ρ`, then `ρ` IS the input function pointwise. -/
theorem permOf_apply {f : Fin n → Fin n} {ρ : Equiv.Perm (Fin n)}
    (h : Deck2.permOf f = some ρ) (v : Fin n) : ρ v = f v := by
  unfold Deck2.permOf at h
  split at h
  · rw [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

/-- **`twistOf` is the identity off `K`.** So a reference generator moves nothing outside its coupled
component, and `DeepenRefInExec`'s `∀ x` is `refl` for `x ∉ K`. -/
theorem twistOf_id_off_K {adj : AdjMatrix n} {χ χ1 : Colouring n} {K : List (Fin n)} {χj : Colouring n}
    {ρ : Equiv.Perm (Fin n)} (h : twistOf adj χ χ1 K χj = some ρ)
    {v : Fin n} (hv : K.contains v = false) : ρ v = v := by
  rw [twistOf_eq_imgFun] at h
  cases hp : Deck2.permOf (imgFun χ1 K χj) with
  | none => rw [hp] at h; simp at h
  | some ρ' =>
      rw [hp] at h
      dsimp only at h
      by_cases hia : decide (IsColAut adj χ ρ') = true
      · rw [if_pos hia, Option.some.injEq] at h
        subst h
        rw [permOf_apply hp v]
        unfold imgFun; rw [if_neg (by rw [hv]; simp)]
      · rw [if_neg hia] at h; exact absurd h (by simp)

/-- **Forward membership in `deepenGens`** — reconstructs that the twist for anchor `r₁`, rep `rⱼ` is an
emitted executable generator, from the pipeline facts (deepen succeeds, gate passes, replay succeeds,
twist verifies). The structural half of the branch-cell reachability. -/
theorem mem_deepenGens_of (adj : AdjMatrix n) (χ : Colouring n) {r₁ rⱼ : Fin n}
    {d1 dj : Refine.ColData n} {seq : List Nat} {g : Equiv.Perm (Fin n)}
    (hr1 : r₁ ∈ Descend.branches χ) (hrj : rⱼ ∈ Descend.branches χ) (hne : (rⱼ == r₁) = false)
    (hdeepen : deepen adj χ n (step adj χ r₁) [] = some (d1, seq))
    (hgate : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false)
    (hrepl : replay adj seq (step adj χ rⱼ) = some dj)
    (htwist : twistOf adj χ d1.col (coupled χ d1.col) dj.col = some g) :
    g ∈ deepenGens adj χ := by
  unfold deepenGens
  dsimp only
  rw [List.mem_flatMap]
  refine ⟨(r₁, step adj χ r₁), List.mem_map.mpr ⟨r₁, hr1, rfl⟩, ?_⟩
  dsimp only
  rw [hdeepen]
  dsimp only
  rw [if_neg (by rw [hgate]; simp)]
  rw [List.mem_filterMap]
  refine ⟨(rⱼ, step adj χ rⱼ), List.mem_map.mpr ⟨rⱼ, hrj, rfl⟩, ?_⟩
  dsimp only
  rw [if_neg (by rw [hne]; simp), hrepl]
  exact htwist

/-- A colour-automorphism leaves its colouring transport-invariant: `transportColouring t χ = χ`. -/
theorem transportColouring_isColAut {adj : AdjMatrix n} {χ : Colouring n} {t : Equiv.Perm (Fin n)}
    (ht : IsColAut adj χ t) : transportColouring t χ = χ := by
  funext u
  show χ (t.symm u) = χ u
  have h := ht.2 (t.symm u)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Elements of a list of length `≤ 1` are all equal. -/
theorem eq_of_mem_of_length_le_one {α : Type*} {l : List α}
    (h : l.length ≤ 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  cases l with
  | nil => simp at ha
  | cons x t =>
    cases t with
    | nil => rw [List.mem_singleton] at ha hb; rw [ha, hb]
    | cons y s => simp only [List.length_cons] at h; omega

/-- **`[DISC] ⟹ [INV]` — off the coupled component, every vertex is a `χ`-singleton.** When the leaf
colouring `χc` is discrete (the whole-graph discretization measured on every firing witness), a vertex `w`
whose `χ`-cell does not split under `χc` (`w ∉ coupled χ χc`) is alone in its `χ`-cell: the cell has a
CONSTANT `χc` value (that is what `∉ coupled` means), and discreteness collapses a constant-`χc` set to a
single vertex. Discharges the `hinv`/`[INV]` hypothesis of `exec_recovers_cell_orbits` from the single
domain fact `[DISC]`. -/
theorem offCoupled_singleton {χ χc : Colouring n} (hdisc : Discrete χc) {w : Fin n}
    (hw : (coupled χ χc).contains w = false) :
    ∀ u, χ u = χ w → u = w := by
  intro u huw
  have hnm : w ∉ coupled χ χc := by
    rw [List.contains_eq_mem] at hw; exact of_decide_eq_false hw
  -- `w ∉ coupled` unfolds to: its `χ`-cell, mapped through `χc`, dedups to `≤ 1` value
  have hlen : (((List.finRange n).filter (fun z => χ z == χ w)).map χc).dedup.length ≤ 1 := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    exact hnm (by rw [coupled, List.mem_filter]; exact ⟨List.mem_finRange w, by simpa using hcon⟩)
  -- `u` and `w` both lie in that `χ`-cell, so their `χc` values coincide in the deduped list
  have hu : u ∈ (List.finRange n).filter (fun z => χ z == χ w) :=
    List.mem_filter.mpr ⟨List.mem_finRange u, by simp [huw]⟩
  have hwm : w ∈ (List.finRange n).filter (fun z => χ z == χ w) :=
    List.mem_filter.mpr ⟨List.mem_finRange w, by simp⟩
  have hcu : χc u ∈ (((List.finRange n).filter (fun z => χ z == χ w)).map χc).dedup :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨u, hu, rfl⟩)
  have hcw : χc w ∈ (((List.finRange n).filter (fun z => χ z == χ w)).map χc).dedup :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨w, hwm, rfl⟩)
  exact hdisc u w (eq_of_mem_of_length_le_one hlen hcu hcw)

/-- **★★ THE BRANCH-CELL HALF — `exec_recovers_cell_orbits`.** For anchor `r₁` and rep `rⱼ` in the branch
cell related by a colour-automorphism `t` (`t r₁ = rⱼ`), the executable emits a verified generator mapping
`r₁ ↦ rⱼ`, so `WordReach exec r₁ rⱼ`. Assembles `joint` (anchor-tracking gives `σf r₁ = rⱼ`) + piece 3
(`twistOf = some σf`, `hfix` from `[INV]`) + `mem_deepenGens_of`. Carries the firing/domain facts: `deepen`
succeeds, the gate passes, `Amenable`, and **`[INV]`** (off the coupled component every vertex is a
`χ`-singleton — the discharge `[DISC] ⟹ [INV]` is the deferred `offCoupled_singleton`). -/
theorem exec_recovers_cell_orbits (adj : AdjMatrix n) (χ : Colouring n) {r₁ rⱼ : Fin n}
    {d1 : Refine.ColData n} {seq : List Nat} {t : Equiv.Perm (Fin n)}
    (hr1 : r₁ ∈ Descend.branches χ) (hrj : rⱼ ∈ Descend.branches χ) (hne : (rⱼ == r₁) = false)
    (ht : IsColAut adj χ t) (htrj : t r₁ = rⱼ)
    (hdeepen : deepen adj χ n (step adj χ r₁) [] = some (d1, seq))
    (hgate : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false)
    (hAmen : AmenablePath adj χ n (step adj χ r₁))
    (hdisc : Discrete d1.col) :
    Consume.WordReach (Consume.verified deepenSupply adj χ) r₁ rⱼ := by
  -- `b`-state is the `t`-transport of `a`-state
  have hrel : (step adj χ rⱼ).col = transportColouring t (step adj χ r₁).col := by
    have hs := step_isColAut ht χ r₁
    rw [transportColouring_isColAut ht, htrj] at hs; exact hs
  -- refinement + protected-singleton invariants for `joint`
  have hrefa : ∀ x y, (step adj χ r₁).col x = (step adj χ r₁).col y → χ x = χ y :=
    fun x y h => step_refines adj χ r₁ h
  have hrefb : ∀ x y, (step adj χ rⱼ).col x = (step adj χ rⱼ).col y → χ x = χ y :=
    fun x y h => step_refines adj χ rⱼ h
  have hb0 : ∀ u, (step adj χ rⱼ).col u = (step adj χ rⱼ).col (t r₁) → u = t r₁ := by
    rw [htrj]; exact step_indiv_singleton adj χ rⱼ
  -- run `joint`: get `σf` with `σf r₁ = rⱼ`
  obtain ⟨σf, leaf_b, hσf, hrepl, hleaf, ha0⟩ :=
    joint adj χ n (step adj χ r₁) (step adj χ rⱼ) t r₁ ht hrel hrefa hrefb hb0 hAmen d1 seq hdeepen
  -- gate ⟹ all-singletons; `[DISC]` ⟹ `hfix`; piece 3 ⟹ the twist verifies to `σf`
  have hall : allSingletonsK (coupled χ d1.col) d1.col = true := by
    rcases Bool.or_eq_false_iff.mp hgate with ⟨_, h2⟩
    simpa using h2
  have hfix : ∀ w, (coupled χ d1.col).contains w = false → σf w = w := fun w hw =>
    isColAut_fixes_singleton hσf (offCoupled_singleton hdisc hw)
  have htwist : twistOf adj χ d1.col (coupled χ d1.col) leaf_b.col = some σf := by
    rw [hleaf]; exact twistOf_of_transport_fixing hall hfix hσf
  -- membership + verification, then the one-step `WordReach`
  have hmem : σf ∈ deepenGens adj χ := mem_deepenGens_of adj χ hr1 hrj hne hdeepen hgate hrepl htwist
  have hver : σf ∈ Consume.verified deepenSupply adj χ := by
    rw [Consume.verified, List.mem_filter]
    exact ⟨hmem, decide_eq_true (deepenGens_isColAut adj χ hmem)⟩
  have hwr := (Consume.WordReach.refl r₁).step hver
  rwa [ha0.trans htrj] at hwr

/-! ## 2b. Branch-cell reachability atoms -/

/-- A verified generator reaches `x ↦ g x` in one step (the base atom of every exec word). -/
theorem wordReach_of_mem_verified {S : Consume.Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Consume.verified S adj χ) (x : Fin n) :
    Consume.WordReach (Consume.verified S adj χ) x (g x) :=
  (Consume.WordReach.refl x).step hg

/-- Word-reachability is symmetric (the orbit is inverse-closed). -/
theorem wordReach_symm {G : List (Equiv.Perm (Fin n))} {u w : Fin n}
    (h : Consume.WordReach G u w) : Consume.WordReach G w u :=
  Consume.mem_orbit_iff_wordReach.mp (Consume.self_mem_orbit_of_wordReach h)

/-- A colour-automorphism preserves the branch cell (it fixes the target colour). -/
theorem isColAut_mem_branches {adj : AdjMatrix n} {χ : Colouring n} {β : Equiv.Perm (Fin n)}
    (hβ : IsColAut adj χ β) {x : Fin n} (hx : x ∈ Descend.branches χ) :
    β x ∈ Descend.branches χ := by
  obtain ⟨c, hc, hxc⟩ := Consume.exists_targetColour_of_mem hx
  exact (Descend.mem_branches_iff hc (β x)).mpr (by rw [hβ.2 x]; exact hxc)

/-! ## 2b′. ★★★ [DISC] IS STRUCTURAL — the track-A win that eliminates `AnchorFires`

`deepen` now individualizes to WHOLE-graph discreteness, so a successful leaf is *automatically* discrete
(`deepen_discrete`) and the gate passes for free on a non-trivial branch cell (`gate_of_discrete`). The old
`AnchorFires` domain hypothesis — `deepen` succeeds + gate + `Discrete` leaf — is thus discharged
structurally: `[DISC]` from the loop's stop condition, `deepen` succeeds by fuel-adequacy
(`deepen_succeeds`), the gate from `[DISC]`. Only `Amenable` remains. -/

/-- The `chooseIdK` min-fold from a `some` seed never returns `none`. -/
theorem foldl_min_isSome (χc : Colouring n) :
    ∀ (L : List (Fin n)) (m : Nat),
      (L.foldl (fun acc v => match acc with
        | none => some (χc v) | some m => some (min m (χc v))) (some m)).isSome := by
  intro L
  induction L with
  | nil => intro m; simp
  | cons v L ih => intro m; simp only [List.foldl_cons]; exact ih _

/-- **★ `chooseIdK (finRange) = none` ⟹ `Discrete`.** No non-singleton cell means every class is a
singleton = injective. This is what makes `[DISC]` STRUCTURAL for whole-graph `deepen`. -/
theorem discrete_of_chooseIdK_none {χc : Colouring n}
    (h : chooseIdK (List.finRange n) χc = none) : Discrete χc := by
  intro u w huw
  by_contra hne
  have hu' : u ∈ classOf χc u := List.mem_filter.mpr ⟨List.mem_finRange u, by simp⟩
  have hw' : w ∈ classOf χc u := List.mem_filter.mpr ⟨List.mem_finRange w, by simpa using huw.symm⟩
  have hlen : 2 ≤ (classOf χc u).length := by
    by_contra hlt
    exact hne (eq_of_mem_of_length_le_one (Nat.lt_succ_iff.mp (Nat.lt_of_not_le hlt)) hu' hw')
  have hmem : u ∈ (List.finRange n).filter (fun v => (classOf χc v).length ≥ 2) :=
    List.mem_filter.mpr ⟨List.mem_finRange u, by simpa using hlen⟩
  have hne_nil : (List.finRange n).filter (fun v => (classOf χc v).length ≥ 2) ≠ [] := by
    intro hc; rw [hc] at hmem; simp at hmem
  unfold chooseIdK at h
  obtain ⟨a, L, hfl⟩ := List.exists_cons_of_ne_nil hne_nil
  rw [hfl] at h
  simp only [List.foldl_cons] at h
  exact absurd h (Option.isSome_iff_ne_none.mp (foldl_min_isSome χc L (χc a)))

/-- **★ [DISC] IS STRUCTURAL.** `deepen` individualizes to whole-graph discreteness, so any successful
leaf is discrete. -/
theorem deepen_discrete (adj : AdjMatrix n) (χp : Colouring n) (fuel : Nat) :
    ∀ (cur : Refine.ColData n) (seq : List Nat) (d1 : Refine.ColData n) (s : List Nat),
      deepen adj χp fuel cur seq = some (d1, s) → Discrete d1.col := by
  induction fuel with
  | zero => intro cur seq d1 s h; simp [deepen] at h
  | succ fuel ih =>
      intro cur seq d1 s h
      unfold deepen at h
      dsimp only at h
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none =>
          rw [hco] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          exact discrete_of_chooseIdK_none hco
      | some cid =>
          rw [hco] at h
          dsimp only at h
          cases hfl : (List.finRange n).filter (fun v => cur.col v == cid) with
          | nil => rw [hfl] at h; simp at h
          | cons w rest => rw [hfl] at h; dsimp only at h; exact ih _ _ _ _ h

/-- **`deepen` fuel-adequacy.** With more fuel than the colour deficit `n - ncol`, `deepen` reaches a
discrete leaf: each level individualizes a non-singleton cell (`chooseIdK = some`), and individualizing a
vertex with a same-colour partner strictly raises `ncol` (`ncol_lt_indivOne_of_partner`), while the warm
refine never lowers it (`ncol_le_refine`). -/
theorem deepen_isSome (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n),
      n - Descend.ncol cur.col < fuel → (deepen adj χp fuel cur []).isSome := by
  intro fuel
  induction fuel with
  | zero => intro cur h; omega
  | succ fuel ih =>
      intro cur h
      unfold deepen
      dsimp only
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => simp
      | some cid =>
          dsimp only
          cases hfl : (List.finRange n).filter (fun v => cur.col v == cid) with
          | nil =>
              exfalso
              have h2 := chooseIdK_mem _ _ hco
              unfold cidCell at h2; rw [hfl] at h2; simp at h2
          | cons w rest =>
              dsimp only
              rw [deepen_acc adj χp fuel (step adj cur.col w) [cid], Option.isSome_map]
              apply ih
              -- `w` has a same-colour partner in its (≥ 2)-cell, so `ncol` strictly increases
              have hcell : cidCell cur.col cid = w :: rest := hfl
              have hlen : 2 ≤ (cidCell cur.col cid).length := chooseIdK_mem _ _ hco
              have hwcid : cur.col w = cid := by
                have hwm : w ∈ cidCell cur.col cid := by rw [hcell]; simp
                exact (mem_cidCell_iff _ _ _).mp hwm
              obtain ⟨u, rest', hrest⟩ : ∃ u rest', rest = u :: rest' := by
                cases rest with
                | nil => rw [hcell] at hlen; simp at hlen
                | cons u rest' => exact ⟨u, rest', rfl⟩
              have hucid : cur.col u = cid := by
                have hum : u ∈ cidCell cur.col cid := by rw [hcell, hrest]; simp
                exact (mem_cidCell_iff _ _ _).mp hum
              have hnd : (cidCell cur.col cid).Nodup := cidCell_nodup cur.col cid
              rw [hcell, hrest] at hnd
              simp only [List.nodup_cons, List.mem_cons] at hnd
              have huw : u ≠ w := fun heq => hnd.1 (Or.inl heq.symm)
              have hpartner : ∃ z, z ≠ w ∧ cur.col z = cur.col w := ⟨u, huw, by rw [hucid, hwcid]⟩
              have h1 : Descend.ncol cur.col < Descend.ncol (Descend.indivOne cur.col w) :=
                Descend.ncol_lt_indivOne_of_partner hpartner
              have h2 : Descend.ncol (Descend.indivOne cur.col w) ≤ Descend.ncol (step adj cur.col w).col := by
                show _ ≤ Descend.ncol (Refine.warmRefineVec adj (Descend.indivOne cur.col w)).col
                rw [Refine.warmRefineVec_col_eq, ← Refine.refineV_encodeFreeFast]
                exact Descend.ncol_le_refine Refine.refineSplits_encodeFreeFast adj (Descend.indivOne cur.col w)
              have h3 := Descend.ncol_le (step adj cur.col w).col
              omega

/-- **★ `deepen` TERMINATES to a discrete leaf** — `[DISC]`/termination is STRUCTURAL (track A). Fuel `n`
always suffices: `ncol (step … x) ≥ 1`, so the colour deficit is `< n`. Discharges (with `deepen_discrete`,
`gate_of_discrete`) the whole of the old `AnchorFires` bundle — only `Amenable` remains. -/
theorem deepen_succeeds (adj : AdjMatrix n) (χ : Colouring n) (x : Fin n) :
    ∃ (d1 : Refine.ColData n) (seq : List Nat),
      deepen adj χ n (step adj χ x) [] = some (d1, seq) := by
  have hpos : 0 < Descend.ncol (step adj χ x).col := by
    unfold Descend.ncol; rw [Finset.card_pos]
    exact ⟨(step adj χ x).col x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  have hle : Descend.ncol (step adj χ x).col ≤ n := Descend.ncol_le _
  have hsome : (deepen adj χ n (step adj χ x) []).isSome := deepen_isSome adj χ n _ (by omega)
  obtain ⟨⟨d1, seq⟩, hd⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨d1, seq, hd⟩

/-- Discrete ⟹ every class is a singleton ⟹ `allSingletonsK` on any `K`. -/
theorem allSingletonsK_of_discrete {χc : Colouring n} (hdisc : Discrete χc) (K : List (Fin n)) :
    allSingletonsK K χc = true := by
  unfold allSingletonsK
  rw [List.all_eq_true]
  intro v _
  simp only [beq_iff_eq]
  have hv : v ∈ classOf χc v := List.mem_filter.mpr ⟨List.mem_finRange v, by simp⟩
  have hnd : (classOf χc v).Nodup := (List.nodup_finRange n).filter _
  have hge : 0 < (classOf χc v).length := List.length_pos_of_mem hv
  have hle : (classOf χc v).length ≤ 1 := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hne_nil : classOf χc v ≠ [] := by intro hc; rw [hc] at hv; simp at hv
    obtain ⟨a, L, hfl⟩ := List.exists_cons_of_ne_nil hne_nil
    rcases L with _ | ⟨b, L'⟩
    · rw [hfl] at hlt; simp at hlt
    · have ha : a ∈ classOf χc v := by rw [hfl]; exact List.mem_cons_self ..
      have hb : b ∈ classOf χc v := by rw [hfl]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      rw [hfl] at hnd
      simp only [List.nodup_cons, List.mem_cons] at hnd
      have hab : a ≠ b := fun h => hnd.1 (Or.inl h)
      have hav : a = v := hdisc a v (by simpa using (List.mem_filter.mp ha).2)
      have hbv : b = v := hdisc b v (by simpa using (List.mem_filter.mp hb).2)
      exact hab (hav.trans hbv.symm)
  omega

/-- **★ THE GATE PASSES FROM `[DISC]`.** A whole-graph-discrete leaf makes every cell a singleton
(`allSingletonsK`), and a non-trivial branch pair `(x, w)` puts `x` in the coupled component (its `χ`-cell
split), so the gate `(K.isEmpty || ¬allSingletonsK) = false`. -/
theorem gate_of_discrete {χ χc : Colouring n} {x w : Fin n}
    (hxw : χ x = χ w) (hne : x ≠ w) (hdisc : Discrete χc) :
    ((coupled χ χc).isEmpty || !allSingletonsK (coupled χ χc) χc) = false := by
  rw [Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · -- `x ∈ coupled` ⟹ coupled non-empty
    have hxmem : x ∈ coupled χ χc := by
      rw [coupled, List.mem_filter]
      refine ⟨List.mem_finRange x, ?_⟩
      -- `x`'s `χ`-cell maps through `χc` to ≥ 2 distinct values (`χc x ≠ χc w`, both in the cell)
      have hxc : x ∈ (List.finRange n).filter (fun z => χ z == χ x) :=
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩
      have hwc : w ∈ (List.finRange n).filter (fun z => χ z == χ x) :=
        List.mem_filter.mpr ⟨List.mem_finRange w, by simpa using hxw.symm⟩
      have hne' : χc x ≠ χc w := fun h => hne (hdisc x w h)
      have hx2 : χc x ∈ (((List.finRange n).filter (fun z => χ z == χ x)).map χc) :=
        List.mem_map.mpr ⟨x, hxc, rfl⟩
      have hw2 : χc w ∈ (((List.finRange n).filter (fun z => χ z == χ x)).map χc) :=
        List.mem_map.mpr ⟨w, hwc, rfl⟩
      have : 2 ≤ (((List.finRange n).filter (fun z => χ z == χ x)).map χc).dedup.length := by
        have hxd : χc x ∈ (((List.finRange n).filter (fun z => χ z == χ x)).map χc).dedup :=
          List.mem_dedup.mpr hx2
        have hwd : χc w ∈ (((List.finRange n).filter (fun z => χ z == χ x)).map χc).dedup :=
          List.mem_dedup.mpr hw2
        by_contra hlt
        exact hne' (eq_of_mem_of_length_le_one (Nat.lt_succ_iff.mp (Nat.lt_of_not_le hlt)) hxd hwd)
      simpa using this
    cases hc : (coupled χ χc) with
    | nil => rw [hc] at hxmem; exact absurd hxmem (by simp)
    | cons a L => simp
  · rw [allSingletonsK_of_discrete hdisc]; simp

/-- **★ CELL COVERAGE — a colour-automorphism image is exec-reachable on the branch cell.** For `x ∈ cell`,
the branch-cell half applied at anchor `x` (rep `ρ x`, automorphism `ρ`) reaches `ρ x` directly; `ρ x = x`
is `refl`. `AnchorFires` is GONE: `deepen` succeeds (`deepen_succeeds`), the leaf is discrete
(`deepen_discrete`), and the gate passes (`gate_of_discrete`) — all structural, only `Amenable` remains. -/
theorem exec_recovers_refgen_on_cell (adj : AdjMatrix n) (χ : Colouring n)
    {ρ : Equiv.Perm (Fin n)} (hρaut : IsColAut adj χ ρ) (hAmen : Amenable adj χ)
    {x : Fin n} (hx : x ∈ Descend.branches χ) :
    Consume.WordReach (Consume.verified deepenSupply adj χ) x (ρ x) := by
  by_cases hfix : ρ x = x
  · rw [hfix]; exact Consume.WordReach.refl x
  · have hρx : ρ x ∈ Descend.branches χ := isColAut_mem_branches hρaut hx
    have hne : (ρ x == x) = false := by rw [beq_eq_false_iff_ne]; exact hfix
    -- both `x` and `ρ x` sit in the branch cell ⟹ same `χ`-colour
    obtain ⟨c, hc, hxc⟩ := Consume.exists_targetColour_of_mem hx
    have hρxc : χ (ρ x) = c := by
      obtain ⟨c', hc', hρxc'⟩ := Consume.exists_targetColour_of_mem hρx
      rw [hc'] at hc; cases hc; exact hρxc'
    have hxeq : χ x = χ (ρ x) := by rw [hxc, hρxc]
    -- structural firing facts (track A)
    obtain ⟨d1, seq, hd⟩ := deepen_succeeds adj χ x
    have hDisc : Discrete d1.col := deepen_discrete adj χ n (step adj χ x) [] d1 seq hd
    have hg : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false :=
      gate_of_discrete hxeq (fun h => hfix h.symm) hDisc
    exact exec_recovers_cell_orbits adj χ hx hρx hne hρaut rfl hd hg (hAmen x hx) hDisc

/-! ## 2b″. ★★★ THE REFERENCE-FREE, ANCHORFIRES-FREE CLOSE — `①c` modulo `{Amenable}` ONLY

`StallEquivariant` needs only that deepen's **branch-orbit relation transports**
(`SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport`) — and it does, because deepen's
branch orbits EQUAL the `IsColAut`-orbits (⟸ = the branch-cell half; ⟹ = soundness), which transport under `σ`
by `isColAut_conj_iff`. So `①c` closes with **no reference, no R1, no R2, no `AnchorFires`** — only `{Amenable}`,
since track-A whole-graph `deepen` makes `[DISC]`/gate/termination structural (`deepen_discrete`,
`gate_of_discrete`, `deepen_succeeds`). This supersedes the entire `SameOrbits`/`deepenRefSupply`/`twistOf`
apparatus (discarded provenance). -/

/-- A `WordReach` in deepen's verified generators is realized by a single colour-automorphism (soundness at the
group level — the word composes to one `IsColAut`). -/
theorem wordReach_imp_isColAut {adj : AdjMatrix n} {χ : Colouring n} {u w : Fin n}
    (h : Consume.WordReach (Consume.verified deepenSupply adj χ) u w) :
    ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w := by
  induction h with
  | refl => exact ⟨1, IsColAut.one adj χ, rfl⟩
  | @step m _ g hg ih =>
      obtain ⟨β, hβ, hβu⟩ := ih
      exact ⟨g * β, (Consume.isColAut_of_mem_verified hg).comp hβ, by
        rw [Equiv.Perm.mul_apply, hβu]⟩

/-- **★ deepen's branch orbits ARE the `IsColAut`-orbits.** For a branch source `u`, `WordReach exec u w` iff `u`
and `w` lie in the same colour-automorphism orbit. `⟹` is `wordReach_imp_isColAut`; `⟸` is the branch-cell half
`exec_recovers_refgen_on_cell`. -/
theorem deepen_branch_orbit_iff_aut (adj : AdjMatrix n) (χ : Colouring n)
    (hAmen : Amenable adj χ)
    {u : Fin n} (hu : u ∈ Descend.branches χ) {w : Fin n} :
    Consume.WordReach (Consume.verified deepenSupply adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w := by
  constructor
  · exact wordReach_imp_isColAut
  · rintro ⟨β, hβ, rfl⟩
    exact exec_recovers_refgen_on_cell adj χ hβ hAmen hu

/-- **★★ deepen's branch-orbit relation TRANSPORTS.** Both sides equal the `IsColAut`-orbit relation, which
conjugates under `σ` (`isColAut_conj_iff`). Needs `{Amenable, AnchorFires}` on every graph (they are ∀-quantified
domain facts, so they hold on the relabelled graph too). -/
theorem deepen_branchOrbit_transport
    (hAmen : ∀ (adj : AdjMatrix n) (χ : Colouring n), Amenable adj χ)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n)
    (ha : a ∈ Descend.branches χ) (hb : b ∈ Descend.branches χ) :
    Consume.WordReach (Consume.verified deepenSupply (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
      ↔ Consume.WordReach (Consume.verified deepenSupply adj χ) a b := by
  have hσa : σ a ∈ Descend.branches (transportColouring σ χ) :=
    (Descend.branches_transport_perm σ χ).mem_iff.mpr (List.mem_map_of_mem ha)
  rw [deepen_branch_orbit_iff_aut _ _ (hAmen _ _) hσa,
      deepen_branch_orbit_iff_aut _ _ (hAmen _ _) ha]
  constructor
  · rintro ⟨β, hβ, hβa⟩
    refine ⟨σ⁻¹ * β * σ, ?_, ?_⟩
    · have := (Consume.isColAut_conj_iff σ (adj := adj) (χ := χ) (α := σ⁻¹ * β * σ)).mp
      rw [show σ * (σ⁻¹ * β * σ) * σ⁻¹ = β by group] at this
      exact this hβ
    · simp [Equiv.Perm.mul_apply, hβa]
  · rintro ⟨β, hβ, hβa⟩
    refine ⟨σ * β * σ⁻¹, (Consume.isColAut_conj_iff σ).mpr hβ, ?_⟩
    simp [Equiv.Perm.mul_apply, hβa]

/-- **★★★ `①c` FOR `deepenSupply` — REFERENCE-FREE, modulo `{Amenable, AnchorFires}` ONLY.** No `deepenRefSupply`,
no R1, no R2, no `twistOf`-transport. deepen's flag is equivariant because its branch orbits are the
`IsColAut`-orbits, which transport. This is the intended, clean close of `①c`. -/
theorem deepenSupply_guarded_canonizer_direct
    (hAmen : ∀ (adj : AdjMatrix n) (χ : Colouring n), Amenable adj χ) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupply (n := n))))) :=
  Residue.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport
      Force.keyEquivariant_lookahead (deepen_branchOrbit_transport hAmen))

/-! ## 2b‴. The rigid handoff — deepen DEFERS SOUNDLY on a rigid obstruction

`①c` is conditional on `Amenable`; an `Amenable`-violation is a `RigidObstructionAt`
(`rigidObstruction_of_not_cellSingleOrbit`). This subsection nails the SOUND half of the rigid handoff at the
branch cell: deepen can never *mishandle* a rigid pair, so it hands it, untouched, to the force / rigid side.
What remains is the WALL (force actually separating the rigid cell = `CellResolved`'s force branch =
`hSmallAutThin`) + the fusion/scheduling gap (the `Amenable` obstruction lives at a deep level; the
interleaving must peel it before consume) — both totality obligations, neither a new conjecture. -/

/-- **★ DEEPEN DEFERS SOUNDLY ON A RIGID OBSTRUCTION.** A same-colour NON-automorphic branch pair `(u, w)` can
never be connected by deepen's verified generators — they are all `IsColAut`, so a `WordReach u w` would furnish
the very automorphism ruled out. Hence `CellIsOrbit` FAILS on a rigid cell: deepen emit-nothings and the pair
passes, untouched, to force. This is the exact `RigidObstructionAt` that G2 attributes an `Amenable`-violation
to — the SAME 1-WL-merged non-automorphic pair the rigid solver / §11.14 classification already own, not a new
obstruction type. -/
theorem rigidObstruction_imp_not_cellIsOrbit {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (hu : u ∈ Descend.branches χ) (hw : w ∈ Descend.branches χ)
    (hrig : ∀ β : Equiv.Perm (Fin n), IsColAut adj χ β → β u ≠ w) :
    ¬ Consume.CellIsOrbit deepenSupply adj χ := by
  intro h
  obtain ⟨β, hβ, hβu⟩ := wordReach_imp_isColAut (h u hu w hw)
  exact hrig β hβ hβu

/-- **★★ A CONSUME-PATH FAILURE EXPOSES A RIGID DECISION.** If the deepening path from a state is NOT
`AmenablePath` — exactly when consume can fail to recover a genuinely same-orbit pair (fusion: symmetry over a
deeper rigid obstruction) — then some cell *along that path* carries a `RigidObstructionAt`: a concrete
same-colour non-automorphic pair, force-actionable. So a consume-stall never dead-ends — it always surfaces one
exposed rigid node (possibly deeper than the compared pair, which itself may be automorphic). This is the honest
handoff target: NOT "the compared pair is rigid" (false under fusion), but "a rigid decision is exposed for
force," which is what makes the force⇄consume interleaving terminate. -/
theorem not_amenablePath_imp_rigidObstruction (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), ¬ AmenablePath adj χp fuel cur →
      ∃ (χc : Colouring n) (cid : Nat), RigidObstructionAt adj χc cid := by
  intro fuel
  induction fuel with
  | zero => intro cur h; exact absurd trivial h
  | succ fuel ih =>
      intro cur h
      unfold AmenablePath at h
      dsimp only at h
      split at h
      · exact absurd trivial h
      · rename_i cid _
        rw [not_and_or] at h
        rcases h with hcso | htail
        · exact ⟨cur.col, cid, rigidObstruction_of_not_cellSingleOrbit adj cur.col cid hcso⟩
        · split at htail
          · exact absurd trivial htail
          · rename_i w _ _
            exact ih (step adj cur.col w) htail

end Deepen
end ChainDescent
