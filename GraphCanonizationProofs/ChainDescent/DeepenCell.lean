import ChainDescent.DeepenGuardComplete
import ChainDescent.SelectCell

/-!
# ★★★ THE CELL-ANCHORED DEEPEN HARVEST — design `B`, step 1

**The defect this repairs** (`docs/chain-descent-percell-plan.md`, 2026-08-07). `deepenSupply` is the
only **pair-anchored** supply in the project: `deepenGens` draws its pairs from `Descend.branches χ`,
the *least* non-singleton cell. But `SelectNode.cellNarrow` reads one **node-global**
`verified S adj χ` list and probes **every** cell against it. Each emitted twist is a full
automorphism supported on `coupled χ leaf` = the union of all non-singleton cells, so a cell that
never had a descent run on it is judged by generators harvested elsewhere — and that verdict is
**measured not relabelling-invariant**:

> `scratchpad/probe_offbranch2.py` — CFI cubic m = 8 and m = 10, plain and twisted, **depth 1**: an
> off-branch cell of size 2 counts `(1,1)` under one labelling and `(2,)` under its own transport.
> `probe_offbranch3.py` — at that node the guard is **OPEN on both sides**, so it falsifies
> `deepenSupplyCert` too, not merely the raw supply.

The repair (`probe_offbranch4/5.py`, 9/9 with 7 non-vacuous rows) is to judge each cell by **its own**
descents. This file supplies the harvest that makes that possible.

## What is here, and why each piece is shaped this way

`deepenGens`'s anchor list is the only thing that has to move. Everything downstream of it —
`deepen`, `replay`, `twistOf`, the gate, `coupled` — is already indexed by `(adj, χ)` alone and
**never mentions which cell the anchors came from**. So §1 abstracts the list into a parameter and
§2–§4 re-run the three facts that consume it. Each of those proofs used its branch-cell hypotheses in
exactly one place:

* `deepenGens_isColAut` — nowhere (it only destructs the `flatMap`);
* `mem_deepenGens_of` — one `List.mem_map.mpr ⟨r₁, hr1, rfl⟩` per anchor;
* `exec_recovers_cell_orbits` — one call to `mem_deepenGens_of`.

⚠ **This is deliberate duplication, not a refactor.** `deepenGens` keeps its definition and every
theorem stated at it keeps its proof; nothing in `DeepenSupply` / `DeepenCrux` / `DeepenTinhofer`
changes. The alternative — re-defining `deepenGens := deepenGensOn adj χ (Descend.branches χ)` — is
defeq but breaks every downstream `unfold deepenGens`, which is a large blast radius for no gain.
`deepenGens_eq_deepenGensOn` is `rfl`, so the two never drift.

## ★ What §5 buys, and why the guard needs no new completeness theorem

The scoping worry recorded in the plan (§10 risk 1) — that a per-cell guard would need a per-cell
analogue of `DeepenGuardComplete.tinhofer_iff_certifiedG`, whose proof routes through
`chooseIdK_eq_targetColour` and so is branch-cell-specific — **does not arise**. `GoodAnchor adj χ x`
is `TinhoferPath adj χ n (step adj χ x)`: a statement about **`x`'s own deepening path**, which never
mentions which cell `x` lives in. Consequently the three facts a per-cell guard needs are already
proved, at full generality:

| need | already proved |
|---|---|
| decidable | `DeepenGuardComplete.goodAnchor_iff_certPath` + `instDecidableGoodAnchor` |
| relabelling-invariant | `DeepenGuardComplete.goodAnchor_relabel` — **unconditional** |
| recovers the orbit | §5 below, `exec_recovers_refgen_on` |

⟹ the per-cell guard is `∀ r ∈ cellList χ c, GoodAnchor adj χ r`, and its **verdict** is invariant
outright. That is the property the whole design turns on: a shut guard emits `[]`, so the count is
`|cell c|` on both sides automatically, and only the verdict has to transport — never the harvest.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut Supply verified gens WordReach)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The harvest, with the anchor list abstracted

`DeepenSupply.deepenGens` verbatim, with `let cell := Descend.branches χ` replaced by a parameter.
Every hoisting (`firsts` computed once — trap #2) and the `Vector` materialisation inside `twistOf`
(trap #1) are preserved, so the cost story is unchanged. -/

/-- **The deepening harvest anchored at an arbitrary vertex list.** For every ordered pair of `cell`,
deepen the first to whole-graph discreteness, replay the recorded id sequence from the second, and
emit the footprint twist if it verifies as an `IsColAut`. -/
def deepenGensOn (adj : AdjMatrix n) (χ : Colouring n) (cell : List (Fin n)) :
    List (Equiv.Perm (Fin n)) :=
  let firsts : List (Fin n × Refine.ColData n) := cell.map (fun r => (r, step adj χ r))
  firsts.flatMap (fun p1 =>
    match deepen adj χ n p1.2 [] with
    | none => []
    | some (d1, seq) =>
        let χ1 := d1.col
        let K := coupled χ χ1
        if K.isEmpty || !allSingletonsK K χ1 then []
        else
          firsts.filterMap (fun pj =>
            if pj.1 == p1.1 then none
            else match replay adj seq pj.2 with
              | none => none
              | some dj => twistOf adj χ χ1 K dj.col))

/-- The executable supply is the branch-cell instance — definitionally. So the two objects can never
drift, and every fact proved below about `deepenGensOn` specialises to `deepenGens` for free. -/
theorem deepenGens_eq_deepenGensOn (adj : AdjMatrix n) (χ : Colouring n) :
    deepenGens adj χ = deepenGensOn adj χ (Descend.branches χ) := rfl

/-! ## 2. Soundness — every emitted generator is verified, at any anchor list

`DeepenCrux.deepenGens_isColAut`'s proof never looked at the anchor list; it only destructs the
`flatMap`/`filterMap` and lands on `twistOf_isColAut`. -/

/-- **Every generator the cell-anchored harvest emits is a genuine colour-automorphism.** The
failsafe half, unconditional at every anchor list — over-splitting costs a branch, never `①`. -/
theorem deepenGensOn_isColAut (adj : AdjMatrix n) (χ : Colouring n) (cell : List (Fin n))
    {ρ : Equiv.Perm (Fin n)} (h : ρ ∈ deepenGensOn adj χ cell) : IsColAut adj χ ρ := by
  unfold deepenGensOn at h
  rw [List.mem_flatMap] at h
  obtain ⟨p1, _, h⟩ := h
  cases hd : deepen adj χ n p1.2 [] with
  | none => rw [hd] at h; simp at h
  | some ds =>
      obtain ⟨d1, seq⟩ := ds
      rw [hd] at h; dsimp only at h
      by_cases hgate :
          ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = true
      · rw [if_pos hgate] at h; simp at h
      · rw [if_neg hgate] at h
        rw [List.mem_filterMap] at h
        obtain ⟨pj, _, h⟩ := h
        by_cases heq : (pj.1 == p1.1) = true
        · rw [if_pos heq] at h; simp at h
        · rw [if_neg heq] at h
          cases hr : replay adj seq pj.2 with
          | none => rw [hr] at h; simp at h
          | some dj =>
              rw [hr] at h; dsimp only at h
              exact twistOf_isColAut adj χ d1.col _ dj.col h

/-! ## 3. Forward membership, at any anchor list

`DeepenTinhofer.mem_deepenGens_of` with `hr1`/`hrj` weakened from `Descend.branches χ` to `cell` —
they were only ever feeding `List.mem_map.mpr`. -/

/-- **The twist for `(r₁, rⱼ)` is an emitted generator**, from the pipeline facts. -/
theorem mem_deepenGensOn_of (adj : AdjMatrix n) (χ : Colouring n) {cell : List (Fin n)}
    {r₁ rⱼ : Fin n} {d1 dj : Refine.ColData n} {seq : List Nat} {g : Equiv.Perm (Fin n)}
    (hr1 : r₁ ∈ cell) (hrj : rⱼ ∈ cell) (hne : (rⱼ == r₁) = false)
    (hdeepen : deepen adj χ n (step adj χ r₁) [] = some (d1, seq))
    (hgate : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false)
    (hrepl : replay adj seq (step adj χ rⱼ) = some dj)
    (htwist : twistOf adj χ d1.col (coupled χ d1.col) dj.col = some g) :
    g ∈ deepenGensOn adj χ cell := by
  unfold deepenGensOn
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

/-! ## 4. Recovery at any anchor list

`DeepenTinhofer.exec_recovers_cell_orbits`, with its one branch-cell dependency (the
`mem_deepenGens_of` call) redirected. The conclusion is stated as a **generator existence** rather
than a `WordReach`, so it is supply-agnostic: §6 turns it into whichever supply the caller needs. -/

/-- **★★ THE CELL-ANCHORED RECOVERY THEOREM.** If `t` is a colour-automorphism carrying `r₁` to `rⱼ`,
both in `cell`, and `r₁`'s own deepening path is Schurian, then the harvest anchored at `cell`
**emits a generator carrying `r₁` to `rⱼ`**. -/
theorem exists_gen_deepenGensOn (adj : AdjMatrix n) (χ : Colouring n) {cell : List (Fin n)}
    {r₁ rⱼ : Fin n} {d1 : Refine.ColData n} {seq : List Nat} {t : Equiv.Perm (Fin n)}
    (hr1 : r₁ ∈ cell) (hrj : rⱼ ∈ cell) (hne : (rⱼ == r₁) = false)
    (ht : IsColAut adj χ t) (htrj : t r₁ = rⱼ)
    (hdeepen : deepen adj χ n (step adj χ r₁) [] = some (d1, seq))
    (hgate : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false)
    (hAmen : TinhoferPath adj χ n (step adj χ r₁))
    (hdisc : Discrete d1.col) :
    ∃ g ∈ deepenGensOn adj χ cell, g r₁ = rⱼ := by
  have hrel : (step adj χ rⱼ).col = transportColouring t (step adj χ r₁).col := by
    have hs := step_isColAut ht χ r₁
    rw [transportColouring_isColAut ht, htrj] at hs; exact hs
  have hrefa : ∀ x y, (step adj χ r₁).col x = (step adj χ r₁).col y → χ x = χ y :=
    fun x y h => step_refines adj χ r₁ h
  have hrefb : ∀ x y, (step adj χ rⱼ).col x = (step adj χ rⱼ).col y → χ x = χ y :=
    fun x y h => step_refines adj χ rⱼ h
  have hb0 : ∀ u, (step adj χ rⱼ).col u = (step adj χ rⱼ).col (t r₁) → u = t r₁ := by
    rw [htrj]; exact step_indiv_singleton adj χ rⱼ
  obtain ⟨σf, leaf_b, hσf, hrepl, hleaf, ha0⟩ :=
    joint adj χ n (step adj χ r₁) (step adj χ rⱼ) t r₁ ht hrel hrefa hrefb hb0 hAmen d1 seq hdeepen
  have hall : allSingletonsK (coupled χ d1.col) d1.col = true := by
    rcases Bool.or_eq_false_iff.mp hgate with ⟨_, h2⟩
    simpa using h2
  have hfix : ∀ w, (coupled χ d1.col).contains w = false → σf w = w := fun w hw =>
    isColAut_fixes_singleton hσf (offCoupled_singleton hdisc hw)
  have htwist : twistOf adj χ d1.col (coupled χ d1.col) leaf_b.col = some σf := by
    rw [hleaf]; exact twistOf_of_transport_fixing hall hfix hσf
  exact ⟨σf, mem_deepenGensOn_of adj χ hr1 hrj hne hdeepen hgate hrepl htwist, ha0.trans htrj⟩

/-! ## 5. ★★★ A GOOD ANCHOR RECOVERS ITS ORBIT **INSIDE ITS OWN CELL**

`DeepenComplete.exec_recovers_refgen_at` with `Descend.branches χ` replaced by an arbitrary
same-coloured list. The branch-cell version obtained its `χ x = χ (ρ x)` from
`Consume.exists_targetColour_of_mem`; here it is free — `IsColAut`'s second component says exactly
that — which is why nothing about the *target* cell is needed. -/

/-- **★★★ THE PER-CELL RECOVERY.** For `x` in `cell` whose own deepening path is Schurian, and any
colour-automorphism `ρ` with `ρ x ∈ cell` and `ρ x ≠ x`, the harvest anchored at `cell` emits a
generator carrying `x` to `ρ x`. -/
theorem exists_gen_of_goodAnchor (adj : AdjMatrix n) (χ : Colouring n) {cell : List (Fin n)}
    {ρ : Equiv.Perm (Fin n)} (hρaut : IsColAut adj χ ρ) {x : Fin n}
    (hx : x ∈ cell) (hρx : ρ x ∈ cell) (hfix : ρ x ≠ x)
    (hgood : GoodAnchor adj χ x) :
    ∃ g ∈ deepenGensOn adj χ cell, g x = ρ x := by
  have hne : (ρ x == x) = false := by rw [beq_eq_false_iff_ne]; exact hfix
  have hxeq : χ x = χ (ρ x) := (hρaut.2 x).symm
  obtain ⟨d1, seq, hd⟩ := deepen_succeeds adj χ x
  have hDisc : Discrete d1.col := deepen_discrete adj χ n (step adj χ x) [] d1 seq hd
  have hg : ((coupled χ d1.col).isEmpty || !allSingletonsK (coupled χ d1.col) d1.col) = false :=
    gate_of_discrete hxeq (fun h => hfix h.symm) hDisc
  exact exists_gen_deepenGensOn adj χ hx hρx hne hρaut rfl hd hg hgood hDisc

/-! ## 6. The per-cell supply, its guard, and orbit completeness AT A CELL -/

/-- **The deepening supply anchored at the cell of colour `c`.** Cost is the same declared flat
`n⁶` the branch-cell supply bills: per cell of size `m` the harvest is `≈ m² n⁴`, and
`Σ_c m_c² ≤ (Σ_c m_c)² = n²`, so the whole per-cell family together still fits inside it. -/
def deepenSupplyAt (c : Nat) : Supply n := fun adj χ =>
  (deepenGensOn adj χ (Select.cellList χ c), n * n * n * n * n * n)

theorem gens_deepenSupplyAt (c : Nat) (adj : AdjMatrix n) (χ : Colouring n) :
    gens (deepenSupplyAt (n := n) c) adj χ = deepenGensOn adj χ (Select.cellList χ c) := rfl

/-- Soundness at any verified list, supply-generic (`DeepenTinhofer.wordReach_imp_isColAut` is
stated at `deepenSupply`; its proof only uses `isColAut_of_mem_verified`). -/
theorem wordReach_imp_isColAut_any {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (h : WordReach (verified S adj χ) u w) :
    ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w := by
  induction h with
  | refl => exact ⟨1, Consume.IsColAut.one adj χ, rfl⟩
  | @step m _ g hg ih =>
      obtain ⟨β, hβ, hβu⟩ := ih
      exact ⟨g * β, (Consume.isColAut_of_mem_verified hg).comp hβ, by
        rw [Equiv.Perm.mul_apply, hβu]⟩

/-- **★★ THE PER-CELL GUARD** — every anchor of the cell has a Schurian deepening path.

Three facts make this the right guard, and **all three are already proved**, because `GoodAnchor` is
a statement about the anchor's *own* path and never mentions which cell it lives in: it is decidable
(`goodAnchor_iff_certPath`), it is relabelling-invariant **unconditionally**
(`goodAnchor_relabel`), and it recovers the orbit (§5). No per-cell analogue of
`tinhofer_iff_certifiedG` is needed. -/
def GoodCell (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) : Prop :=
  ∀ r ∈ Select.cellList χ c, GoodAnchor adj χ r

instance instDecidableGoodCell (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    Decidable (GoodCell adj χ c) :=
  inferInstanceAs (Decidable (∀ r ∈ Select.cellList χ c, GoodAnchor adj χ r))

/-- **★★★ THE GUARD'S VERDICT TRANSPORTS** — unconditionally. Cells correspond under relabelling
(`cellList_transport_perm`, colour VALUES being canonical) and goodness transports outright
(`goodAnchor_relabel`). This is the only invariance the design needs. -/
theorem goodCell_transport (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : GoodCell adj χ c) :
    GoodCell (relabelAdj σ adj) (transportColouring σ χ) c := by
  intro r' hr'
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Select.cellList χ c, σ r = r' := by
    rw [(Select.cellList_transport_perm σ χ c).mem_iff, List.mem_map] at hr'; exact hr'
  exact goodAnchor_relabel σ (h r hr)

theorem goodCell_transport_iff (σ : Equiv.Perm (Fin n)) {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} :
    GoodCell (relabelAdj σ adj) (transportColouring σ χ) c ↔ GoodCell adj χ c := by
  refine ⟨fun h => ?_, goodCell_transport σ⟩
  have h' := goodCell_transport σ⁻¹ h
  rwa [← relabelAdj_mul, transportColouring_comp, inv_mul_cancel, relabelAdj_one,
       transportColouring_one] at h'

/-- **Orbit completeness AT A CELL** — the per-cell analogue of `Deepen.OrbitComplete`, and what
`cellNarrow`'s length at colour `c` actually needs. -/
def OrbitCompleteAt (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) : Prop :=
  ∀ u ∈ Select.cellList χ c, ∀ ρ : Equiv.Perm (Fin n), IsColAut adj χ ρ →
    WordReach (verified (deepenSupplyAt (n := n) c) adj χ) u (ρ u)

/-- **★★★ THE GUARD DELIVERS ORBIT COMPLETENESS AT ITS OWN CELL.** -/
theorem orbitCompleteAt_of_goodCell {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : GoodCell adj χ c) : OrbitCompleteAt adj χ c := by
  intro u hu ρ hρ
  by_cases hfx : ρ u = u
  · rw [hfx]; exact Consume.WordReach.refl u
  · have hu' : χ u = c := (Select.mem_cellList_iff u).mp hu
    have hρu : ρ u ∈ Select.cellList χ c :=
      (Select.mem_cellList_iff (ρ u)).mpr ((hρ.2 u).trans hu')
    obtain ⟨g, hg, hgu⟩ := exists_gen_of_goodAnchor adj χ hρ hu hρu hfx (h u hu)
    have hver : g ∈ verified (deepenSupplyAt (n := n) c) adj χ := by
      rw [verified, List.mem_filter]
      exact ⟨hg, decide_eq_true (deepenGensOn_isColAut adj χ _ hg)⟩
    have hwr := (Consume.WordReach.refl u).step hver
    rwa [hgu] at hwr

/-- Under `OrbitCompleteAt` the emitted relation on the cell **is** the `IsColAut`-orbit relation:
soundness is unconditional, completeness is the guard's. -/
theorem cellOrbit_iff_aut_of_orbitCompleteAt {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : OrbitCompleteAt adj χ c) {u : Fin n} (hu : u ∈ Select.cellList χ c) {w : Fin n} :
    WordReach (verified (deepenSupplyAt (n := n) c) adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w :=
  ⟨wordReach_imp_isColAut_any, by rintro ⟨β, hβ, rfl⟩; exact h u hu β hβ⟩

/-! ## 7. ★★★ THE GUARDED PER-CELL SUPPLY, AND ITS ORBIT TRANSPORT

The payoff. `cellNarrow`'s only supply dependence is the number of orbits meeting the cell, so this
is exactly the hypothesis `SelectNode.cellNarrow_length_transport` needs — with `SupplyEquivariant`
(which `deepenSupply` provably lacks) replaced by a property the guard delivers. -/

/-- **The guarded cell-anchored supply**: deepen's own generators where the cell's anchors are all
good, nothing where they are not. Computable — `GoodCell` is decidable. -/
def deepenCellSupply (c : Nat) : Supply n := fun adj χ =>
  if GoodCell adj χ c then deepenSupplyAt (n := n) c adj χ else ([], n * n * n * n * n * n)

theorem verified_deepenCellSupply_of_open {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : GoodCell adj χ c) :
    verified (deepenCellSupply (n := n) c) adj χ = verified (deepenSupplyAt (n := n) c) adj χ := by
  unfold verified gens deepenCellSupply
  rw [if_pos h]

theorem verified_deepenCellSupply_of_shut {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : ¬ GoodCell adj χ c) : verified (deepenCellSupply (n := n) c) adj χ = [] := by
  unfold verified gens deepenCellSupply
  rw [if_neg h]; rfl

/-- **★★★ THE PER-CELL ORBIT RELATION TRANSPORTS.** Open side: the guard makes the relation *equal*
the `IsColAut`-orbit relation on the cell, which conjugates. Shut side: both are `[]`, and the guard
shuts on both sides together (`goodCell_transport_iff`) so the two cases cannot split.

★ Note what is **not** required: no completeness of deepen as an orbit oracle, no
`SupplyEquivariant`, no equivariant reference supply. Only the guard's verdict transports. -/
theorem cellOrbit_transport_deepenCellSupply (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n)
    (χ : Colouring n) (c : Nat) {a b : Fin n}
    (ha : a ∈ Select.cellList χ c) (_hb : b ∈ Select.cellList χ c) :
    WordReach (verified (deepenCellSupply (n := n) c) (relabelAdj σ adj)
        (transportColouring σ χ)) (σ a) (σ b)
      ↔ WordReach (verified (deepenCellSupply (n := n) c) adj χ) a b := by
  by_cases hA : GoodCell adj χ c
  · have hA' := goodCell_transport σ hA
    rw [verified_deepenCellSupply_of_open hA', verified_deepenCellSupply_of_open hA]
    have hσa : σ a ∈ Select.cellList (transportColouring σ χ) c :=
      (Select.cellList_transport_perm σ χ c).mem_iff.mpr (List.mem_map_of_mem ha)
    rw [cellOrbit_iff_aut_of_orbitCompleteAt (orbitCompleteAt_of_goodCell hA') hσa,
        cellOrbit_iff_aut_of_orbitCompleteAt (orbitCompleteAt_of_goodCell hA) ha]
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
  · have hA' : ¬ GoodCell (relabelAdj σ adj) (transportColouring σ χ) c :=
      fun h => hA ((goodCell_transport_iff σ).mp h)
    rw [verified_deepenCellSupply_of_shut hA', verified_deepenCellSupply_of_shut hA,
        wordReach_nil_iff, wordReach_nil_iff]
    exact ⟨fun h => σ.injective h, fun h => congrArg σ h⟩

/-! ## 8. ★★★ `①` AT THE CELL-INDEXED FUSED OBJECT

The capstone of design `B`. `Select.selNodeC_canonizer` asks for `KeyEquivariant` plus
`CellOrbitTransport`, and §7 supplies the second with **no `SupplyEquivariant`, no equivariant
reference supply, and no completeness theorem about deepen** — only the guard's verdict transports. -/

/-- The cell-indexed deepening supply: each cell judged by descents anchored in itself. -/
def deepenCellSupplyC : Select.CellSupply n := fun c => deepenCellSupply c

theorem cellOrbitTransport_deepenCellSupplyC :
    Select.CellOrbitTransport (deepenCellSupplyC (n := n)) :=
  fun σ adj χ c _ _ ha hb => cellOrbit_transport_deepenCellSupply σ adj χ c ha hb

/-- **★★★ `①` FOR THE CELL-INDEXED FUSED OBJECT AT THE GUARDED CELL-ANCHORED SUPPLY** — sound,
complete and flag-iso-invariant, with no hypothesis beyond the key's.

This is the statement the node-global object cannot have: `probe_offbranch2/3.py` exhibit a CFI node
at depth 1 where the node-global list gives a cell count of `1` under one labelling and `2` under its
transport, **with the guard open on both sides**. -/
theorem deepenCell_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (deepenCellSupplyC (n := n)))) :=
  Select.selNodeC_canonizer Force.keyEquivariant_lookahead cellOrbitTransport_deepenCellSupplyC

/-! ### 8a. Composing with another supply — the shape the record append needs

Where the guard is **open**, deepen alone already realises the full `IsColAut`-orbit relation on the
cell, and soundness caps any additional generators from above — so the union is *exactly* the orbit
relation however many extra generators the left factor contributes. Where it is **shut**, deepen
emits `[]` and the union is the left factor's own relation, which must transport on its own.

⟹ appending is free on the open side and inherits on the shut side. This is why the record supply can
be carried along without its non-equivariant `kernelSupply` interfering wherever the guard fires. -/

theorem verified_append_deepenCell_of_shut {R : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (h : ¬ GoodCell adj χ c) :
    verified (Deck.appendSupply R (deepenCellSupply (n := n) c)) adj χ = verified R adj χ := by
  unfold verified gens Deck.appendSupply deepenCellSupply
  rw [if_neg h]
  simp

/-- On the open side the appended relation **is** the orbit relation on the cell: `⊆` by soundness
(every verified generator is an `IsColAut`), `⊇` by the guard (`wordReach_mono` from deepen's own
half). No property of `R` is used. -/
theorem cellOrbit_append_iff_aut_of_goodCell {R : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (h : GoodCell adj χ c) {u : Fin n} (hu : u ∈ Select.cellList χ c) {w : Fin n} :
    WordReach (verified (Deck.appendSupply R (deepenCellSupply (n := n) c)) adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w := by
  refine ⟨wordReach_imp_isColAut_any, ?_⟩
  rintro ⟨β, hβ, rfl⟩
  refine wordReach_mono (fun g hg => mem_verified_appendSupply_right ?_)
    (orbitCompleteAt_of_goodCell h u hu β hβ)
  rwa [verified_deepenCellSupply_of_open h]

/-- **★★ THE APPEND CARRIES `CellOrbitTransport`**, given only that the left factor's own relation
transports on cells where deepen's guard is shut. -/
theorem cellOrbitTransport_append {R : Supply n}
    (hR : ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n),
      WordReach (verified R (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
        ↔ WordReach (verified R adj χ) a b) :
    Select.CellOrbitTransport (fun c => Deck.appendSupply R (deepenCellSupply (n := n) c)) := by
  intro σ adj χ c a b ha _hb
  by_cases hA : GoodCell adj χ c
  · have hA' := goodCell_transport σ hA
    have hσa : σ a ∈ Select.cellList (transportColouring σ χ) c :=
      (Select.cellList_transport_perm σ χ c).mem_iff.mpr (List.mem_map_of_mem ha)
    rw [cellOrbit_append_iff_aut_of_goodCell hA' hσa, cellOrbit_append_iff_aut_of_goodCell hA ha]
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
  · have hA' : ¬ GoodCell (relabelAdj σ adj) (transportColouring σ χ) c :=
      fun h => hA ((goodCell_transport_iff σ).mp h)
    rw [verified_append_deepenCell_of_shut hA', verified_append_deepenCell_of_shut hA]
    exact hR σ adj χ a b

/-- The instance for an equivariant left factor — e.g. `foldSupplyFast ++ deckSupply ++ deck2Supply`.
(`kernelSupply` is provably not `GensEquivariant`; it enters through `OrbitPrune.SameOrbits` against
an equivariant reference, which is the next increment.) -/
theorem cellOrbitTransport_append_of_supplyEquivariant {R : Supply n}
    (hR : SupplyTransport.SupplyEquivariant R) :
    Select.CellOrbitTransport (fun c => Deck.appendSupply R (deepenCellSupply (n := n) c)) :=
  cellOrbitTransport_append
    (fun σ adj χ _a _b => SupplyTransport.wordReach_conj_iff (fun g => hR σ adj χ g))

/-- **★★★ `①` AT THE APPENDED CELL-INDEXED OBJECT.** -/
theorem deepenCell_append_canonizer {key : Force.Key n} (hk : Force.KeyEquivariant key)
    {R : Supply n} (hR : SupplyTransport.SupplyEquivariant R) :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) key
          (fun c => Deck.appendSupply R (deepenCellSupply (n := n) c)))) :=
  Select.selNodeC_canonizer hk (cellOrbitTransport_append_of_supplyEquivariant hR)

end Deepen
end ChainDescent
