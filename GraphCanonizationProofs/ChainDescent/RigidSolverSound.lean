import ChainDescent.RigidSolverInterface

/-!
# P3-Sound — soundness is free (the relabelling-emit solver), and the ① content isolates to one `gen`

This module discharges the `PtSound` obligation of the rigid solver **unconditionally**, via the C# B1c/B3
*verify-by-reconstruction* design lifted to Lean: a solver that emits a **relabelling of the pointed graph**
(`ptForm`) is sound *by construction* — two vertices with the same form are carried onto each other by the very
relabelling the forms exhibit. Combined with P3-I this means:

* **`PtSound` is free** (`ptSound_emitLabel`, any `gen`).
* **`PtIsoInvariant` reduces to `GenEquivariant gen`** (`ptIsoInvariant_emitLabel`) — the labelling `gen` chooses
  must transport correctly under relabelling.

So the *entire* `①` content of Algorithm R collapses to **one object: an iso-invariant canonical labelling
`gen`** of the pointed residue. The remaining work (P3-F₂ / P3-ring) is exactly *building a polynomial such
`gen`* (and `hemit`: it must not flag) — which is graph canonization of the F₂/ring-linear residue. The
polynomial-ness (`②`) and the flag (`③`, where poly fails) are all that is left; soundness and the iso-invariance
*reduction* are done here.

The reflection `colAut_of_ptForm_eq` is `RigidSeal.r0a_core` generalised off the discretizing regime to an
arbitrary pair of permutations — the same three-component decomposition (labelled adjacency, pin, colour order).
-/

namespace ChainDescent
namespace RigidSolver

open ChainDescent.Descend
open ChainDescent.Force
open ChainDescent.Consume (IsColAut)
open ChainDescent.RigidSeal

variable {n : Nat}

/-! ## 1. The pointed-graph form and the reflection (soundness core) -/

/-- **The canonical-form payload**: the pointed coloured graph `(adj, χ, v)` relabelled by `π`, encoded as a
`List Nat` — the pin's image, the transported colouring in index order, and the relabelled adjacency. Injective
in the triple `(relabelAdj π adj, transportColouring π χ, π v)`, which is what makes emitting it *sound*. -/
def ptForm (π : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  (π v).val :: ((List.finRange n).map (fun i => χ (π.symm i)) ++ flatten (labelledAdj π adj))

/-- **The reflection core** (`r0a_core` for arbitrary permutations). Equal labelled adjacency + equal pin +
equal colour order for two permutations `πu, πw` furnish a colour-automorphism `σ = πw⁻¹ πu` carrying `u ↦ w`. -/
theorem colAut_of_labelledAdj_eq (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (πu πw : Equiv.Perm (Fin n))
    (hlm : labelledAdj πu adj = labelledAdj πw adj)
    (hpin : πu u = πw w)
    (hcol : ∀ i : Fin n, χ (πu.symm i) = χ (πw.symm i)) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  refine ⟨πw⁻¹ * πu, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    have hEq := congrFun (congrFun hlm (πu i)) (πu j)
    simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
    change adj.adj (πw.symm (πu i)) (πw.symm (πu j)) = adj.adj i j
    exact hEq.symm
  · intro v'
    change χ (πw.symm (πu v')) = χ v'
    have := hcol (πu v')
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  · change πw.symm (πu u) = w
    rw [hpin, Equiv.symm_apply_apply]

/-- **★★ Soundness reflection.** Two pins with the *same* emitted `ptForm` are carried onto each other by a
colour-automorphism — the pointed-graph analog of `colAut_of_leafColKey_eq`, off the discretizing regime. -/
theorem colAut_of_ptForm_eq (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (πu πw : Equiv.Perm (Fin n)) (hkey : ptForm πu adj χ u = ptForm πw adj χ w) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  unfold ptForm at hkey
  obtain ⟨hhead, htail⟩ := List.cons.inj hkey
  have hlen : ((List.finRange n).map (fun i => χ (πu.symm i))).length
      = ((List.finRange n).map (fun i => χ (πw.symm i))).length := by simp
  obtain ⟨hmap, hflat⟩ := List.append_inj htail hlen
  have hpin : πu u = πw w := Fin.val_injective hhead
  have hlm : labelledAdj πu adj = labelledAdj πw adj := flatten_injective hflat
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map] at hmap
  have hcol : ∀ i, χ (πu.symm i) = χ (πw.symm i) := fun i => congrFun (List.ofFn_inj.mp hmap) i
  exact colAut_of_labelledAdj_eq adj χ u w πu πw hlm hpin hcol

/-! ## 2. The relabelling-emit solver — `PtSound` is free -/

/-- **The relabelling-emit solver.** Given a labelling oracle `gen` (which chooses a permutation, or flags), emit
that permutation's `ptForm` — a genuine relabelling. Soundness holds for *any* `gen`. -/
def emitLabel (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n))) : PtSolver n :=
  fun adj χ v => (gen adj χ v).map (fun π => ptForm π adj χ v)

/-- **★★★ P3-Sound — soundness is free.** For any labelling oracle, the relabelling-emit solver is `PtSound`:
equal non-flag forms are relabellings exhibiting the colour-automorphism. (C# B1c/B3 verify-by-reconstruction.) -/
theorem ptSound_emitLabel (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n))) :
    PtSound (emitLabel gen) := by
  intro adj χ u w c hu hw
  simp only [emitLabel] at hu hw
  cases hgu : gen adj χ u with
  | none => rw [hgu] at hu; simp at hu
  | some πu =>
    cases hgw : gen adj χ w with
    | none => rw [hgw] at hw; simp at hw
    | some πw =>
      rw [hgu, Option.map_some] at hu
      rw [hgw, Option.map_some] at hw
      exact colAut_of_ptForm_eq adj χ u w πu πw
        ((Option.some.inj hu).trans (Option.some.inj hw).symm)

/-! ## 3. The iso-invariance reduction — `PtIsoInvariant ⟸ GenEquivariant` -/

/-- **The labelling-oracle equivariance obligation.** The canonical labelling of the *relabelled* graph is the
original's, post-composed to undo the relabelling: `gen (relabel σ ·) = (gen ·).map (· * σ⁻¹)`. This is the
defining property of a canonical labelling, and the sole remaining `①` obligation on `gen`. -/
def GenEquivariant (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n))) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    gen (relabelAdj σ adj) (transportColouring σ χ) (σ v) = (gen adj χ v).map (fun π => π * σ⁻¹)

/-- The form transports as a permutation shift: relabelling the input by `σ` and evaluating at `π` is the same
as evaluating the original at `π * σ`. -/
theorem ptForm_transport (π σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    ptForm π (relabelAdj σ adj) (transportColouring σ χ) (σ v) = ptForm (π * σ) adj χ v := by
  have hsymm : ∀ i, (π * σ).symm i = σ.symm (π.symm i) := by
    intro i
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hlab : labelledAdj π (relabelAdj σ adj) = labelledAdj (π * σ) adj := by
    funext i j; simp only [labelledAdj, relabelAdj_adj, hsymm]
  simp only [ptForm, Equiv.Perm.mul_apply, transportColouring, hsymm, hlab]

/-- **★★ P3-Sound(b) — the iso-invariance reduction.** If the labelling oracle is equivariant, the emit solver is
`PtIsoInvariant`. Feeds `keyEquivariant_skOf` ⟹ `compKey`'s `①` obligation. So the whole `①` content is now
exactly `GenEquivariant gen`. -/
theorem ptIsoInvariant_emitLabel
    (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n)))
    (h : GenEquivariant gen) : PtIsoInvariant (emitLabel gen) := by
  intro σ adj χ v
  simp only [emitLabel]
  rw [h σ adj χ v, Option.map_map]
  have hfun : (fun π => ptForm π (relabelAdj σ adj) (transportColouring σ χ) (σ v)) ∘ (fun π => π * σ⁻¹)
            = (fun π => ptForm π adj χ v) := by
    funext π
    show ptForm (π * σ⁻¹) (relabelAdj σ adj) (transportColouring σ χ) (σ v) = ptForm π adj χ v
    rw [ptForm_transport]
    congr 1
    group
  rw [hfun]

/-! ## 4. Capstone — the whole rigid seam closes on `GenEquivariant` + `hemit`

Composing P3-I (`keyEquivariant_skOf` / `solverSeparates_skOf`) with P3-Sound (`ptSound_emitLabel` /
`ptIsoInvariant_emitLabel`) and `compKey` (`RigidSeal`): the composite force key
`compKey (skOf (emitLabel gen))` discharges **both** of `compKey`'s obligations — `KeyEquivariant` and (per rigid
cell) `NodeResolved` — with soundness **free**, leaving exactly two obligations on the concrete labelling `gen`:

* `GenEquivariant gen` — `gen` is an iso-invariant canonical labelling (the whole `①` content);
* `hemit` — `gen` does not flag on the cell (the completeness / `②`-poly content; where it flags = the residue).

Building a **polynomial** such `gen` (`P3-F₂` via RREF / `P3-ring` via finite Smith, once `P2` supplies the
extraction) is all that remains of Algorithm R's `①`. -/

/-- **★★★ The `①` obligation of `compKey`, via the emit solver.** `KeyEquivariant (compKey (skOf (emitLabel gen)))`
from just `GenEquivariant gen`. -/
theorem keyEquivariant_compKey_emitLabel
    (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n)))
    (hgen : GenEquivariant gen) :
    KeyEquivariant (compKey (skOf (emitLabel gen))) :=
  keyEquivariant_compKey _ (keyEquivariant_skOf _ (ptIsoInvariant_emitLabel gen hgen))

/-- **★★★ The firing obligation of `compKey`, via the emit solver.** `NodeResolved` on any rigid cell where the
labelling emits — soundness is free (`ptSound_emitLabel`), so the *only* hypothesis is `hemit` (no-flag). Where
`gen` flags, the pair stays in the residue `¬HandledS` = non-linear rigid. -/
theorem nodeResolved_compKey_emitLabel
    (gen : AdjMatrix n → Colouring n → Fin n → Option (Equiv.Perm (Fin n)))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hemit : ∀ u ∈ branches χ, ¬ Discrete (lookData adj χ u).col → (emitLabel gen adj χ u).isSome)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel gen))) S adj χ :=
  nodeResolved_compKey_of_rigid _ S adj χ hnd
    (solverSeparates_skOf (emitLabel gen) adj χ (ptSound_emitLabel gen) hemit) hrigid

end RigidSolver
end ChainDescent
