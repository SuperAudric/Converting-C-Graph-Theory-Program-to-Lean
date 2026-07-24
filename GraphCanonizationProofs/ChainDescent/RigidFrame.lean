import ChainDescent.RigidRREF
import ChainDescent.RigidSeal

/-!
# `gen` sub-brick (C) — the χ-frame: the χ-rank column order makes the framed RREF σ-invariant

Brick (B) (`RigidRREF.lean`) proved the executable F₂ RREF `rrefCanon` is a canonical function of the row
*space* — **given a fixed column order** `0…m-1`. That is not enough for an iso-invariant labelling `gen`:
**RREF is NOT column-equivariant** — permuting the columns changes which column is "leftmost", hence changes
the pivot set (e.g. `span{[1,1]}` pivots at column 0, but swap the two columns and it still pivots at position
0, now the *other* actual column). So the column order cannot come from the raw vertex labels.

The fix is the **χ-frame**: order the columns by the iso-invariant **χ-rank** (`Colouring.vertexRank`, via
`rankInv`). This is exactly the `leafMatrix` pattern (`Descend.leafMatrix_transport`): reading a vertex-indexed
object in rank order makes it *literally* invariant under a relabelling `σ`, because `rankInv` transports
(`RigidSeal.rankInv_transport`: `rankInv (transportColouring σ χ) = σ ∘ rankInv χ`). So the χ-framed system is
literally σ-invariant, and therefore so is its `rrefCanon`.

* `frameRow χ r` — read a row `r : Fin n → Bool` (F₂ over vertex-columns) in χ-rank order.
* `frameRow_transport` / `frameSys_transport` — the framed row/system is literally σ-invariant, when the row
  transports as `r ↦ r ∘ σ⁻¹` (the standard vertex-column transport, `transportRow`).
* **`framedRREF_transport`** — hence the χ-framed `rrefCanon` is σ-invariant. This reduces `gen`'s
  `GenEquivariant` to the *extraction* transporting as `H ↦ H.map (transportRow σ)` (a P2 / extraction property,
  carried) — the RREF/frame layer no longer contributes any equivariance obligation.
-/

namespace ChainDescent
namespace RigidFrame

open ChainDescent.Descend
open ChainDescent.RigidRREF

variable {n : Nat}

/-- A row over the vertices of `adj` transports to `relabelAdj σ adj` by precomposition with `σ⁻¹`
(the F₂/vertex-column analog of `transportColouring`). -/
def transportRow (σ : Equiv.Perm (Fin n)) (r : Fin n → Bool) : Fin n → Bool :=
  fun u => r (σ.symm u)

/-- **The χ-framed row.** Read `r`'s F₂ entries in χ-**rank** order (columns = vertices, ordered by the
iso-invariant rank). Length `n`. This is `leafMatrix`'s idea for a single F₂ vector. -/
def frameRow (χ : Colouring n) (r : Fin n → Bool) : List Bool :=
  (List.finRange n).map (fun rank => r (rankInv χ rank))

@[simp] theorem length_frameRow (χ : Colouring n) (r : Fin n → Bool) :
    (frameRow χ r).length = n := by simp [frameRow]

/-- The χ-framed system — every extracted row read in χ-rank order. -/
def frameSys (χ : Colouring n) (H : List (Fin n → Bool)) : List (List Bool) :=
  H.map (frameRow χ)

/-- **★ The framed row is literally σ-invariant.** Reading `r ∘ σ⁻¹` in the transported χ-rank order gives the
same list as reading `r` in the original χ-rank order — because `rankInv` transports (`RigidSeal.rankInv_transport`),
so `σ⁻¹ (rankInv (transportColouring σ χ) rank) = rankInv χ rank`. -/
theorem frameRow_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (h : Discrete χ) (r : Fin n → Bool) :
    frameRow (transportColouring σ χ) (transportRow σ r) = frameRow χ r := by
  unfold frameRow
  refine List.map_congr_left (fun rank _ => ?_)
  show transportRow σ r (rankInv (transportColouring σ χ) rank) = r (rankInv χ rank)
  unfold transportRow
  rw [RigidSeal.rankInv_transport σ χ h rank, Equiv.symm_apply_apply]

/-- The whole framed system is literally σ-invariant, when each extracted row transports as `transportRow σ`. -/
theorem frameSys_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (h : Discrete χ)
    (H : List (Fin n → Bool)) :
    frameSys (transportColouring σ χ) (H.map (transportRow σ)) = frameSys χ H := by
  unfold frameSys
  rw [List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  exact frameRow_transport σ χ h r

/-- **★★ (C) — the χ-framed RREF transports.** Ordering columns by the iso-invariant χ-rank makes the framed
system *literally* σ-invariant (the `leafMatrix` pattern — NOT column-equivariance of RREF, which is false), so
its canonical RREF (`rrefCanon`, brick B) is σ-invariant. This reduces `gen`'s `GenEquivariant` to the
extraction transporting as `H ↦ H.map (transportRow σ)` (a P2/extraction property, carried); the RREF/frame
layer contributes no further equivariance obligation. -/
theorem framedRREF_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (h : Discrete χ)
    (H : List (Fin n → Bool)) :
    rrefCanon n (frameSys (transportColouring σ χ) (H.map (transportRow σ)))
      = rrefCanon n (frameSys χ H) := by
  rw [frameSys_transport σ χ h H]

/-- The framed RREF is also (from brick B) a canonical function of the framed *code*: two extractions of the
same F₂ row space (in the same χ-frame) give the same canonical RREF. Robustness to how the extraction presents
its generators. -/
theorem framedRREF_span_invariant (χ : Colouring n) (H₁ H₂ : List (Fin n → Bool))
    (hsp : ∀ w, Kernel.Spans n (frameSys χ H₁) w ↔ Kernel.Spans n (frameSys χ H₂) w) :
    rrefCanon n (frameSys χ H₁) = rrefCanon n (frameSys χ H₂) :=
  rrefCanon_eq_of_span_eq
    (by intro r hr; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr; simp)
    (by intro r hr; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr; simp)
    hsp

end RigidFrame
end ChainDescent
