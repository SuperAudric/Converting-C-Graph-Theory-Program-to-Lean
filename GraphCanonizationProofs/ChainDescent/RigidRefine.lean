import ChainDescent.RigidGen
import ChainDescent.ForcingModel
import ChainDescent.RigidSolveF2

/-!
# The concrete `ref` = `refineByFrame` — ROUTE B′ (coordinate-free forcing)

The concrete rigid refinement `ref adj χ` that `RigidGen.genOfRef` consumes, built **Route B′**: over P2's
already-built `rowspace` / `Forced`, coordinate-free — **not** the χ-frame.

**Why not the frame (the de-risk finding, 2026-07-25).** `RigidFrame.framedRREF_transport` carries a
`(h : Discrete χ)` hypothesis (via `frameRow_transport` → `rankInv_transport`, which needs injectivity of the
rank map). But `ref` is applied to **non-discrete cell colourings**, and on a non-discrete cell there is provably
no equivariant column tiebreak (the "no iso-invariant within-cell vertex pick" wall). So the χ-frame cannot prove
the *unconditional* `RefEquivariant` that `RigidGen.genEquivariant_genOfRef` consumes. The frame conflated the
solving *algorithm* (`②`) with the *equivariance argument* (`①`).

**The fix.** The per-vertex datum is coordinate-free forcing: *"is `e_v` forced (`e_v ∈ rowspace H`), and if so to
what value"* = P2's `certificate_of_forced_notMem` read per vertex. This transports **unconditionally** because
`rowspace` transports under the linear equiv `transportVec σ` (`span` commutes with a linear iso — no `Discrete χ`,
no frame). It also handles the **mixed** residue (`CellsAreOrbits` false with only *some* rigid decisions): the
reader pins exactly the forced (rigid) coordinates and leaves the gauge/kernel coordinates unforced (tie preserved
= consume's job). It needs **no uniqueness** — `unique_solution_of_rigid` assumes the *whole* system rigid, which
the mixed residue violates.

## Build order
1. **`transportVec σ`** — the `ZMod 2` analog of `RigidFrame.transportRow` (precomposition by `σ⁻¹`), as a linear
   map — and **`rowspace_transport`** (`(rowspace H).map (transportVec σ) = rowspace (H.image (transportVec σ))`).
   *(this file, below)*
2. `forcedVal` (per-vertex forced value over `rowspace`/target) + its transport. *(next)*
3. `refineByFrame` + `RefEquivariant` (unconditional) ⟹ feed `RigidGen.genEquivariant_genOfRef`. *(next)*
-/

namespace ChainDescent
namespace RigidRefine

open ChainDescent.ForcingCircuits

variable {n : Nat}

/-! ## Step 1 — the `ZMod 2` transport equiv and `rowspace_transport` -/

/-- **The `ZMod 2` vertex-column transport**, the analog of `RigidFrame.transportRow` for assignments
`x : Fin n → ZMod 2`: read `x` at `σ⁻¹ u` (precomposition by `σ.symm`). A linear map (indeed a linear equiv, but
the map form is all `rowspace_transport` needs). This is how a codeword over the vertices of `adj` transports to
`relabelAdj σ adj`. -/
def transportVec (σ : Equiv.Perm (Fin n)) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := fun u => x (σ.symm u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem transportVec_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) (u : Fin n) :
    transportVec σ x u = x (σ.symm u) := rfl

/-- **★ `rowspace` transports.** The row space of the σ-relabelled system is the `transportVec σ`-image of the row
space — `span` commutes with the linear map `transportVec σ` (`Submodule.map_span`). This is the single new lemma
Route B′ needs: it makes the coordinate-free forced-reader equivariant with **no** `Discrete χ` and **no** frame. -/
theorem rowspace_transport (σ : Equiv.Perm (Fin n)) (H : Finset (Fin n → ZMod 2)) :
    (rowspace H).map (transportVec σ) = rowspace (H.image (transportVec σ)) := by
  unfold rowspace
  rw [Submodule.map_span, Finset.coe_image]

end RigidRefine
end ChainDescent
