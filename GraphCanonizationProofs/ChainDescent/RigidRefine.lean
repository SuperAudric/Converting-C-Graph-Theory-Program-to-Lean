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
open ChainDescent.Descend
open ChainDescent.RigidGen
open ChainDescent.Force
open ChainDescent.RigidSolver
open ChainDescent.RigidSeal
open ChainDescent.Consume (IsColAut)

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

/-- `transportVec σ` is injective (it precomposes by the bijection `σ.symm`). -/
theorem transportVec_injective (σ : Equiv.Perm (Fin n)) :
    Function.Injective (transportVec σ) := by
  intro x y h
  funext u
  have := congrFun h (σ u)
  simpa [transportVec_apply] using this

/-- The transport of the `v`-th unit codeword `e_v` is the `σv`-th unit codeword: `transportVec σ (e_v) = e_(σv)`.
The bridge that turns `rowspace_transport` into a per-vertex membership fact. -/
theorem transportVec_e (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    transportVec σ (Pi.single v (1 : ZMod 2)) = Pi.single (σ v) (1 : ZMod 2) := by
  funext u
  rw [transportVec_apply]
  by_cases h : u = σ v
  · subst h; rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · have hh : σ.symm u ≠ v := by
      intro hc; apply h; rw [← hc, Equiv.apply_symm_apply]
    rw [Pi.single_eq_of_ne hh, Pi.single_eq_of_ne h]

/-- **★ Per-vertex forcedness transports.** `e_(σv)` is forced in the σ-relabelled row space iff `e_v` is forced
in the original — via `rowspace_transport` + `transportVec_e` + injectivity. The coordinate-free "is `v` a rigid
(pinned) coordinate" is a σ-invariant, with **no** `Discrete χ` and **no** frame. -/
theorem e_mem_rowspace_transport (σ : Equiv.Perm (Fin n)) (H : Finset (Fin n → ZMod 2)) (v : Fin n) :
    (Pi.single (σ v) (1 : ZMod 2) ∈ rowspace (H.image (transportVec σ)))
      ↔ (Pi.single v (1 : ZMod 2) ∈ rowspace H) := by
  rw [← rowspace_transport, ← transportVec_e]
  constructor
  · intro h
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp h
    rwa [transportVec_injective σ hfy] at hy
  · intro h
    exact Submodule.mem_map.mpr ⟨_, h, rfl⟩

/-! ## Step 2 — the per-vertex forced-value reader and its transport -/

/-- **The coordinate-free forced-value reader.** For a system `H` with a witness solution `x₀` (a particular
assignment), vertex `v` reads:
* `some (x₀ v)` when `e_v ∈ rowspace H` — `v` is a **forced (rigid) coordinate**, so `x₀ v` is its canonical value
  (constant across the whole solution space, since `e_v ⊥ ker H`);
* `none` when `e_v ∉ rowspace H` — `v` is a **gauge / free coordinate** (its `x₀`-value is arbitrary), left
  unrefined = tie preserved = consume's job.

This is exactly P2's forcedness read per vertex. Noncomputable (membership in `rowspace` is a `Prop`; the `①`
proof needs no executability — the executable route is the `②` RREF, brick C). -/
noncomputable def forcedVal (H : Finset (Fin n → ZMod 2)) (x₀ : Fin n → ZMod 2) (v : Fin n) :
    Option (ZMod 2) := by
  classical
  exact if Pi.single v (1 : ZMod 2) ∈ rowspace H then some (x₀ v) else none

/-- **★★ The forced-value reader is a vertex-invariant.** On the σ-relabelled system (row space imaged by
`transportVec σ`, witness `transportVec σ x₀`), vertex `σv` reads exactly what vertex `v` reads on the original.
Unconditional — the heart of Route B′'s `①`. -/
theorem forcedVal_transport (σ : Equiv.Perm (Fin n)) (H : Finset (Fin n → ZMod 2))
    (x₀ : Fin n → ZMod 2) (v : Fin n) :
    forcedVal (H.image (transportVec σ)) (transportVec σ x₀) (σ v) = forcedVal H x₀ v := by
  classical
  unfold forcedVal
  have hval : (transportVec σ x₀) (σ v) = x₀ v := by
    rw [transportVec_apply, Equiv.symm_apply_apply]
  by_cases h : Pi.single v (1 : ZMod 2) ∈ rowspace H
  · rw [if_pos ((e_mem_rowspace_transport σ H v).mpr h), if_pos h, hval]
  · rw [if_neg (fun hc => h ((e_mem_rowspace_transport σ H v).mp hc)), if_neg h]

/-! ## Step 3 — the concrete `refineByFrame` and its unconditional `RefEquivariant` -/

/-- **The extraction's transport hypothesis (carried).** The system + witness the extraction reads off `(adj, χ)`
transports under `σ`: the row set is imaged by `transportVec σ`, and the witness assignment by `transportVec σ`.
This is the P2/extraction property (`gForce`/`encodeFreeFast` realizing the F₂ system) — carried per family, the
same object as `ForcingModel.bridge`'s graph realization. It is the *only* obligation `refineByFrame`'s `①` needs. -/
def RefExtractEquivariant
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    extract (relabelAdj σ adj) (transportColouring σ χ)
      = ((extract adj χ).1.image (transportVec σ), transportVec σ (extract adj χ).2)

/-- The per-vertex forced reader assembled from an extraction. -/
noncomputable def frameRead
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Option (ZMod 2) :=
  forcedVal (extract adj χ).1 (extract adj χ).2 v

/-- **The reader is a vertex-invariant**, given the carried extraction transport — `frameRead` on the σ-relabelled
node at `σv` reads what the original reads at `v`. `forcedVal_transport` pulled through `RefExtractEquivariant`. -/
theorem frameRead_transport
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n)
    (χ : Colouring n) (v : Fin n) :
    frameRead extract (relabelAdj σ adj) (transportColouring σ χ) (σ v) = frameRead extract adj χ v := by
  unfold frameRead
  rw [hext σ adj χ]
  exact forcedVal_transport σ (extract adj χ).1 (extract adj χ).2 v

/-- Encode a forced value into the refined colour's low digit: `none` (gauge/free) ↦ 0, `some 0` ↦ 1, `some 1` ↦ 2.
Injective on `Option (ZMod 2)`, so `3 * χ v + encOpt …` genuinely refines χ. -/
def encOpt : Option (ZMod 2) → Nat
  | none => 0
  | some x => 1 + x.val

/-- **The concrete rigid refinement `ref = refineByFrame` (Route B′).** Refine χ by each vertex's coordinate-free
forced value: `3 * χ v + encOpt (frameRead …)`. Forced (rigid) coords split off by their value; gauge/free coords
(`none` ↦ 0) keep χ's tie = consume's job. Parameterized by the extraction; noncomputable (the `①` proof needs no
executability). -/
noncomputable def refineByFrame
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (adj : AdjMatrix n) (χ : Colouring n) : Colouring n :=
  fun v => 3 * χ v + encOpt (frameRead extract adj χ v)

/-- **★★★ Route B′ payoff — `refineByFrame` is `RefEquivariant`, UNCONDITIONALLY.** No `Discrete χ`, no frame:
`χ` transports pointwise and `frameRead` is a vertex-invariant (`frameRead_transport`). The whole `①`/equivariance
obligation of the concrete rigid `ref` reduces to the carried `RefExtractEquivariant`. -/
theorem refEquivariant_refineByFrame
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) :
    RefEquivariant (refineByFrame extract) := by
  intro σ adj χ
  funext u
  have hr := frameRead_transport extract hext σ adj χ (σ.symm u)
  rw [Equiv.apply_symm_apply] at hr
  simp only [refineByFrame, transportColouring, hr]

/-- **★★★ (D) capstone, concretely.** The rigid **linear** `①` (`compKey`'s `KeyEquivariant`) closes for the
concrete `refineByFrame` on the single carried obligation `RefExtractEquivariant` — composing
`refEquivariant_refineByFrame` with `RigidGen.keyEquivariant_compKey_genOfRef`. No `Discrete χ`, no frame; (D) is
untouched. -/
theorem keyEquivariant_compKey_refineByFrame
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) :
    KeyEquivariant (compKey (skOf (emitLabel (genOfRef (refineByFrame extract))))) :=
  keyEquivariant_compKey_genOfRef (refineByFrame extract) (refEquivariant_refineByFrame extract hext)

/-- **★★★ (D) firing capstone, concretely.** `NodeResolved` fires on any rigid cell where `refineByFrame` is
discrete — soundness is free (P3-Sound), so the only hypotheses are `refineByFrame` discrete on the branch
(⟸ the extraction forces every rigid coordinate, carried per-family) and rigidity. Does **not** need `hext`
(firing is equivariance-free). Instantiates `RigidGen.nodeResolved_compKey_genOfRef`. -/
theorem nodeResolved_compKey_refineByFrame
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hdisc : ∀ u ∈ branches χ, ¬ Discrete (lookData adj χ u).col → Discrete (refineByFrame extract adj χ))
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel (genOfRef (refineByFrame extract))))) S adj χ :=
  nodeResolved_compKey_genOfRef (refineByFrame extract) S adj χ hnd hdisc hrigid

/-- **Non-vacuity of `RefExtractEquivariant`.** The trivial extraction (empty system, zero witness) satisfies it —
`∅` images to `∅` and `transportVec σ 0 = 0`. So the carried hypothesis is genuinely satisfiable (the meaningful
instances are the P2 `gForce`/`encodeFreeFast` extraction; forced-coordinate non-triviality is measured in
`scratchpad/probe_forced.py`). With it, `refineByFrame` is `3 * χ` — pure χ, forcing nothing (all coords gauge). -/
theorem refExtractEquivariant_trivial :
    RefExtractEquivariant (n := n) (fun _ _ => (∅, 0)) := by
  intro σ adj χ
  simp [Finset.image_empty, map_zero]

end RigidRefine
end ChainDescent
