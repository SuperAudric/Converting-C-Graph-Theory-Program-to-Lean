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

/-! ## Step 4 — a concrete extraction: generic local-row transport + the adjacency instance

`RefExtractEquivariant` needs only that the extraction **transports** (structural); the extraction's
**faithfulness** (that its system forces the actual rigid coordinates) is the carried `ForcingModel.bridge`,
separate. Step A packages *any* per-vertex local extraction; Step B is a concrete non-vacuous instance (the
faithful per-family CFI extraction plugs into Step A the same way). -/

/-- A local row-builder is equivariant when the row at `σi` on the σ-relabelled node is the `transportVec σ`
of the row at `i` — the pointwise transport that lifts to the whole extracted system. -/
def RowAtEquivariant (rowAt : AdjMatrix n → Colouring n → Fin n → (Fin n → ZMod 2)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (i : Fin n),
    rowAt (relabelAdj σ adj) (transportColouring σ χ) (σ i) = transportVec σ (rowAt adj χ i)

/-- The witness assignment is equivariant (transports as `transportVec σ`). -/
def WitEquivariant (wit : AdjMatrix n → Colouring n → (Fin n → ZMod 2)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    wit (relabelAdj σ adj) (transportColouring σ χ) = transportVec σ (wit adj χ)

/-- **The extraction from a local row-builder + witness:** rows = `{rowAt adj χ i : i}`, witness = `wit adj χ`. -/
def extractOf (rowAt : AdjMatrix n → Colouring n → Fin n → (Fin n → ZMod 2))
    (wit : AdjMatrix n → Colouring n → (Fin n → ZMod 2)) :
    AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  fun adj χ => (Finset.univ.image (rowAt adj χ), wit adj χ)

/-- **★ Step A — any equivariant local extraction transports.** `RefExtractEquivariant (extractOf rowAt wit)`
from `RowAtEquivariant rowAt` + `WitEquivariant wit`: the row set transports by reindexing the `Finset.image`
along the bijection `σ` (`univ.image σ = univ`, then `Finset.image_image` + the pointwise `RowAtEquivariant`);
the witness by `WitEquivariant`. The faithful per-family extraction discharges its `①` obligation **here**. -/
theorem refExtractEquivariant_extractOf
    (rowAt : AdjMatrix n → Colouring n → Fin n → (Fin n → ZMod 2))
    (wit : AdjMatrix n → Colouring n → (Fin n → ZMod 2))
    (hrow : RowAtEquivariant rowAt) (hwit : WitEquivariant wit) :
    RefExtractEquivariant (extractOf rowAt wit) := by
  intro σ adj χ
  simp only [extractOf, Prod.mk.injEq]
  refine ⟨?_, hwit σ adj χ⟩
  have hσ : (Finset.univ : Finset (Fin n)).image (⇑σ) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    exact Finset.mem_image.mpr ⟨σ.symm x, Finset.mem_univ _, by simp⟩
  calc Finset.univ.image (rowAt (relabelAdj σ adj) (transportColouring σ χ))
      = (Finset.univ.image (⇑σ)).image (rowAt (relabelAdj σ adj) (transportColouring σ χ)) := by rw [hσ]
    _ = Finset.univ.image (fun i => rowAt (relabelAdj σ adj) (transportColouring σ χ) (σ i)) := by
          rw [Finset.image_image]; rfl
    _ = Finset.univ.image (fun i => transportVec σ (rowAt adj χ i)) :=
          Finset.image_congr (fun i _ => hrow σ adj χ i)
    _ = (Finset.univ.image (rowAt adj χ)).image (transportVec σ) := by rw [Finset.image_image]; rfl

/-- Concrete row-builder: the F₂ adjacency row of `i` (`v ↦ adj i v mod 2`). A genuine graph invariant. -/
def rowAdj (adj : AdjMatrix n) (_χ : Colouring n) (i : Fin n) : Fin n → ZMod 2 :=
  fun v => (adj.adj i v : ZMod 2)

/-- Concrete witness: `χ` reduced mod 2. -/
def witChi (_adj : AdjMatrix n) (χ : Colouring n) : Fin n → ZMod 2 :=
  fun v => (χ v : ZMod 2)

theorem rowAtEquivariant_rowAdj : RowAtEquivariant (rowAdj (n := n)) := by
  intro σ adj χ i
  funext v
  simp only [rowAdj, transportVec_apply, relabelAdj_adj, Equiv.symm_apply_apply]

theorem witEquivariant_witChi : WitEquivariant (witChi (n := n)) := by
  intro σ adj χ
  funext v
  simp only [witChi, transportVec_apply, transportColouring]

/-- **★ Step B — the adjacency extraction transports.** A concrete, non-vacuous `RefExtractEquivariant` witness. -/
theorem refExtractEquivariant_adj : RefExtractEquivariant (extractOf (rowAdj (n := n)) witChi) :=
  refExtractEquivariant_extractOf rowAdj witChi rowAtEquivariant_rowAdj witEquivariant_witChi

/-- **★★★ Step C — the rigid linear `①`, CONCRETELY and UNCONDITIONALLY closed.** For the concrete extraction
`extractOf rowAdj witChi`, `refineByFrame`'s `RefEquivariant` holds with **no hypotheses**, so `compKey`'s
`KeyEquivariant` holds outright. The whole rigid-linear `①` machinery is thereby instantiated end-to-end; the only
remaining rigid-linear content is `hemit` (the extraction faithfully forces the rigid coordinates = the carried
`ForcingModel.bridge`), per family — where the faithful extraction replaces `rowAdj` via `refExtractEquivariant_extractOf`. -/
theorem keyEquivariant_compKey_refineByFrame_adj :
    KeyEquivariant (compKey (skOf (emitLabel
      (genOfRef (refineByFrame (extractOf (rowAdj (n := n)) witChi)))))) :=
  keyEquivariant_compKey_refineByFrame (extractOf rowAdj witChi) refExtractEquivariant_adj

/-! ## Step 5 — the `②` reduction: `hemit` (discreteness) ⟸ `ForcedSeparates` (faithfulness)

The `②`/firing side reduced to one clean, family-agnostic predicate — the mirror of Step A's `①` reduction.
`refineByFrame` discretizes exactly when the extraction's forced values separate co-cellular vertices; that
separation IS the per-family faithfulness (carried). On CFI it holds on the **rigid residue after consume peels
the `Z₂^β` gauge** (raw-cell gauge coords are `none` = tie = consume's job), so it is entangled with the
interleaving (R6), not a standalone CFI fact. -/

theorem encOpt_lt_three (o : Option (ZMod 2)) : encOpt o < 3 := by
  cases o with
  | none => decide
  | some x =>
    have hx : x.val < 2 := ZMod.val_lt x
    simp only [encOpt]; omega

theorem encOpt_injective : Function.Injective encOpt := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => simp only [encOpt] at hab; omega
  | some x =>
    cases b with
    | none => simp only [encOpt] at hab; omega
    | some y =>
      simp only [encOpt] at hab
      have hxy : x.val = y.val := by omega
      exact congrArg some (ZMod.val_injective 2 hxy)

/-- **The extraction's forced values SEPARATE co-cellular vertices** — distinct vertices of the same χ-colour get
distinct forced values (`frameRead`). This is the per-family faithfulness the `②`/firing needs; carried. On CFI it
holds on the rigid residue (after consume peels the gauge), i.e. entangled with the interleaving. -/
def ForcedSeparates
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u v : Fin n, χ u = χ v → frameRead extract adj χ u = frameRead extract adj χ v → u = v

/-- **★ Step 5 — the `②` reduction.** `hemit` for `refineByFrame` (= `Discrete (refineByFrame extract adj χ)`)
reduces to `ForcedSeparates`: the refined colour `3 * χ v + encOpt (frameRead …)` is injective because
`encOpt ∈ {0,1,2} < 3` splits it into the χ-digit and the forced-digit, and `ForcedSeparates` separates within a
χ-cell. Family-agnostic; any faithful extraction discharges `hemit` through this. -/
theorem hemit_of_forcedSeparates
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (adj : AdjMatrix n) (χ : Colouring n) (h : ForcedSeparates extract adj χ) :
    Discrete (refineByFrame extract adj χ) := by
  intro u v huv
  simp only [refineByFrame] at huv
  have hu := encOpt_lt_three (frameRead extract adj χ u)
  have hv := encOpt_lt_three (frameRead extract adj χ v)
  have hχ : χ u = χ v := by omega
  have hc : encOpt (frameRead extract adj χ u) = encOpt (frameRead extract adj χ v) := by omega
  exact h u v hχ (encOpt_injective hc)

/-- **★★★ The `②`/firing capstone, on the clean interface.** `NodeResolved` for `refineByFrame` reduces to
`ForcedSeparates` (the per-family faithfulness — the extraction's forced values separate co-cellular vertices) +
rigidity. Soundness is free (P3-Sound), `hext`-free (firing is equivariance-free). Combined with
`keyEquivariant_compKey_refineByFrame` (`①` ⟸ `RefExtractEquivariant`), the whole rigid-**linear** seal for
`refineByFrame` rests on exactly two per-family objects: `RefExtractEquivariant` (extraction transports — ✅
discharged for the adjacency instance) and `ForcedSeparates` (extraction faithful — the carried bridge). -/
theorem nodeResolved_compKey_refineByFrame_of_forcedSeparates
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hsep : ForcedSeparates extract adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel (genOfRef (refineByFrame extract))))) S adj χ :=
  nodeResolved_compKey_refineByFrame extract S adj χ hnd
    (fun _ _ _ => hemit_of_forcedSeparates extract adj χ hsep) hrigid

end RigidRefine
end ChainDescent
