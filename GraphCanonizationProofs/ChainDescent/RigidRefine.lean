import ChainDescent.RigidGen
import ChainDescent.ForcingModel
import ChainDescent.RigidSolveF2

/-!
# The concrete rigid refinement `ref` that `RigidGen.genOfRef` consumes

`RigidGen.genOfRef` reduced the rigid **linear** `①` to *"supply a **discrete**, **equivariant** `ref adj χ`"*
(it reads `rankPerm` of `ref`). This module builds that `ref`. It contains **two** readers and a general interface;
**the object of record is the structural reader `structRead` (§ step 6b)** — the coordinate-free reader
(`refineByFrame`, steps 1–5) is retained but provably **cannot discretize** the primary target.

⛔⛔⛔ **STOP — THAT SENTENCE IS SUPERSEDED BY THIS FILE'S OWN §9D/§9F (banner added 2026-08-10).**
Read this before acting on anything in "The two readers", "Build order" or "What remains" below; those
three sections predate steps 9D–9F and will route you into a retired generation. There are **three**
generations of reader here, not two:
* **(1) single-order `structRead` (§6b, §8, §9A–§9C) — DEAD.** Its `①` hypothesis `OrdEquivariant ord`
  is stated ∀ `adj χ` and is **unsatisfiable for `n ≥ 2`**: at the empty graph with the constant
  colouring every `σ` is a colour-aut, so the definition forces `ord adj χ = σ * ord adj χ`, i.e.
  `σ = 1`. §9F's milder wording (*"holds only on purely rigid inputs"*) is too generous — a `Force.Key`
  must be **one global function**, so there is no "restrict to the rigid regime" instantiation.
  ⟹ `readEquivariant_structRead`, `keyEquivariant_compKey_structRead`, `nodeResolved_compKey_structRead`,
  `keyEquivariant_compKey_skStruct*` are all correct lemmas with an undischargeable hypothesis.
* **(2) full-order aggregate `readAgg` (§9D) — CORRECT BUT EXPONENTIAL.** `①` unconditional, read is
  RICH (a full RREF column signature), but §9F proves any `FramesEquivariant` set of full orders has
  `|frames| ≥ 2^β` on a gauged input. `framesUniv` is the only instance.
* **(3) de-classed aggregate `readAggB` (§9F) — THE LIVE ONE.** `①` unconditional **and poly**;
  `keyEquivariant_compKey_readAggB_pin` closes with zero carried hypotheses once `refExtractEquivariant_adj`
  (step 4, proved) is plugged in. The open wall is `AggFaithfulB`, per-family.

⚠⚠ **AND A CAP ON THE ONLY CONCRETE `baseRead` — check this before enlarging any frame family.**
`baseReadPin = encOpt (forcedVal …)` and `encOpt_lt_three` bounds its codomain by `{0,1,2}`. `readAggB`
is `encode ∘ sort` of the **image** of that read over the frames, so it takes **at most 8 distinct
values on any input, for any frame family whatsoever**. By pigeonhole `AggFaithfulB` is *provably false*
at any node with ≥ 9 pairwise-non-automorphic branches — i.e. at every rigid multipede cell of interest.
⟹ §9F's own `▶ NEXT` (*"a RICH pinning family"*) cannot be satisfied by enlarging `frames`: **richness
has to come from the READ, not the frame set** (e.g. pair each per-frame read with an invariant of the
frame, so the aggregate encodes the map `frame ↦ value` instead of collapsing it).

⚠ Everything from `forcedVal` down is `noncomputable` (`rowspace` membership is a `Prop`), and so are
`readAgg`/`readAggB`/`genOfRef`. Wiring any of them into `RecordKey.recordKey` would cost the published
object its executability — that is a real cost the wind-down's "S4 = wire" step does not price in.

## The two readers (read this before editing)

**(A) `refineByFrame` — coordinate-free forcing (steps 1–5). `①` yes, `②` NO.** Per vertex reads one F₂ bit:
*"is `e_v` forced (`e_v ∈ rowspace H`), and if so its value"* = P2's `certificate_of_forced_notMem`. `①`
(`refEquivariant_refineByFrame`) is **unconditional** — `rowspace` transports under the linear equiv `transportVec σ`
(`span` commutes with a linear iso — no `Discrete χ`, no frame), which is why this was built (the χ-frame route (C)
has a `Discrete χ` gap: `framedRREF_transport` needs `rankInv` injective, false on a non-discrete cell, and there
is no equivariant within-cell tiebreak — the "no iso-invariant vertex pick" wall). ⚠⚠ **But one F₂ bit gives ≤2
classes per cell**, so on a **rigid** cell (zero symmetry ⟹ every coord forced, no gauge) a colour class with >2
vertices is NOT separated. The rigid **multipede** — the rigid solver's primary target — has exactly such cells, so
`refineByFrame` is NOT discrete there and `genOfRef` flags. Probe: `scratchpad/probe_rigid.py`. The reduction lemmas
(`hemit_of_forcedSeparates`, the firing capstone) are correct and kept; the mis-scoping was contained to *this
reader*. It still correctly identifies forced-vs-gauge (the mixed-cell split), just not discretization.

**(B) `structRead` — the DISCRETIZING structural reader (step 6b). The object of record.** Per vertex reads its
**RREF-column signature** (`RigidRREF.rrefCanon`, reused) over a **recovered iso-invariant column order** `ord` (a
`Perm` transporting as `ord' = σ · ord`). ★ The unlock: a *structural* order makes the framed RREF σ-invariant
**unconditionally** (`framedRREFBy_transport` — the general-order, χ-rank-free frame; χ-rank's gap was exactly
`rankInv` injectivity). So the whole rigid-linear seal rests on **three carried `Recover` facts**:
`OrdEquivariant ord` + `HsEquivariant Hs` (`①`, `readEquivariant_structRead`/`keyEquivariant_compKey_structRead`)
and `structRead` injective (`②` = "the ordered base pins every vertex" = full-rank on the rigid residue,
`readSeparates_of_injective`/`nodeResolved_compKey_structRead`). No `Discrete χ`, no coarseness. This is the reader
the multipede needs; `ord`/`Hs` are the carried Lean `Recover` objects (C#-tested; Lean side = P2/`ForcingModel`).

## Build order (sections in this file)
1. `transportVec σ` (ZMod 2 analog of `transportRow`) + **`rowspace_transport`**.
2. `forcedVal` (per-vertex forced bit over `rowspace`) + `forcedVal_transport`.
3. `refineByFrame` + **`refEquivariant_refineByFrame`** (`①`, unconditional) ⟹ `RigidGen` capstones.
4. concrete extraction (`extractOf`/`refExtractEquivariant_extractOf` generic + adjacency instance) — discharges the
   carried `RefExtractEquivariant` (`①`) concretely.
5. `②` reduction `hemit_of_forcedSeparates` (`Discrete refineByFrame ⟸ ForcedSeparates`) — ⚠ correct lemma, but
   `ForcedSeparates` is unsatisfiable for the single-bit reader on rigid cells (see (A)).
6. the **general reader interface** `refineBy read` + `ReadEquivariant`/`ReadSeparates` (both readers plug in).
6b. **`structRead`** = reader (B): `frameRowBy`/`framedRREFBy_transport` (the unlock) + `readEquivariant_structRead`
   + `readSeparates_of_injective` + capstones. **The discretizing reader.**

## What remains (for a fresh reader)
Discharge the three carried `Recover` facts: **`IsRigidF2 ⟹ structRead` injective** (self-contained Lean, via
`RigidRREF`'s rank toolkit — shrinks `②`) and/or the **concrete Lean `Recover`** (per family; = `ForcingModel.bridge`/L4).
Then P3-ring, P4. Authoritative detail: `docs/chain-descent-rigid-seal.md` STATUS + §8.2 + §10.
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
open ChainDescent.RigidRREF (rrefCanon)
open ChainDescent.RigidFrame (transportRow)

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

/-! ## Step 6 — the discretizing reader over a structural frame (match Recover)

The `②` FIX. The single-bit `forcedVal`/`frameRead` reader **cannot discretize** a rigid cell — one F₂ bit ⟹ ≤2
classes per cell, and a rigid multipede (the rigid solver's primary target, zero symmetry) has colour classes with
>2 vertices (probe `scratchpad/probe_rigid.py`). Discretization needs a **richer** per-vertex value over an
**iso-invariant column order**; since χ-rank needs `Discrete χ` and coordinate-free F₂ gives ≤2 classes, the order
must come from the **recovered canonical ordered base** (structural — the C# `Recover` path, IR §11 B1a, tested).

This section re-parameterizes the refinement around an arbitrary per-vertex canonical reader `read : … → Fin n → ℕ`
with two clean, mirrored obligations: `ReadEquivariant` (transports ⟹ `①`) and `ReadSeparates` (separates ⟹ `②`).
**The structural (Recover-ordered) reader is the carried instance satisfying both** — its `ReadSeparates` is the
honest restatement of the old `ForcedSeparates` ("the ordered base pins every vertex"). The single-bit reader is
retained as a coarse `ReadEquivariant` instance (`readEquivariant_encOpt_frameRead`) that does *not* separate. -/

/-- A per-vertex canonical reader is **equivariant** = a vertex-invariant (transports along σ). The structural
(Recover-ordered) reader has this from structural-order transport (carried); `encOpt ∘ frameRead` has it too, but
is too coarse to separate. -/
def ReadEquivariant (read : AdjMatrix n → Colouring n → Fin n → Nat) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    read (relabelAdj σ adj) (transportColouring σ χ) (σ v) = read adj χ v

/-- **Refine χ by a per-vertex canonical reader** — `Nat.pair` with χ (injective ⟹ a genuine refinement). The
general form the structural frame plugs into (replaces the single-bit `refineByFrame`). -/
def refineBy (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Colouring n :=
  fun v => Nat.pair (χ v) (read adj χ v)

/-- **★ `①` (general).** `refineBy read` is `RefEquivariant` from `ReadEquivariant read` alone (χ transports
pointwise, `read` is a vertex-invariant). Reader-agnostic — the structural reader inherits it. -/
theorem refEquivariant_refineBy (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (h : ReadEquivariant read) : RefEquivariant (refineBy read) := by
  intro σ adj χ
  funext u
  have hr := h σ adj χ (σ.symm u)
  rw [Equiv.apply_symm_apply] at hr
  simp only [refineBy, transportColouring, hr]

/-- The reader **separates** co-cellular vertices — the `②`/discretization obligation. Carried on the structural
(Recover-ordered) reader = "the ordered base pins every vertex"; NOT met by `encOpt ∘ frameRead` on rigid cells
(pigeonhole on the single F₂ bit). The honest restatement of `ForcedSeparates`. -/
def ReadSeparates (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u v : Fin n, χ u = χ v → read adj χ v = read adj χ u → u = v

/-- **★ `②` (general).** `refineBy read` is discrete from `ReadSeparates` (via `Nat.pair` injectivity). -/
theorem discrete_refineBy (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (h : ReadSeparates read adj χ) :
    Discrete (refineBy read adj χ) := by
  intro u v huv
  simp only [refineBy] at huv
  have hp : ((χ u, read adj χ u) : Nat × Nat) = (χ v, read adj χ v) := by
    have := congrArg Nat.unpair huv
    rwa [Nat.unpair_pair, Nat.unpair_pair] at this
  exact h u v (congrArg Prod.fst hp) (congrArg Prod.snd hp).symm

/-- **★★★ `①` capstone (general).** `compKey`'s `KeyEquivariant` for `refineBy read` from `ReadEquivariant`. -/
theorem keyEquivariant_compKey_refineBy (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (h : ReadEquivariant read) :
    KeyEquivariant (compKey (skOf (emitLabel (genOfRef (refineBy read))))) :=
  keyEquivariant_compKey_genOfRef (refineBy read) (refEquivariant_refineBy read h)

/-- **★★★ `②`/firing capstone (general).** `NodeResolved` for `refineBy read` from `ReadSeparates` + rigidity
(soundness free). With `keyEquivariant_compKey_refineBy`, the rigid-linear seal for the structural reader rests on
exactly `{ReadEquivariant, ReadSeparates}` — both discharged by the recovered canonical ordered base (carried). -/
theorem nodeResolved_compKey_refineBy_of_readSeparates
    (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hsep : ReadSeparates read adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel (genOfRef (refineBy read))))) S adj χ :=
  nodeResolved_compKey_genOfRef (refineBy read) S adj χ hnd
    (fun _ _ _ => discrete_refineBy read adj χ hsep) hrigid

/-- **The single-bit reader is a coarse `ReadEquivariant` instance** (from `frameRead_transport`) — so steps 1–5
supply a *transporting* reader — but it does NOT satisfy `ReadSeparates` on rigid cells (≤2 F₂ classes), which is
why the structural (Recover) reader is needed for `②`. -/
theorem readEquivariant_encOpt_frameRead
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) :
    ReadEquivariant (fun adj χ v => encOpt (frameRead extract adj χ v)) := by
  intro σ adj χ v
  simp only [frameRead_transport extract hext σ adj χ v]

/-! ## Step 6b — the concrete structural reader (RREF-column over a recovered order)

The `②`-delivering reader. Reads each vertex's **RREF-column signature** (`rrefCanon`, reused) over a **structural
column order** `ord` — a `Perm` that transports as `ord' = σ · ord` (iso-invariant, from `Recover`). ★ The unlock:
a structural order makes the framed RREF invariant **unconditionally** — no `Discrete χ` (the χ-rank frame's gap
came exactly from `rankInv` needing injectivity; a recovered order sidesteps it). So `ReadEquivariant` (`①`) holds
for the structural reader modulo two carried transport facts (`OrdEquivariant`, `HsEquivariant`); `ReadSeparates`
(`②`, discretization) stays carried = "`Recover`'s ordered base pins every vertex." -/

/-- Read a row in a **given** column order `ord` (position ↦ vertex) — the general-order frame, χ-rank-free. -/
def frameRowBy (ord : Equiv.Perm (Fin n)) (r : Fin n → Bool) : List Bool :=
  (List.finRange n).map (fun pos => r (ord pos))

/-- The system read in the order `ord`. -/
def frameSysBy (ord : Equiv.Perm (Fin n)) (Hs : List (Fin n → Bool)) : List (List Bool) :=
  Hs.map (frameRowBy ord)

/-- **★ The general-order framed row is σ-invariant** when the order transports as `ord' = σ · ord` — read `r ∘ σ⁻¹`
in the `σ·ord` order = read `r` in the `ord` order. **No `Discrete χ`** (the unlock vs. the χ-rank frame). -/
theorem frameRowBy_transport (σ ord : Equiv.Perm (Fin n)) (r : Fin n → Bool) :
    frameRowBy (σ * ord) (transportRow σ r) = frameRowBy ord r := by
  unfold frameRowBy
  refine List.map_congr_left (fun pos _ => ?_)
  show transportRow σ r ((σ * ord) pos) = r (ord pos)
  unfold transportRow
  rw [Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

theorem frameSysBy_transport (σ ord : Equiv.Perm (Fin n)) (Hs : List (Fin n → Bool)) :
    frameSysBy (σ * ord) (Hs.map (transportRow σ)) = frameSysBy ord Hs := by
  unfold frameSysBy
  rw [List.map_map]
  exact List.map_congr_left (fun r _ => frameRowBy_transport σ ord r)

/-- **★★ The structurally-framed `rrefCanon` transports** (`ord' = σ · ord`) — unconditionally. The χ-rank-free
analog of `RigidFrame.framedRREF_transport`. -/
theorem framedRREFBy_transport (σ ord : Equiv.Perm (Fin n)) (Hs : List (Fin n → Bool)) :
    rrefCanon n (frameSysBy (σ * ord) (Hs.map (transportRow σ))) = rrefCanon n (frameSysBy ord Hs) := by
  rw [frameSysBy_transport]

/-- The column of an RREF at position `pos` — the vertex's coordinate signature across the pivot rows. -/
def colSig (rref : List (Nat × List Bool)) (pos : Fin n) : List Bool :=
  rref.map (fun cr => cr.2.getD pos.val false)

/-- Encode a bit-list injectively (leading `1` sentinel makes it injective across lengths). -/
def bitsToNat : List Bool → Nat :=
  List.foldl (fun a b => 2 * a + (if b then 1 else 0)) 1

/-- **The structural reader.** Vertex `v`'s RREF-column signature over the recovered order `ord`, encoded to `ℕ`.
Parameterized by the carried `Recover` objects: the order `ord` and the system `Hs`. -/
def structRead (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  bitsToNat (colSig (rrefCanon n (frameSysBy (ord adj χ) (Hs adj χ))) ((ord adj χ).symm v))

/-- The recovered order transports as `ord' = σ · ord` (iso-invariant structural order — carried on `Recover`). -/
def OrdEquivariant (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    ord (relabelAdj σ adj) (transportColouring σ χ) = σ * ord adj χ

/-- The recovered system transports as `Hs' = Hs.map (transportRow σ)` (carried on `Recover`). -/
def HsEquivariant (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    Hs (relabelAdj σ adj) (transportColouring σ χ) = (Hs adj χ).map (transportRow σ)

/-- **★★★ Step 6b `①` payoff — the structural reader is `ReadEquivariant`.** From the carried order/system
transport (`OrdEquivariant` + `HsEquivariant`) and the χ-rank-free `framedRREFBy_transport`. **No `Discrete χ`.**
Feeds `refEquivariant_refineBy` / `keyEquivariant_compKey_refineBy` — the rigid-linear `①` for the structural
reader, modulo only the two carried `Recover` transport facts. -/
theorem readEquivariant_structRead
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (ho : OrdEquivariant ord) (hH : HsEquivariant Hs) :
    ReadEquivariant (structRead ord Hs) := by
  intro σ adj χ v
  simp only [structRead]
  rw [ho σ adj χ, hH σ adj χ, framedRREFBy_transport σ (ord adj χ) (Hs adj χ)]
  have hpos : (σ * ord adj χ).symm (σ v) = (ord adj χ).symm v := by
    have h1 : (σ * ord adj χ) ((ord adj χ).symm v) = σ v := by
      rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    rw [← h1, Equiv.symm_apply_apply]
  rw [hpos]

/-- **★★★ Step 6b `①` capstone.** `compKey`'s `KeyEquivariant` for the concrete structural reader — the rigid-linear
`①` closes on the two carried `Recover` transport facts alone. -/
theorem keyEquivariant_compKey_structRead
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (ho : OrdEquivariant ord) (hH : HsEquivariant Hs) :
    KeyEquivariant (compKey (skOf (emitLabel (genOfRef (refineBy (structRead ord Hs)))))) :=
  keyEquivariant_compKey_refineBy (structRead ord Hs) (readEquivariant_structRead ord Hs ho hH)

/-- **The `②` obligation for the structural reader**, crisply: the reader is injective on the residue — every
vertex gets a distinct column signature. This is exactly *"`Recover`'s ordered base pins every vertex"* = the RREF
is full column rank on the rigid residue (⟸ rigidity `IsRigidF2` + faithful `Recover`). Carried; its non-vacuity
is the rigid solver itself (a rigid multipede has trivial kernel ⟹ full-rank recovered system ⟹ distinct columns
— the probe `scratchpad/probe_rigid.py` shows the RREF-column reader discretizes exactly where the single bit
cannot). -/
theorem readSeparates_of_injective
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n)
    (h : Function.Injective (structRead ord Hs adj χ)) :
    ReadSeparates (structRead ord Hs) adj χ :=
  fun _ _ _ huv => (h huv).symm

/-- **★★★ Step 6b `②`/firing capstone.** `NodeResolved` for the concrete structural reader from its injectivity
(the carried `Recover` discretization) + rigidity. Combined with `keyEquivariant_compKey_structRead` (`①`), the
whole rigid-**linear** seal for the structural reader rests on exactly the three carried `Recover` facts:
`OrdEquivariant` + `HsEquivariant` (the order/system transport, `①`) and `structRead` injective (discretization,
`②`) — no `Discrete χ`, no coordinate-free coarseness. This is the discretizing reader the multipede needs. -/
theorem nodeResolved_compKey_structRead
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hinj : Function.Injective (structRead ord Hs adj χ))
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skOf (emitLabel (genOfRef (refineBy (structRead ord Hs)))))) S adj χ :=
  nodeResolved_compKey_refineBy_of_readSeparates (structRead ord Hs) S adj χ hnd
    (readSeparates_of_injective ord Hs adj χ hinj) hrigid

/-! ## Step 7 — per-pair (mixed-native) firing via `skRead` / `SolverSeparates` (de-class the `②` carry)

Steps 6/6b close firing through `genOfRef`'s **all-or-nothing `Discrete` gate** (`skOf ∘ emitLabel ∘ genOfRef`), so
`nodeResolved_compKey_structRead` fires only when the reader *fully* discretizes the node = the **purely-rigid** case
(pure multipede). On a **mixed** cell (some forced coords + a gauge kernel) `genOfRef` flags ⟹ `encodeOpt` emits the
`[]` sentinel ⟹ everything ties, nothing separates — the solver's partial progress is discarded and the mixed residue
is not handled.

This step routes firing through the **per-pair, family-agnostic** seam `RigidSeal.SolverSeparates` /
`nodeResolved_compKey_of_rigid` instead. It is **mixed-native**: the equivariance ceiling ties gauge/automorphic pairs
(consume merges them) and only the *non-automorphic* pairs must separate — there is **no** global-discreteness
requirement. The carried predicate `ReadSeparatesRigid` is the **kernel characterization** `ker(recovered H) =
{automorphism-induced differences}` restricted to the exposed pairs (non-aut ⟺ `e_u−e_w ∉ ker(H)` ⟺ distinct
signature), stated ONCE over the generic extraction — not per family. Schurian (`ker H` = everything) and CFI/multipede
(`ker H` = cycle-space gauge) are the extremes of this one predicate; mixed is the interpolation. Global injectivity
(the purely-rigid `IsRigidF2 ⟹ structRead` injective) is the `ker = 0` special case
(`readSeparatesRigid_of_injective`). -/

/-- **The force key read directly off a per-vertex reader** — the reader's value wrapped as a `Force.Key`, NOT routed
through `genOfRef`/`emitLabel` (whose `Discrete` gate is all-or-nothing). This is what lets the rigid solver fire
per-pair on a mixed cell. `skCost` is the placeholder `②` cost (no `①` obligation). -/
def skRead (read : AdjMatrix n → Colouring n → Fin n → Nat) : Force.Key n :=
  fun adj χ v => ([read adj χ v], RigidSolver.skCost n)

@[simp] theorem keyV_skRead (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    Force.keyV (skRead read) adj χ v = [read adj χ v] := rfl

/-- **★ `①` — the reader key is equivariant** from `ReadEquivariant read` alone (the value is `[read …]`, a
vertex-invariant). Feeds `keyEquivariant_compKey`. -/
theorem keyEquivariant_skRead (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (h : ReadEquivariant read) : KeyEquivariant (skRead read) := by
  intro σ adj χ v
  simp only [keyV_skRead]
  rw [h σ adj χ v]

/-- **The per-pair carried predicate = the kernel characterization on the exposed pairs.** A non-automorphic,
non-discretizing, co-cellular pair `(u,w)` gets **distinct** reads — i.e. `e_u − e_w ∉ ker(recovered H)`. This is the
mixed-native `②`: it says nothing about gauge/automorphic pairs (they tie, correctly), only that the *rigid decisions*
separate. Stated once over the generic reader — Schurian/CFI/mixed are all instances by the value of `ker(recovered
H)`. -/
def ReadSeparatesRigid (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) →
    ¬ Discrete (lookData adj χ u).col → ¬ Discrete (lookData adj χ w).col →
    read adj χ u ≠ read adj χ w

/-- **★★ Firing reduction — `SolverSeparates` from `ReadSeparatesRigid`, with NO `hemit`/no-flag hypothesis.** The
mirror of `RigidSolver.solverSeparates_skOf`, but the direct reader key never flags, so the discretization
completeness that `skOf` needed (`hemit`) drops out entirely — the reader separates the exposed rigid pairs *per pair*.
This is the whole point of step 7: mixed cells fire without full discreteness. -/
theorem solverSeparates_skRead (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (hsep : ReadSeparatesRigid read adj χ) :
    SolverSeparates (compKey (skRead read)) adj χ := by
  intro u hu w hw hrig hdu hdw hkey
  rw [keyV_compKey_not_disc (skRead read) adj χ u hdu,
      keyV_compKey_not_disc (skRead read) adj χ w hdw, keyV_skRead, keyV_skRead] at hkey
  obtain ⟨_, h2⟩ := List.cons.inj hkey
  obtain ⟨hval, _⟩ := List.cons.inj h2
  exact hsep u hu w hw hrig hdu hdw hval

/-- **★ `①` capstone (per-pair).** `compKey (skRead read)`'s `KeyEquivariant` from `ReadEquivariant read`. -/
theorem keyEquivariant_compKey_skRead (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (h : ReadEquivariant read) : KeyEquivariant (compKey (skRead read)) :=
  keyEquivariant_compKey (skRead read) (keyEquivariant_skRead read h)

/-- **★★★ `②`/firing capstone (per-pair, MIXED-NATIVE).** `NodeResolved` for `compKey (skRead read)` from
`ReadSeparatesRigid` (the exposed rigid pairs separate) + rigidity — **no global discreteness**. The gauge pairs stay
tied and are consume's job (the untouched `cellIsOrbit` disjunct); only the rigid decisions must separate. This is the
firing the mixed residue actually needs. -/
theorem nodeResolved_compKey_skRead (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hsep : ReadSeparatesRigid read adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skRead read)) S adj χ :=
  nodeResolved_compKey_of_rigid (skRead read) S adj χ hnd
    (solverSeparates_skRead read adj χ hsep) hrigid

/-- **Global injectivity ⟹ `ReadSeparatesRigid`** — the `ker = 0` (purely-rigid) special case: if the reader is
injective on the whole vertex set (`IsRigidF2 ⟹ structRead` injective, the pure multipede) then in particular it
separates every non-automorphic pair, since a non-automorphic pair is distinct (the identity `IsColAut.one` would
otherwise map `u` to `w`). So the purely-rigid result feeds the mixed-native firing as its extreme. -/
theorem readSeparatesRigid_of_injective (read : AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (h : Function.Injective (read adj χ)) :
    ReadSeparatesRigid read adj χ := by
  intro u _ w _ hrig _ _ hval
  exact hrig 1 (Consume.IsColAut.one adj χ) (by simpa using h hval)

/-! ### Step 7 — the `structRead` instantiation (`skStruct`) -/

/-- **`skStruct ord Hs`** — the concrete mixed-native force key: the structural RREF-column reader wrapped directly as
a `Force.Key`, bypassing `genOfRef`. Its `①` rides the carried order/system transport; its firing rides the per-pair
kernel characterization `ReadSeparatesRigid (structRead ord Hs)`. -/
def skStruct (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool)) : Force.Key n :=
  skRead (structRead ord Hs)

/-- **★★★ Step 7 `①` capstone (structural).** `compKey (skStruct ord Hs)`'s `KeyEquivariant` from the two carried
transport facts (`OrdEquivariant` + `HsEquivariant`) — no global discreteness, no `genOfRef`. -/
theorem keyEquivariant_compKey_skStruct
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (ho : OrdEquivariant ord) (hH : HsEquivariant Hs) :
    KeyEquivariant (compKey (skStruct ord Hs)) :=
  keyEquivariant_compKey_skRead (structRead ord Hs) (readEquivariant_structRead ord Hs ho hH)

/-- **★★★ Step 7 `②`/firing capstone (structural, MIXED-NATIVE).** `NodeResolved` for `compKey (skStruct ord Hs)` from
the per-pair kernel characterization `ReadSeparatesRigid (structRead ord Hs)` + rigidity — **no global discreteness**.
This is the discretizing reader firing on a MIXED cell (forced pairs separate, gauge pairs tie for consume), which
step 6b's `nodeResolved_compKey_structRead` could not do. The whole rigid seal for the mixed residue now rests on:
`OrdEquivariant` + `HsEquivariant` (`①`) + `ReadSeparatesRigid (structRead ord Hs)` (`②` = the kernel characterization,
one generic predicate). -/
theorem nodeResolved_compKey_skStruct
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hsep : ReadSeparatesRigid (structRead ord Hs) adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skStruct ord Hs)) S adj χ :=
  nodeResolved_compKey_skRead (structRead ord Hs) S adj χ hnd hsep hrigid

/-- **The purely-rigid (`ker = 0`) firing, recovered as a corollary.** Global `structRead` injectivity (the pure
multipede, `IsRigidF2 ⟹ structRead` injective) ⟹ the mixed-native firing capstone — so step 6b's fully-rigid case is
subsumed by step 7's per-pair route (via `readSeparatesRigid_of_injective`), and the two are one theorem. -/
theorem nodeResolved_compKey_skStruct_of_injective
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n))
    (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hinj : Function.Injective (structRead ord Hs adj χ))
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skStruct ord Hs)) S adj χ :=
  nodeResolved_compKey_skStruct ord Hs S adj χ hnd
    (readSeparatesRigid_of_injective (structRead ord Hs) adj χ hinj) hrigid

/-! ## Step 8 — the concrete `Recover`, part 1: the extracted system `Hs` (discharge `HsEquivariant`)

`structRead` carries two `Recover` objects: the column order `ord` and the extracted F₂ system `Hs`. This step
discharges the `Hs` half **concretely** — the adjacency Bool-row system `hsAdj` — so `HsEquivariant` drops off the
carried list, leaving only the order `ord` (the crux, piece 2) and the kernel predicate (piece 3).

**★ Interface correction (surfaced by building):** a real index-based extraction satisfies `HsEquivariant` only **up
to row permutation** — under `σ` the rows are both column-transported (`transportRow σ`) *and* re-indexed. That is
harmless: `rrefCanon` is a canonical function of the row **space** (`rrefCanon_eq_of_span_eq`), so a `List.Perm` of the
rows leaves the framed RREF — hence `structRead` — unchanged. This step proves that span-level transport for `hsAdj`,
which is strictly the honest form of `HsEquivariant` (`readEquivariant_structRead` used the literal list equality,
which no concrete index-based extraction meets on the nose). -/

open ChainDescent.Kernel (Spans)

/-- **`rrefCanon` is `List.Perm`-invariant on its rows** — a permutation of the generating list preserves the row
space (`Spans` both ways via `Spans.mono`), so the canonical RREF is unchanged. The "row order doesn't matter" fact
any concrete (index-based) extraction needs. -/
theorem rrefCanon_congr_perm {m : Nat} {L₁ L₂ : List (List Bool)}
    (h₁ : ∀ r ∈ L₁, r.length = m) (h₂ : ∀ r ∈ L₂, r.length = m) (hp : L₁.Perm L₂) :
    rrefCanon m L₁ = rrefCanon m L₂ :=
  RigidRREF.rrefCanon_eq_of_span_eq h₁ h₂ (fun _ =>
    ⟨Spans.mono (fun _ hb => hp.mem_iff.mp hb), Spans.mono (fun _ hb => hp.mem_iff.mpr hb)⟩)

/-- Mapping an `Equiv.Perm` over `List.finRange n` permutes it (same nodup elements). -/
theorem finRange_map_perm (e : Equiv.Perm (Fin n)) :
    ((List.finRange n).map (⇑e)).Perm (List.finRange n) := by
  refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).map e.injective)
    (List.nodup_finRange n)).mpr (fun x => ?_)
  simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
  exact ⟨e.symm x, by simp⟩

/-- The concrete adjacency Bool-row of vertex `i`: `v ↦ [adj i v ≠ 0]`. -/
def boolRow (adj : AdjMatrix n) (i : Fin n) : Fin n → Bool := fun v => decide (adj.adj i v ≠ 0)

/-- **The concrete extracted system** — the graph's adjacency rows as an F₂ system (χ-independent; the simplest
non-vacuous faithful-of-the-adjacency extraction, the Bool/`List` analog of step 4's `rowAdj`). This is the `Hs`
the structural reader consumes; the per-family faithful extraction (CFI rails) slots in the same way. -/
def hsAdj (adj : AdjMatrix n) (_χ : Colouring n) : List (Fin n → Bool) :=
  (List.finRange n).map (boolRow adj)

/-- The relabelled adjacency row is the transported row at the pre-image index: a pure reindex + column transport. -/
theorem boolRow_relabel (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (i : Fin n) :
    boolRow (relabelAdj σ adj) i = transportRow σ (boolRow adj (σ.symm i)) := by
  funext v
  show decide ((relabelAdj σ adj).adj i v ≠ 0) = decide (adj.adj (σ.symm i) (σ.symm v) ≠ 0)
  rw [relabelAdj_adj]

/-- **★ `hsAdj` transports up to `List.Perm`.** The σ-relabelled system is a row-permutation of the
column-transported system — the honest (row-order-agnostic) form of `HsEquivariant`. -/
theorem hsAdj_transport_perm (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    (hsAdj (relabelAdj σ adj) (transportColouring σ χ)).Perm ((hsAdj adj χ).map (transportRow σ)) := by
  have key : hsAdj (relabelAdj σ adj) (transportColouring σ χ)
      = ((List.finRange n).map (⇑σ.symm)).map (transportRow σ ∘ boolRow adj) := by
    simp only [hsAdj, List.map_map]
    exact List.map_congr_left (fun i _ => boolRow_relabel σ adj i)
  have key2 : (hsAdj adj χ).map (transportRow σ)
      = (List.finRange n).map (transportRow σ ∘ boolRow adj) := by
    simp only [hsAdj, List.map_map]
  rw [key, key2]
  exact (finRange_map_perm σ.symm).map (transportRow σ ∘ boolRow adj)

/-- Every row of a `frameSysBy` output has length `n` (it maps over `finRange n`). -/
theorem length_mem_frameSysBy (o : Equiv.Perm (Fin n)) (L : List (Fin n → Bool)) :
    ∀ r ∈ frameSysBy o L, r.length = n := by
  intro r hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  simp [frameRowBy]

/-- **★★ The structurally-framed RREF of the concrete system transports** (order `o ↦ σ · o`) — the `hsAdj`
instance of `framedRREFBy_transport`, with the row-permutation absorbed by `rrefCanon_congr_perm`. This is exactly
what `readEquivariant_structRead` consumes at the `Hs` step, now discharged for the concrete extraction. -/
theorem framedRREF_hsAdj_transport (σ o : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    rrefCanon n (frameSysBy (σ * o) (hsAdj (relabelAdj σ adj) (transportColouring σ χ)))
      = rrefCanon n (frameSysBy o (hsAdj adj χ)) := by
  have hp : (frameSysBy (σ * o) (hsAdj (relabelAdj σ adj) (transportColouring σ χ))).Perm
      (frameSysBy (σ * o) ((hsAdj adj χ).map (transportRow σ))) :=
    (hsAdj_transport_perm σ adj χ).map (frameRowBy (σ * o))
  rw [rrefCanon_congr_perm (length_mem_frameSysBy _ _) (length_mem_frameSysBy _ _) hp]
  exact framedRREFBy_transport σ o (hsAdj adj χ)

/-- **★★★ Step 8 payoff — `ReadEquivariant (structRead ord hsAdj)` from `OrdEquivariant ord` ALONE.** The
`HsEquivariant` carried fact is discharged for the concrete adjacency extraction (via the span-level
`framedRREF_hsAdj_transport`). So a concrete `Recover` for the structural reader now carries only the order `ord`
(`OrdEquivariant`) and the kernel predicate — the `Hs` extraction is no longer a hypothesis. -/
theorem readEquivariant_structRead_hsAdj
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n)) (ho : OrdEquivariant ord) :
    ReadEquivariant (structRead ord hsAdj) := by
  intro σ adj χ v
  simp only [structRead]
  rw [ho σ adj χ, framedRREF_hsAdj_transport σ (ord adj χ) adj χ]
  have hpos : (σ * ord adj χ).symm (σ v) = (ord adj χ).symm v := by
    have h1 : (σ * ord adj χ) ((ord adj χ).symm v) = σ v := by
      rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    rw [← h1, Equiv.symm_apply_apply]
  rw [hpos]

/-- **★★★ Step 8 `①` capstone — the mixed-native force key's equivariance, on the concrete extraction, modulo ONLY
`OrdEquivariant`.** `HsEquivariant` is gone (discharged); the rigid-linear `①` for `compKey (skStruct ord hsAdj)`
now rests on the single carried order fact. -/
theorem keyEquivariant_compKey_skStruct_hsAdj
    (ord : AdjMatrix n → Colouring n → Equiv.Perm (Fin n)) (ho : OrdEquivariant ord) :
    KeyEquivariant (compKey (skStruct ord hsAdj)) :=
  keyEquivariant_compKey_skRead (structRead ord hsAdj) (readEquivariant_structRead_hsAdj ord ho)

/-! ## Step 9 — piece 2 of the concrete `Recover`: the iso-invariant column order via MIN over an equivariant frame set

The step-8 crux: an equivariant order **permutation** (`OrdEquivariant`) is satisfiable ONLY on rigid inputs — a
colour-automorphism `σ` forces `ord adj χ = σ · ord adj χ ⟹ σ = 1`. The resolution is the C# `Recover`/B2 mechanism:
**not** a directly-constructed equivariant Perm, but a **canonical MIN over an equivariant candidate-frame set** (fire
at the iso-invariant root partition, lex-min the labelling; ties = residual symmetry). This section builds that engine
abstractly:

* `frames adj χ : Finset (Perm)` — the candidate column orders (concretely the poly base/pivot frames of the code,
  §9B), with **`FramesEquivariant`** (σ maps frames to frames).
* `key adj χ o : ℕ` — an iso-invariant frame key (concretely any function of `rrefCanon (frameSysBy o (hsAdj …))`),
  with **`KeyTransport`** — DISCHARGED for `hsAdj` from `framedRREF_hsAdj_transport` (`keyTransport_hsAdj`, any `f`).
* the order = the min-key frame. **`isMinFrame_transport`**: the min frame transports as `o ↦ σ·o`. When the min is
  **unique** (the rigid regime — ties are exactly residual symmetry), this yields **`OrdEquivariant`** for the choice
  function (`ordEquivariant_minOrd`), feeding step 8's `readEquivariant_structRead_hsAdj` / `keyEquivariant_compKey_*`
  end-to-end. So the ① crux is resolved modulo {`FramesEquivariant`, existence, uniqueness}; concrete `frames` is §9B,
  and uniqueness = the rigid regime (§9C). The general (tie) case — reading at any min-achiever, tied frames agreeing —
  is §9C, deferred with the interleaving. -/

/-- The candidate frame set transports: σ maps each candidate column order `o` to `σ · o`. Iso-invariance of the
CANDIDATE SET (not of any single frame) — this is the object that exists on all inputs, unlike an equivariant Perm. -/
def FramesEquivariant (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n))) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    frames (relabelAdj σ adj) (transportColouring σ χ) = (frames adj χ).image (fun o => σ * o)

/-- The frame key is an iso-invariant: the key of `σ · o` on the σ-relabelled node equals the key of `o` on the
original. For `hsAdj` this is FREE from `framedRREF_hsAdj_transport` (`keyTransport_hsAdj`). -/
def KeyTransport (key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (o : Equiv.Perm (Fin n)),
    key (relabelAdj σ adj) (transportColouring σ χ) (σ * o) = key adj χ o

/-- `o` is a (key-)minimal frame at `(adj, χ)`: a candidate whose key is `≤` every candidate's. -/
def IsMinFrame (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (o : Equiv.Perm (Fin n)) : Prop :=
  o ∈ frames adj χ ∧ ∀ o' ∈ frames adj χ, key adj χ o ≤ key adj χ o'

/-- **★ The min frame transports** as `o ↦ σ · o`: the candidate set transports (`FramesEquivariant`) and the key
transports (`KeyTransport`), so a minimizer maps to a minimizer. The heart of the engine — this is why the min-over-set
is iso-invariant where a single equivariant Perm cannot exist. -/
theorem isMinFrame_transport
    {frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n))}
    {key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat}
    (hf : FramesEquivariant frames) (hk : KeyTransport key)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (o : Equiv.Perm (Fin n))
    (h : IsMinFrame frames key adj χ o) :
    IsMinFrame frames key (relabelAdj σ adj) (transportColouring σ χ) (σ * o) := by
  obtain ⟨hmem, hmin⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hf σ adj χ]; exact Finset.mem_image.mpr ⟨o, hmem, rfl⟩
  · intro o'' ho''
    rw [hf σ adj χ] at ho''
    obtain ⟨o', ho', rfl⟩ := Finset.mem_image.mp ho''
    rw [hk σ adj χ o, hk σ adj χ o']
    exact hmin o' ho'

/-- **The selected canonical order** — a chosen min frame (needs existence; uniqueness makes it equivariant). -/
noncomputable def minOrd (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat)
    (hex : ∀ adj χ, ∃ o, IsMinFrame frames key adj χ o) :
    AdjMatrix n → Colouring n → Equiv.Perm (Fin n) :=
  fun adj χ => Classical.choose (hex adj χ)

theorem isMinFrame_minOrd {frames key} (hex : ∀ adj χ, ∃ o, IsMinFrame frames key adj χ o)
    (adj : AdjMatrix n) (χ : Colouring n) :
    IsMinFrame frames key adj χ (minOrd frames key hex adj χ) :=
  Classical.choose_spec (hex adj χ)

/-- **★★ `OrdEquivariant` for the min-frame order, on a UNIQUE min.** Both `minOrd (relabel σ)(transport χ)` and
`σ · minOrd adj χ` are min frames at the relabelled node (`isMinFrame_transport`); uniqueness forces them equal. This
discharges the step-8 order obligation `OrdEquivariant` from {`FramesEquivariant`, existence, uniqueness} — the
resolution of the crux (uniqueness ⟺ trivial residual symmetry ⟺ the rigid regime). -/
theorem ordEquivariant_minOrd
    {frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n))}
    {key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat}
    (hf : FramesEquivariant frames) (hk : KeyTransport key)
    (hex : ∀ adj χ, ∃ o, IsMinFrame frames key adj χ o)
    (huniq : ∀ adj χ o o', IsMinFrame frames key adj χ o → IsMinFrame frames key adj χ o' → o = o') :
    OrdEquivariant (minOrd frames key hex) := by
  intro σ adj χ
  exact huniq (relabelAdj σ adj) (transportColouring σ χ) _ _
    (isMinFrame_minOrd hex (relabelAdj σ adj) (transportColouring σ χ))
    (isMinFrame_transport hf hk σ adj χ (minOrd frames key hex adj χ) (isMinFrame_minOrd hex adj χ))

/-- The concrete `hsAdj` frame key: any encoding `f` of the framed canonical RREF. -/
noncomputable def frameKeyHsAdj (f : List (Nat × List Bool) → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (o : Equiv.Perm (Fin n)) : Nat :=
  f (rrefCanon n (frameSysBy o (hsAdj adj χ)))

/-- **`KeyTransport` is FREE for the concrete `hsAdj` frame key** — for ANY encoding `f`, the key transports because
the framed RREF itself transports (`framedRREF_hsAdj_transport`). So the engine's key obligation costs nothing on the
concrete extraction. -/
theorem keyTransport_hsAdj (f : List (Nat × List Bool) → Nat) :
    KeyTransport (frameKeyHsAdj (n := n) f) := by
  intro σ adj χ o
  simp only [frameKeyHsAdj, framedRREF_hsAdj_transport σ o adj χ]

/-- **★★★ Step 9A capstone — the mixed-native force key's `①` on the concrete extraction, via the MIN-frame order,
modulo {`FramesEquivariant`, existence, uniqueness} ONLY.** The step-8 order obligation `OrdEquivariant` is discharged
by the min-over-frames engine (`ordEquivariant_minOrd` + free `keyTransport_hsAdj`), so `KeyEquivariant` of the whole
`compKey (skStruct (minOrd …) hsAdj)` holds. What remains for piece 2 is the concrete frame set (§9B — `FramesEquivariant`
+ existence) and uniqueness (§9C — the rigid regime). -/
theorem keyEquivariant_compKey_skStruct_minFrame
    (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (f : List (Nat × List Bool) → Nat)
    (hf : FramesEquivariant frames)
    (hex : ∀ adj χ, ∃ o, IsMinFrame frames (frameKeyHsAdj f) adj χ o)
    (huniq : ∀ adj χ o o',
      IsMinFrame frames (frameKeyHsAdj f) adj χ o →
      IsMinFrame frames (frameKeyHsAdj f) adj χ o' → o = o') :
    KeyEquivariant (compKey (skStruct (minOrd frames (frameKeyHsAdj f) hex) hsAdj)) :=
  keyEquivariant_compKey_skStruct_hsAdj _
    (ordEquivariant_minOrd hf (keyTransport_hsAdj f) hex huniq)

/-! ## Step 9B — a concrete frame set: the exhaustive `univ` instance (correct; poly refinement deferred)

9A left the order's `①` modulo {`FramesEquivariant`, existence, uniqueness}. This step discharges the first two with
the simplest concrete frame set — **all** column orders, `frames adj χ = univ`. It is manifestly equivariant (left
multiplication by `σ` is a bijection of `Perm`, so `univ.image (σ·) = univ`) and non-empty (so a key-minimizer exists),
closing the order's `①` end-to-end **modulo uniqueness alone** (§9C = the rigid regime).

**⚠ This is the CORRECT-BUT-EXPONENTIAL instance** (the analog of the exhaustive canonizer the whole project refines to
poly): `univ` is `n!`. The **poly** frame set — built **structurally/greedily** (the C# "no base enumeration" single
greedy canonical-base path, poly by bounded ring rank per B1d), NOT by naive enumeration (which would re-import the `s!`
blow-up the fold-robustness note guards against) — is a `②`-cost refinement that drops into the SAME 9A engine
(`FramesEquivariant` + existence for the poly set), leaving `①`/uniqueness untouched. Deferred. -/

/-- The exhaustive frame set — every column order. -/
def framesUniv : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)) :=
  fun _ _ => Finset.univ

/-- **★ The exhaustive frame set is equivariant.** `univ.image (σ·) = univ` since left-multiplication by `σ` is a
bijection of `Perm`. The simplest concrete `FramesEquivariant` witness. -/
theorem framesEquivariant_univ : FramesEquivariant (framesUniv (n := n)) := by
  intro σ adj χ
  show (Finset.univ : Finset (Equiv.Perm (Fin n))) = Finset.univ.image (fun o => σ * o)
  refine (Finset.eq_univ_of_forall (fun p => ?_)).symm
  exact Finset.mem_image.mpr ⟨σ⁻¹ * p, Finset.mem_univ _, mul_inv_cancel_left σ p⟩

/-- **A key-minimal frame exists over `univ`** — `univ` is non-empty (`1 ∈ univ`) and the key lands in `ℕ`
(well-ordered), so `Finset.exists_min_image` gives a minimizer. Discharges the engine's `existence` obligation. -/
theorem exists_isMinFrame_univ (key : AdjMatrix n → Colouring n → Equiv.Perm (Fin n) → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) :
    ∃ o, IsMinFrame framesUniv key adj χ o := by
  obtain ⟨o, _, ho⟩ := Finset.exists_min_image Finset.univ (key adj χ) ⟨1, Finset.mem_univ 1⟩
  exact ⟨o, Finset.mem_univ o, fun o' _ => ho o' (Finset.mem_univ o')⟩

/-- **★★★ Step 9B capstone — the mixed-native force key's `①` on the concrete `hsAdj` extraction with the CONCRETE
(exhaustive) frame set, modulo UNIQUENESS ALONE.** `FramesEquivariant` and existence are discharged (`univ`); the only
remaining order obligation is that the min frame is unique — which holds exactly on the rigid regime (§9C), where ties
(orders giving the same framed RREF) are code-automorphisms = graph-automorphisms = trivial. So the entire order piece
(piece 2) of the concrete `Recover` reduces to **one** rigid-regime uniqueness fact. -/
theorem keyEquivariant_compKey_skStruct_univ (f : List (Nat × List Bool) → Nat)
    (huniq : ∀ (adj : AdjMatrix n) (χ : Colouring n) (o o' : Equiv.Perm (Fin n)),
      IsMinFrame framesUniv (frameKeyHsAdj f) adj χ o →
      IsMinFrame framesUniv (frameKeyHsAdj f) adj χ o' → o = o') :
    KeyEquivariant (compKey (skStruct
      (minOrd (framesUniv (n := n)) (frameKeyHsAdj f) (exists_isMinFrame_univ (frameKeyHsAdj f))) hsAdj)) :=
  keyEquivariant_compKey_skStruct_minFrame (framesUniv (n := n)) f
    framesEquivariant_univ (exists_isMinFrame_univ (frameKeyHsAdj f)) huniq

/-! ## Step 9C — rigid ⟹ unique min: reduce `huniq` to the single faithfulness predicate `RigidFrameUnique`

9B left piece 2's `①` modulo `huniq` (the min frame is unique). Two `IsMinFrame`s force **equal keys** ⟹ (injective
encoding) **equal framed RREFs**. Since `rrefCanon` is a function of the row *space*, equal framed RREF ⟺ `o'·o⁻¹` is a
coordinate-permutation automorphism of the recovered code. So uniqueness ⟺ *the code has no nontrivial coordinate
automorphism* = **faithfulness** (code-auto = graph-auto, the kernel characterization / `ForcingModel.bridge`, piece 3)
+ **graph-rigidity**. Piece 2's uniqueness and piece 3's kernel predicate are thus the **same** faithfulness fact.

This step (9C-1) makes that reduction concrete: `huniq` ⟸ **`RigidFrameUnique`** (distinct orders ⟹ distinct framed
RREF), with a **concrete injective encoding** (`Encodable.encode`) so no `f`-injectivity is carried. The remaining core
9C-2 — `IsRigidF2` + the faithfulness bridge ⟹ `RigidFrameUnique` (the equal-RREF ⟹ code-auto ⟹ graph-auto ⟹ id
chain), and the same faithfulness ⟹ `structRead` injective (the ② kernel predicate, via step 7's
`readSeparatesRigid_of_injective`) — is the hard, carried-per-family linear-algebra content. -/

/-- **The rigid-regime frame-uniqueness predicate.** Distinct column orders give distinct canonical framed RREFs. On a
rigid input this holds because two orders with the same framed RREF differ by a coordinate-permutation automorphism of
the recovered code = (faithfulness) a graph colour-automorphism = (rigidity) the identity. Carried = piece 3 / the
kernel characterization; 9C-2 proves it from `IsRigidF2` + the faithfulness bridge. -/
def RigidFrameUnique (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ o o' : Equiv.Perm (Fin n),
    rrefCanon n (frameSysBy o (Hs adj χ)) = rrefCanon n (frameSysBy o' (Hs adj χ)) → o = o'

/-- **★ `huniq` from `RigidFrameUnique`** (pointwise): two key-minimal frames tie on the key ⟹ (injective `f`) tie on
the framed RREF ⟹ (`RigidFrameUnique`) are equal. The rigid-regime uniqueness the min-frame engine needs, reduced to
the single faithfulness predicate. -/
theorem eq_of_isMinFrame_hsAdj {f : List (Nat × List Bool) → Nat} (hf : Function.Injective f)
    (adj : AdjMatrix n) (χ : Colouring n) (hru : RigidFrameUnique hsAdj adj χ)
    (o o' : Equiv.Perm (Fin n))
    (ho : IsMinFrame framesUniv (frameKeyHsAdj f) adj χ o)
    (ho' : IsMinFrame framesUniv (frameKeyHsAdj f) adj χ o') : o = o' := by
  have hkey : frameKeyHsAdj f adj χ o = frameKeyHsAdj f adj χ o' :=
    le_antisymm (ho.2 o' (Finset.mem_univ o')) (ho'.2 o (Finset.mem_univ o))
  simp only [frameKeyHsAdj] at hkey
  exact hru o o' (hf hkey)

/-- **★★★ Step 9C-1 capstone — the pure-rigid `①`, closed on `RigidFrameUnique` ALONE.** With the concrete injective
encoding `Encodable.encode`, `keyEquivariant_compKey_skStruct_univ`'s `huniq` is discharged from the per-node
`RigidFrameUnique` (= the rigid-regime faithfulness). So the whole rigid-linear `①` for the mixed-native force key over
the concrete `hsAdj` extraction now rests on exactly ONE carried predicate — the same faithfulness that (9C-2) also
gives the ② kernel predicate. -/
theorem keyEquivariant_compKey_skStruct_rigid
    (hru : ∀ (adj : AdjMatrix n) (χ : Colouring n), RigidFrameUnique hsAdj adj χ) :
    KeyEquivariant (compKey (skStruct
      (minOrd (framesUniv (n := n)) (frameKeyHsAdj (Encodable.encode : List (Nat × List Bool) → Nat))
        (exists_isMinFrame_univ (frameKeyHsAdj Encodable.encode))) hsAdj)) :=
  keyEquivariant_compKey_skStruct_univ Encodable.encode
    (fun adj χ o o' ho ho' =>
      eq_of_isMinFrame_hsAdj Encodable.encode_injective adj χ (hru adj χ) o o' ho ho')

/-! ## Step 9C-2 — `RigidFrameUnique` from faithfulness + rigidity (the provable/carried boundary)

9C-1 reduced piece-2's `①` to `RigidFrameUnique`. This step proves it, exposing the honest gap boundary:

* **PROVABLE (linear algebra):** equal framed RREF ⟹ the connecting permutation `π = o'·o⁻¹` is a **symmetry of the
  framed recovered code** (`framedCodeSym_of_rrefCanon_eq`). Two ingredients: `frameSysBy_eq_transport` (framing `H` by
  `o` = framing the `π`-transported `H` by `o'`, from `frameRowBy_transport`) + `spans_eq_of_rrefCanon_eq` (equal
  `rrefCanon` ⟹ equal row space — the converse of `rrefCanon_eq_of_span_eq`, via `PivInv`'s `spanned`/`covers`).
* **CARRIED — the one irreducible gap:** `CodeFaithful` (a framed-code symmetry IS a graph colour-automorphism) =
  FAITHFULNESS = `ForcingModel.bridge`/L4. **Per-family resolvable** (CFI/multipede: the C#-tested recovery has
  code-auto = graph-auto by construction); general-**un**resolvable (its failure = the non-linear residue = the wall).
  The same wall carried throughout — the honest stopping point.
* **CARRIED — input hypothesis:** graph-rigidity (trivial `IsColAut`), from the interleaving handoff (the residue is
  rigid). ⚠ This is GRAPH rigidity, NOT `IsRigidF2` (trivial kernel) — the latter is the separation (`②`) condition;
  uniqueness needs the former. -/

/-- **Framing `H` by `o` = framing the `(o'·o⁻¹)`-transported `H` by `o'`.** The geometric identity relating two column
orders of the same system, straight from `frameRowBy_transport`. -/
theorem frameSysBy_eq_transport (o o' : Equiv.Perm (Fin n)) (H : List (Fin n → Bool)) :
    frameSysBy o H = frameSysBy o' (H.map (transportRow (o' * o⁻¹))) := by
  unfold frameSysBy
  rw [List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  show frameRowBy o r = (frameRowBy o' ∘ transportRow (o' * o⁻¹)) r
  have h := frameRowBy_transport (o' * o⁻¹) o r
  rw [inv_mul_cancel_right] at h
  exact h.symm

/-- The reduced-echelon rows span the same space as the input rows (both ways), via `PivInv.spanned`/`covers`. -/
theorem spans_pivInv_iff {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : Kernel.PivInv n rows P) (hrows : ∀ r ∈ rows, r.length = n) (w : List Bool) :
    Spans n (P.map (·.2)) w ↔ Spans n rows w := by
  refine ⟨fun h => Spans.trans_basis hrows (fun b hb => ?_) h,
    fun h => Spans.trans_basis (fun b hb => ?_) (fun b hb => hpiv.covers b hb) h⟩
  · obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb; exact hpiv.spanned cp hcp
  · obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb; exact hpiv.len cp hcp

/-- **★ The converse of `rrefCanon_eq_of_span_eq`** — equal canonical RREF ⟹ equal row space. `rrefCanon` is a
canonical function OF the subspace, so it also DETERMINES it (the rref rows span the original, both ways). -/
theorem spans_eq_of_rrefCanon_eq {L1 L2 : List (List Bool)}
    (h1 : ∀ r ∈ L1, r.length = n) (h2 : ∀ r ∈ L2, r.length = n)
    (heq : rrefCanon n L1 = rrefCanon n L2) (w : List Bool) :
    Spans n L1 w ↔ Spans n L2 w := by
  rw [← spans_pivInv_iff (RigidRREF.pivInv_rrefCanon h1) h1 w,
      ← spans_pivInv_iff (RigidRREF.pivInv_rrefCanon h2) h2 w, heq]

/-- π is a symmetry of the `o`-framed recovered code: transporting the system by π leaves the framed row space fixed. -/
def FramedCodeSym (H : List (Fin n → Bool)) (o π : Equiv.Perm (Fin n)) : Prop :=
  ∀ w, Spans n (frameSysBy o (H.map (transportRow π))) w ↔ Spans n (frameSysBy o H) w

/-- **★★ PROVABLE half — equal framed RREF ⟹ the connecting perm `o'·o⁻¹` is a framed-code symmetry.** Combines
`frameSysBy_eq_transport` (rewrite the `o`-framing as the `π`-transported `o'`-framing) with `spans_eq_of_rrefCanon_eq`
(equal RREF ⟹ equal span). No faithfulness used — pure linear algebra. -/
theorem framedCodeSym_of_rrefCanon_eq (H : List (Fin n → Bool)) (o o' : Equiv.Perm (Fin n))
    (heq : rrefCanon n (frameSysBy o H) = rrefCanon n (frameSysBy o' H)) :
    FramedCodeSym H o' (o' * o⁻¹) := by
  rw [frameSysBy_eq_transport o o' H] at heq
  intro w
  exact spans_eq_of_rrefCanon_eq (length_mem_frameSysBy _ _) (length_mem_frameSysBy _ _) heq w

/-- **CARRIED — faithfulness (the wall gap):** a framed-code symmetry of the recovered system IS a graph
colour-automorphism. = `ForcingModel.bridge`/L4, per-family (CFI/multipede: C#-tested recovery, code-auto = graph-auto
by construction); its failure = the non-linear residue = the wall. -/
def CodeFaithful (H : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ (o π : Equiv.Perm (Fin n)), FramedCodeSym (H adj χ) o π → IsColAut adj χ π

/-- **★★ Assembly — `RigidFrameUnique` from faithfulness + graph rigidity.** Equal framed RREF ⟹ (provable) `o'·o⁻¹`
is a framed-code symmetry ⟹ (faithful) a graph colour-automorphism ⟹ (rigid) the identity ⟹ `o = o'`. -/
theorem rigidFrameUnique_of_codeFaithful (H : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n)
    (hcf : CodeFaithful H adj χ) (hrigid : ∀ π : Equiv.Perm (Fin n), IsColAut adj χ π → π = 1) :
    RigidFrameUnique H adj χ := by
  intro o o' heq
  have hsym := framedCodeSym_of_rrefCanon_eq (H adj χ) o o' heq
  have hone : o' * o⁻¹ = 1 := hrigid _ (hcf o' (o' * o⁻¹) hsym)
  exact (mul_inv_eq_one.mp hone).symm

/-- **★★★ Step 9C-2 capstone — the pure-rigid `①`, closed modulo {faithfulness, graph-rigidity}.** With the concrete
adjacency extraction `hsAdj`, 9C-1's `keyEquivariant_compKey_skStruct_rigid` obligation `RigidFrameUnique` is
discharged from exactly two honest carried facts: `CodeFaithful` (= the wall, per-family resolvable) and graph rigidity
(the input is rigid). So the whole rigid-linear `①` for the pure multipede rests on the shared faithfulness bridge. -/
theorem keyEquivariant_compKey_skStruct_faithful
    (hcf : ∀ (adj : AdjMatrix n) (χ : Colouring n), CodeFaithful hsAdj adj χ)
    (hrigid : ∀ (adj : AdjMatrix n) (χ : Colouring n) (π : Equiv.Perm (Fin n)),
      IsColAut adj χ π → π = 1) :
    KeyEquivariant (compKey (skStruct
      (minOrd (framesUniv (n := n)) (frameKeyHsAdj (Encodable.encode : List (Nat × List Bool) → Nat))
        (exists_isMinFrame_univ (frameKeyHsAdj Encodable.encode))) hsAdj)) :=
  keyEquivariant_compKey_skStruct_rigid
    (fun adj χ => rigidFrameUnique_of_codeFaithful hsAdj adj χ (hcf adj χ) (hrigid adj χ))

/-! ## Step 9D — the MIXED-NATIVE reader: aggregate over the equivariant frame set (route around whole-node rigidity)

Steps 6b–9C read via a SINGLE `ord : Perm` (`structRead ord`), whose `①` (`ReadEquivariant ⟸ OrdEquivariant`) needs a
UNIQUE equivariant order = **whole-node graph rigidity** (the step-8 crux, made unavoidable by 9A's `Classical.choose`
of a unique minimizer, then explicit in 9C's `RigidFrameUnique`/rigidity). That closes only PURELY-rigid nodes —
insufficient for the mixed residue (`CellsAreOrbits` false ⟹ *some* but not all decisions rigid), the real target.
Those single-`ord` results are kept as the `ker=0` / purely-rigid ANCHOR; this step is the general reader.

**The fix — don't PICK a frame; aggregate the per-frame read over the whole equivariant frame set.** No frame is
chosen ⟹ no uniqueness/rigidity. `ReadEquivariant` holds UNCONDITIONALLY (the frame set transports, so the aggregate
is invariant); gauge/orbit pairs tie automatically (`ReadEquivariant` at a colour-aut); rigid pairs separate via the
per-pair carried faithfulness (`ReadSeparatesRigid`, step 7) — never whole-node rigidity.

⚠ **COST — no NEW exponential.** The aggregate ranges over `frames adj χ`; with `frames = framesUniv` (all `n!`
orders) it is exponential — but that is the SAME `②`-cost deferral as 9B (`framesUniv` = correct-but-exponential; the
poly/greedy structural frame set, bounded ring rank, drops into the SAME `FramesEquivariant` slot unchanged). The `①`
here is **frame-set-agnostic** (any `FramesEquivariant frames` works), so it is poly-frame-ready. -/

/-- The per-frame structural read of vertex `v` under a fixed column order `o`. -/
def structReadAt (o : Equiv.Perm (Fin n)) (Hs : AdjMatrix n → Colouring n → List (Fin n → Bool))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  bitsToNat (colSig (rrefCanon n (frameSysBy o (Hs adj χ))) (o.symm v))

/-- The per-frame read transports (for `hsAdj`): reading `σv` under frame `σ·o` on the relabelled node = reading `v`
under frame `o` on the original — `framedRREF_hsAdj_transport` + `(σ·o).symm (σv) = o.symm v`. -/
theorem structReadAt_hsAdj_transport (σ o : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) :
    structReadAt (σ * o) hsAdj (relabelAdj σ adj) (transportColouring σ χ) (σ v)
      = structReadAt o hsAdj adj χ v := by
  simp only [structReadAt, framedRREF_hsAdj_transport σ o adj χ]
  have hpos : (σ * o).symm (σ v) = o.symm v := by
    have h1 : (σ * o) (o.symm v) = σ v := by rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    rw [← h1, Equiv.symm_apply_apply]
  rw [hpos]

/-- **The mixed-native reader** — the sorted set of per-frame reads of `v` over the equivariant frame set, encoded to
`ℕ`. No frame is chosen ⟹ no uniqueness/rigidity. Parameterized by the frame set (poly-ready). -/
noncomputable def readAgg (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  Encodable.encode
    (((frames adj χ).image (fun o => structReadAt o hsAdj adj χ v)).sort (· ≤ ·))

/-- **★★★ Step 9D — `ReadEquivariant (readAgg frames)` UNCONDITIONALLY**, from `FramesEquivariant` ALONE — NO
uniqueness, NO rigidity. The frame set transports as `o ↦ σ·o` and each per-frame read transports
(`structReadAt_hsAdj_transport`), so the image `Finset` — hence its sorted encoding — is invariant. **This is the route
around whole-node rigidity: `①` now holds on EVERY input, mixed included.** -/
theorem readEquivariant_readAgg (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (hf : FramesEquivariant frames) :
    ReadEquivariant (readAgg frames) := by
  intro σ adj χ v
  have himg : (frames (relabelAdj σ adj) (transportColouring σ χ)).image
        (fun o => structReadAt o hsAdj (relabelAdj σ adj) (transportColouring σ χ) (σ v))
      = (frames adj χ).image (fun o => structReadAt o hsAdj adj χ v) := by
    rw [hf σ adj χ, Finset.image_image]
    refine Finset.image_congr (fun o _ => ?_)
    show structReadAt (σ * o) hsAdj (relabelAdj σ adj) (transportColouring σ χ) (σ v)
      = structReadAt o hsAdj adj χ v
    exact structReadAt_hsAdj_transport σ o adj χ v
  simp only [readAgg, himg]

/-- **★★★ Step 9D `①` capstone (general, MIXED-NATIVE).** `compKey (skRead (readAgg frames))`'s `KeyEquivariant` from
`FramesEquivariant` alone — no rigidity. The whole rigid-linear `①` for the mixed residue, on any equivariant frame
set. -/
theorem keyEquivariant_compKey_readAgg
    (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (hf : FramesEquivariant frames) :
    KeyEquivariant (compKey (skRead (readAgg frames))) :=
  keyEquivariant_compKey_skRead (readAgg frames) (readEquivariant_readAgg frames hf)

/-- **★★★ Step 9D `②`/firing capstone (general, MIXED-NATIVE).** `NodeResolved` from the per-pair kernel predicate
`ReadSeparatesRigid (readAgg frames)` + rigidity of the exposed pair — no global discreteness, no whole-node rigidity.
Gauge pairs tie (consume's `cellIsOrbit` disjunct); only the exposed rigid decisions separate. -/
theorem nodeResolved_compKey_readAgg
    (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (hsep : ReadSeparatesRigid (readAgg frames) adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skRead (readAgg frames))) S adj χ :=
  nodeResolved_compKey_skRead (readAgg frames) S adj χ hnd hsep hrigid

/-- **★★★ Step 9D concrete — the mixed-native `①`, closed with NO carried hypothesis** (over the exhaustive
`framesUniv`; exponential-but-correct, the poly frame set drops in unchanged). Contrast the purely-rigid
`keyEquivariant_compKey_skStruct_rigid`, which carried `RigidFrameUnique`: the aggregate reader owes NOTHING on `①`
for ANY input, rigid or mixed. -/
theorem keyEquivariant_compKey_readAgg_univ :
    KeyEquivariant (compKey (skRead (readAgg (framesUniv (n := n))))) :=
  keyEquivariant_compKey_readAgg framesUniv framesEquivariant_univ

/-! ## Step 9D-② — separation: `ReadSeparatesRigid (readAgg)` via the MIXED-NATIVE faithfulness `AggFaithful`

The `②`/firing side of the aggregate reader. `readAgg u = readAgg w` ⟺ (encode∘sort injective) the **sets of per-frame
signatures** coincide (`aggSet u = aggSet w`). So separation reduces to a faithfulness predicate — but with the crucial
**modification for non-trivial automorphisms** (vs the purely-rigid 9C):

* 9C (purely rigid): code-symmetric ⟹ **identity** (trivial aut).
* 9D (mixed): **`AggFaithful` — aggregate-indistinguishable ⟹ AUTOMORPHIC** (`∃ colour-aut σ, σu=w`), NOT identity.
  This admits gauge, and the two directions come out mixed-natively:
  - **gauge pairs tie provably** (`readAgg_eq_of_aut`, from `ReadEquivariant` at the colour-aut) — no over-separation;
  - **non-automorphic pairs separate** (`readSeparatesRigid_readAgg`, from `AggFaithful` + the non-aut hypothesis).

Carried gap = `AggFaithful` (aggregate faithfulness, the wall, per-family). ⚠ `aggSet` is a SET (dedup); the MULTISET
aggregate is strictly finer and weakens `AggFaithful` if the set proves too coarse on a family — a drop-in `②` upgrade. -/

/-- The set of per-frame signatures of vertex `v` — the semantic content of `readAgg` (before sort/encode). -/
noncomputable def aggSet (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Finset Nat :=
  (frames adj χ).image (fun o => structReadAt o hsAdj adj χ v)

/-- `readAgg` is `encode` of the sorted `aggSet` (definitional). -/
theorem readAgg_eq_encode_sort (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    readAgg frames adj χ v = Encodable.encode ((aggSet frames adj χ v).sort (· ≤ ·)) := rfl

/-- **`readAgg` distinguishes vertices exactly when their signature SETS differ** — `encode ∘ sort` is injective on
`Finset ℕ` (`encode` injective; `sort` determines the Finset via `toFinset`). -/
theorem aggSet_eq_of_readAgg_eq (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (h : readAgg frames adj χ u = readAgg frames adj χ w) :
    aggSet frames adj χ u = aggSet frames adj χ w := by
  rw [readAgg_eq_encode_sort, readAgg_eq_encode_sort] at h
  have hs := Encodable.encode_injective h
  have := congrArg List.toFinset hs
  rwa [Finset.sort_toFinset, Finset.sort_toFinset] at this

/-- **★ Gauge pairs TIE (correctness — no over-separation).** An automorphic pair (`σ` a colour-aut, `σ u = w`) gets
EQUAL `readAgg`, straight from `ReadEquivariant` at `σ` (`relabelAdj σ adj = adj`, `transportColouring σ χ = χ`). So the
aggregate reader correctly leaves gauge/orbit pairs unrefined (consume's job) — it separates ONLY genuine decisions. -/
theorem readAgg_eq_of_aut (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (hf : FramesEquivariant frames) (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (σ : Equiv.Perm (Fin n)) (hσ : IsColAut adj χ σ) (hσuw : σ u = w) :
    readAgg frames adj χ u = readAgg frames adj χ w := by
  have h := readEquivariant_readAgg frames hf σ adj χ u
  rw [hσ.relabel, hσ.transport, hσuw] at h
  exact h.symm

/-- **CARRIED — aggregate faithfulness (the wall, MIXED-NATIVE form):** if two co-cellular vertices have the same set
of per-frame signatures, they are **automorphic** (`∃ colour-aut σ, σ u = w`) — NOT merely equal. This is the mixed
analog of 9C-2's `CodeFaithful` (which landed on the identity); admitting non-trivial `σ` is exactly what lets the
mixed residue's gauge coexist with rigid decisions. Per-family resolvable; its failure = the non-linear residue. -/
def AggFaithful (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    aggSet frames adj χ u = aggSet frames adj χ w → ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w

/-- **★★ `ReadSeparatesRigid (readAgg frames)` from `AggFaithful`.** A non-automorphic, non-discretizing, co-cellular
pair gets distinct `readAgg`: equal `readAgg` ⟹ equal signature sets ⟹ (`AggFaithful`) automorphic — contradicting
non-automorphy. No rigidity of the node/cell; purely the per-pair non-aut hypothesis. -/
theorem readSeparatesRigid_readAgg (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (adj : AdjMatrix n) (χ : Colouring n) (haf : AggFaithful frames adj χ) :
    ReadSeparatesRigid (readAgg frames) adj χ := by
  intro u hu w hw hnaut _ _ heq
  obtain ⟨σ, hσ, hσuw⟩ := haf u hu w hw (aggSet_eq_of_readAgg_eq frames adj χ u w heq)
  exact hnaut σ hσ hσuw

/-- **★★★ Step 9D-② capstone — MIXED-NATIVE firing from `AggFaithful` alone.** `NodeResolved` for the aggregate force
key from the aggregate faithfulness (`②`) + the exposed-pairs-non-automorphic condition — no whole-node/whole-cell
rigidity, no global discreteness. Combined with `keyEquivariant_compKey_readAgg` (`①`, zero carried), the whole
rigid-linear seal for the mixed-native reader rests on exactly `{FramesEquivariant, AggFaithful}` — the frame-set
transport (structural) and the aggregate faithfulness (the shared wall). -/
theorem nodeResolved_compKey_readAgg_faithful
    (frames : AdjMatrix n → Colouring n → Finset (Equiv.Perm (Fin n)))
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (haf : AggFaithful frames adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skRead (readAgg frames))) S adj χ :=
  nodeResolved_compKey_readAgg frames S adj χ hnd
    (readSeparatesRigid_readAgg frames adj χ haf) hrigid

/-! ## Step 9F — the DE-CLASSED base-quotient aggregate reader (the TYPE ESCAPE; retires full-order `seedFrames`)

**Why the full-order frame set is impossible at poly cardinality (the finding that retired `seedFrames`).** `readAgg`
(9D) ranges over `Finset (Equiv.Perm (Fin n))` — FULL vertex orders. At a **gauge** colour-aut `σ` (`relabelAdj σ adj
= adj`, `transportColouring σ χ = χ`), `FramesEquivariant` forces `frames adj χ = (frames adj χ).image (σ * ·)`: the
set is invariant under LEFT-MULTIPLICATION by the whole gauge group `G`. Left-mult on a group is a **free** action
(`σ * o = o ⟹ σ = 1`), so any nonempty invariant set is a union of full `G`-orbits ⟹ `|frames| ≥ |G| = 2^β`. **No
poly `FramesEquivariant` set of full orders exists on a gauged (mixed) input — the exponential is forced by the TYPE,
not the choice of set.** (Machine-checkable against `framesEquivariant_univ` + `structReadAt`'s `o.symm v`. The old
`seedFrames`/`OrderOfEquivariant` interface is thus target-vacuous: `OrderOfEquivariant` at a gauge `σ` fixing a seed
forces `σ = 1`, so it holds only on purely-rigid inputs.)

**The escape — range the aggregate over an ABSTRACT base-frame type `B` on which the gauge acts NON-freely.** The
recovered base is gauge-fixed (gauge induces the identity on the base), so `act σ` is trivial for gauge `σ`; a
gauge-closed frame set of poly (even singleton) cardinality EXISTS and the free-action bound does not apply. This
section re-types the whole aggregate over generic `(B, act, baseRead)` with two clean obligations: `FramesEquivariantB`
(the frame set transports via `act`) and `ReadAtEquivariant` (each per-frame read is a vertex-invariant). The
full-order `readAgg` is exactly the `B = Perm`, `act = (σ * ·)` instance (the exponential anchor); the concrete
`forcedVal`-based **pinning** instance below is the poly-ready one, non-vacuous already at a singleton frame family.

▶ NEXT (the probe, then P2): a RICH pinning family whose aggregate discretizes the rigid part while tying gauge —
`AggFaithfulB` non-vacuous on `mp7`. The `①`/type escape is settled here; richness/cost is the concrete pinning P2. -/

variable {B : Type*} [DecidableEq B]

/-- The frame set transports via the base-frame action `act` (not left-mult on `Perm`). For a base-quotient `B`,
`act σ` is the identity on any gauge `σ` — exactly what dodges the free-action `≥ 2^β` bound. -/
def FramesEquivariantB (frames : AdjMatrix n → Colouring n → Finset B)
    (act : Equiv.Perm (Fin n) → B → B) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    frames (relabelAdj σ adj) (transportColouring σ χ) = (frames adj χ).image (act σ)

/-- Each per-frame read is a vertex-invariant: reading `σ v` under the `act σ`-moved frame on the relabelled node =
reading `v` under the original frame. The base-quotient analog of `structReadAt_hsAdj_transport`. -/
def ReadAtEquivariant (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (act : Equiv.Perm (Fin n) → B → B) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (b : B) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    baseRead (act σ b) (relabelAdj σ adj) (transportColouring σ χ) (σ v) = baseRead b adj χ v

/-- **The de-classed aggregate reader** — the sorted, encoded SET of a vertex's per-frame reads over the base-frame
set. Same shape as `readAgg`, but the frames are base-quotient objects (`B`), not full orders. -/
noncomputable def readAggB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  Encodable.encode (((frames adj χ).image (fun b => baseRead b adj χ v)).sort (· ≤ ·))

/-- **★★★ `ReadEquivariant (readAggB …)` UNCONDITIONALLY** — from `FramesEquivariantB` + `ReadAtEquivariant` alone,
NO rigidity. The frame set transports (`act σ`) and each read transports, so the image `Finset` — hence its sorted
encoding — is invariant. The `①` of the de-classed reader, on ANY input, poly frame set included. -/
theorem readEquivariant_readAggB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat) (act : Equiv.Perm (Fin n) → B → B)
    (hf : FramesEquivariantB frames act) (hr : ReadAtEquivariant baseRead act) :
    ReadEquivariant (readAggB frames baseRead) := by
  intro σ adj χ v
  have himg : (frames (relabelAdj σ adj) (transportColouring σ χ)).image
        (fun b => baseRead b (relabelAdj σ adj) (transportColouring σ χ) (σ v))
      = (frames adj χ).image (fun b => baseRead b adj χ v) := by
    rw [hf σ adj χ, Finset.image_image]
    refine Finset.image_congr (fun b _ => ?_)
    show baseRead (act σ b) (relabelAdj σ adj) (transportColouring σ χ) (σ v) = baseRead b adj χ v
    exact hr σ b adj χ v
  simp only [readAggB, himg]

/-- **★★★ `①` capstone (de-classed).** `compKey (skRead (readAggB …))`'s `KeyEquivariant` from the base-frame
equivariance alone. -/
theorem keyEquivariant_compKey_readAggB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat) (act : Equiv.Perm (Fin n) → B → B)
    (hf : FramesEquivariantB frames act) (hr : ReadAtEquivariant baseRead act) :
    KeyEquivariant (compKey (skRead (readAggB frames baseRead))) :=
  keyEquivariant_compKey_skRead (readAggB frames baseRead)
    (readEquivariant_readAggB frames baseRead act hf hr)

/-! ### Step 9F `②` — separation via the base-quotient faithfulness `AggFaithfulB` (mixed-native) -/

/-- The set of per-frame reads of `v` — the semantic content of `readAggB` before sort/encode. -/
noncomputable def aggSetB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Finset Nat :=
  (frames adj χ).image (fun b => baseRead b adj χ v)

omit [DecidableEq B] in
theorem readAggB_eq_encode_sort (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    readAggB frames baseRead adj χ v
      = Encodable.encode ((aggSetB frames baseRead adj χ v).sort (· ≤ ·)) := rfl

omit [DecidableEq B] in
/-- `readAggB` distinguishes vertices exactly when their per-frame read SETS differ (`encode ∘ sort` injective). -/
theorem aggSetB_eq_of_readAggB_eq (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (h : readAggB frames baseRead adj χ u = readAggB frames baseRead adj χ w) :
    aggSetB frames baseRead adj χ u = aggSetB frames baseRead adj χ w := by
  rw [readAggB_eq_encode_sort, readAggB_eq_encode_sort] at h
  have hs := Encodable.encode_injective h
  have := congrArg List.toFinset hs
  rwa [Finset.sort_toFinset, Finset.sort_toFinset] at this

/-- **★ Gauge pairs TIE** (correctness — no over-separation) — an automorphic pair gets EQUAL `readAggB`, from
`ReadEquivariant` at `σ`. So the de-classed reader leaves gauge/orbit pairs to consume. -/
theorem readAggB_eq_of_aut (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat) (act : Equiv.Perm (Fin n) → B → B)
    (hf : FramesEquivariantB frames act) (hr : ReadAtEquivariant baseRead act)
    (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (σ : Equiv.Perm (Fin n)) (hσ : IsColAut adj χ σ) (hσuw : σ u = w) :
    readAggB frames baseRead adj χ u = readAggB frames baseRead adj χ w := by
  have h := readEquivariant_readAggB frames baseRead act hf hr σ adj χ u
  rw [hσ.relabel, hσ.transport, hσuw] at h
  exact h.symm

/-- **CARRIED — base-quotient aggregate faithfulness (the wall, mixed-native):** co-cellular vertices with the same
per-frame read SET are **automorphic** (not merely equal). Same shape as `AggFaithful`, over base frames; per-family
resolvable (P3), its failure = the non-linear residue. -/
def AggFaithfulB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    aggSetB frames baseRead adj χ u = aggSetB frames baseRead adj χ w →
      ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w

omit [DecidableEq B] in
/-- **★★ `ReadSeparatesRigid (readAggB …)` from `AggFaithfulB`** — a non-automorphic, non-discretizing, co-cellular
pair gets distinct `readAggB`. No rigidity of the node/cell; purely the per-pair non-aut hypothesis. -/
theorem readSeparatesRigid_readAggB (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (adj : AdjMatrix n) (χ : Colouring n) (haf : AggFaithfulB frames baseRead adj χ) :
    ReadSeparatesRigid (readAggB frames baseRead) adj χ := by
  intro u hu w hw hnaut _ _ heq
  obtain ⟨σ, hσ, hσuw⟩ := haf u hu w hw (aggSetB_eq_of_readAggB_eq frames baseRead adj χ u w heq)
  exact hnaut σ hσ hσuw

omit [DecidableEq B] in
/-- **★★★ `②`/firing capstone (de-classed, mixed-native).** `NodeResolved` from `AggFaithfulB` + the exposed pairs
non-automorphic — no whole-node/whole-cell rigidity, no global discreteness. With `keyEquivariant_compKey_readAggB`
(`①`), the whole de-classed seal rests on exactly `{FramesEquivariantB, ReadAtEquivariant, AggFaithfulB}`. -/
theorem nodeResolved_compKey_readAggB_faithful (frames : AdjMatrix n → Colouring n → Finset B)
    (baseRead : B → AdjMatrix n → Colouring n → Fin n → Nat)
    (S : Consume.Supply n) (adj : AdjMatrix n) (χ : Colouring n) (hnd : ¬ Discrete χ)
    (haf : AggFaithfulB frames baseRead adj χ)
    (hrigid : ∀ u ∈ branches χ, ∀ w ∈ branches χ, u ≠ w →
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Select.NodeResolved (compKey (skRead (readAggB frames baseRead))) S adj χ :=
  nodeResolved_compKey_skRead (readAggB frames baseRead) S adj χ hnd
    (readSeparatesRigid_readAggB frames baseRead adj χ haf) hrigid

/-- **★ Singleton frame families are `FramesEquivariantB`** when `act` fixes the base point — the concrete escape from
the free-action `2^β` bound (`|frames| = 1`, poly). -/
theorem framesEquivariantB_singleton (act : Equiv.Perm (Fin n) → B → B) (b₀ : B)
    (hb₀ : ∀ σ : Equiv.Perm (Fin n), act σ b₀ = b₀) :
    FramesEquivariantB (fun _ _ => ({b₀} : Finset B)) act := by
  intro σ adj χ
  rw [Finset.image_singleton, hb₀ σ]

/-! ### Step 9F concrete — the pinning instance (`forcedVal`-based, gauge-FIXED frames): the escape realized

`B = Finset (Fin n → ZMod 2)` = a base **pinning** (extra F₂ constraints on top of the extracted system). Gauge fixes
the base ⟹ `pinAct σ` fixes the recovered base pinnings, so a gauge-closed frame set of poly (here singleton)
cardinality EXISTS — the free-action `2^β` bound is dodged. The read reuses step 2's `forcedVal` (ORDER-FREE, already
transport-proven): a vertex reads its forced value under (base system ∪ pinning). This is the C# `Recover → base pin →
solve` read with NO full order and NO `rrefCanon` in the `①` handle. The rich (discretizing) pinning family is P2. -/

/-- The pinning action: transport the pinning constraints by `transportVec σ`. Fixes `∅` (and any gauge-recovered base
pinning), so it is NOT free — this is the type-level reason a poly `FramesEquivariantB` set exists. -/
def pinAct (σ : Equiv.Perm (Fin n)) (p : Finset (Fin n → ZMod 2)) : Finset (Fin n → ZMod 2) :=
  p.image (transportVec σ)

/-- The base-pinned forced read: vertex `v`'s forced value under (extracted system ∪ pinning `p`), encoded. Reuses
`forcedVal` — order-free, no `rrefCanon` in the `①` handle. -/
noncomputable def baseReadPin
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (p : Finset (Fin n → ZMod 2)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  encOpt (forcedVal ((extract adj χ).1 ∪ p) (extract adj χ).2 v)

/-- **★★ The pinned read is a vertex-invariant** — from `forcedVal_transport` + the carried `RefExtractEquivariant`
(image distributes over `∪`). The concrete `ReadAtEquivariant` for the pinning instance. -/
theorem readAtEquivariant_baseReadPin
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) :
    ReadAtEquivariant (baseReadPin extract) pinAct := by
  intro σ p adj χ v
  simp only [baseReadPin, pinAct, hext σ adj χ]
  rw [← Finset.image_union, forcedVal_transport σ ((extract adj χ).1 ∪ p) (extract adj χ).2 v]

/-- **★★★ The concrete de-classed `①`, POLY (singleton pinning family), ZERO carried beyond the extraction.** The
base-quotient analog of `keyEquivariant_compKey_readAgg_univ`, but the frame set is size 1, not `n!` — the type escape
realized: gauge fixes `∅`, so this is a genuine POLY `FramesEquivariantB` witness. (Discretization/richness = a bigger
pinning family = P2/the probe.) -/
theorem keyEquivariant_compKey_readAggB_pin
    (extract : AdjMatrix n → Colouring n → Finset (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (hext : RefExtractEquivariant extract) :
    KeyEquivariant (compKey (skRead
      (readAggB (fun _ _ => ({∅} : Finset (Finset (Fin n → ZMod 2)))) (baseReadPin extract)))) :=
  keyEquivariant_compKey_readAggB _ (baseReadPin extract) pinAct
    (framesEquivariantB_singleton pinAct ∅ (fun σ => by simp [pinAct]))
    (readAtEquivariant_baseReadPin extract hext)

end RigidRefine
end ChainDescent
