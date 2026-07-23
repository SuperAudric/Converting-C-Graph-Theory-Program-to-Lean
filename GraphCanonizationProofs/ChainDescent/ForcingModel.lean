import ChainDescent.ForcingCircuits
import ChainDescent.RigidSolverInterface

/-!
# P2 — the forcing-model bridge (graph ↔ F₂ system)

This module is the **forcing-model bridge** of the rigid seal (`docs/chain-descent-rigid-seal.md` §8.2 P2;
`chain-descent-ir-blindspot-solver.md` §11.3–§11.4a Layer B). It links the *graph* side (the descent's 1-WL
refinement forcing, over vertices `Fin n`) to the *pure-F₂* side (`ForcingCircuits.Forced` / `rowspace`, over
abstract variables `ι`), so that P1's extraction-soundness transports to a **graph-level** statement — which is
what P3-F₂'s concrete solver `gen` consumes.

## What P2 is — and what is carried

The empirical content of P2 is **Layer B**: *WL-forcing on the real (multipede/CFI) graph = unit-propagation on
the recovered F₂ matrix `H`, exactly* (validated 50/50, mechanism-verified; asymptotics cited Neuen–Schweitzer,
`IR §11.4a`). This is a property of the **gadget model**, not a universal theorem, so — per the roadmap — the
bridge is **carried as a hypothesis** (`ForcingModel.bridge`). Where it fails, the residue is *non-linear* rigid.

The graph-side forcing oracle `gForce` is likewise abstract here: its concrete realization by the refinement
`encodeFreeFast` is the further wiring step (deferred, like P3-F₂'s RREF). What P2 **proves** is the transport and
the exact-recovery reduction; what it **carries** is `bridge` + `gForce`'s graph realization + `RecoversRowspace`
(the Layer-C generation).

## Deliverables

* `ForcingModel adj χ H var gForce` — the bridge: `gForce S j ↔ Forced H S j` (Layer B), with `var : ι → Fin n`
  the variable-to-vertex embedding.
* `recoverable_of_model` / `forcing_certificate_of_model` — **the transport**: anything the graph forces is backed
  by a genuine `rowspace H` codeword (P1's `forced_certificate` pulled across the bridge). Graph-extraction
  soundness — what P3-F₂ consumes.
* `rowspace_eq_span_recoverable` — **exact recovery** reduces to the carried generation `RecoversRowspace`
  (soundness direction done here; generation is the delicate minimal-circuit / Layer-C content, carried).
-/

namespace ChainDescent
namespace ForcingModel

open ChainDescent.Descend
open ChainDescent.ForcingCircuits

variable {n : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The bridge -/

/-- **The forcing-model bridge (Layer B, carried).** The graph node `(adj, χ)` models the F₂ system `H` over
variables `ι` embedded by `var : ι → Fin n` when the graph's 1-WL forcing oracle `gForce` agrees, on every
known-set/target, with unit-propagation over `H` (`ForcingCircuits.Forced`). This equivalence is the empirical
Layer-B fact — true for the gadget model, carried in general. -/
structure ForcingModel (adj : AdjMatrix n) (χ : Colouring n)
    (H : Finset (ι → ZMod 2)) (var : ι → Fin n)
    (gForce : Finset ι → ι → Prop) : Prop where
  /-- **WL-forcing = unit-propagation** (`IR §11.4a` Layer B). -/
  bridge : ∀ (S : Finset ι) (j : ι), gForce S j ↔ Forced H S j

/-! ## 2. The transport — graph forcing is backed by the row space -/

/-- A codeword is **recoverable** from forcing: it is the `rowspace H` certificate of some unit-propagation step,
supported inside `insert j S`. (The set the extraction accumulates.) -/
def Recoverable (H : Finset (ι → ZMod 2)) (c : ι → ZMod 2) : Prop :=
  ∃ (S : Finset ι) (j : ι), j ∉ S ∧ Forced H S j ∧ c ∈ rowspace H ∧ c j ≠ 0 ∧
    ∀ k, c k ≠ 0 → k = j ∨ k ∈ S

/-- Recoverable codewords lie in the row space (immediate from the definition; the soundness half). -/
theorem recoverable_mem_rowspace {H : Finset (ι → ZMod 2)} {c : ι → ZMod 2}
    (h : Recoverable H c) : c ∈ rowspace H := by
  obtain ⟨_, _, _, _, hc, _, _⟩ := h; exact hc

/-- **★★ P2 transport.** Anything the graph forces (`gForce`) is backed by a genuine `rowspace H` codeword —
P1's `forced_certificate` pulled across the Layer-B bridge. This is the **graph-extraction soundness** the
concrete solver `gen` (P3-F₂) consumes: every forced decision is a real row-space consequence. -/
theorem recoverable_of_model {adj : AdjMatrix n} {χ : Colouring n} {H : Finset (ι → ZMod 2)}
    {var : ι → Fin n} {gForce : Finset ι → ι → Prop}
    (M : ForcingModel adj χ H var gForce) (S : Finset ι) (j : ι) (hj : j ∉ S) (h : gForce S j) :
    ∃ c, Recoverable H c ∧ c j ≠ 0 := by
  have hForced : Forced H S j := (M.bridge S j).mp h
  obtain ⟨c, hcmem, hcj, hsupp⟩ := certificate_of_forced_notMem H S j hj hForced
  exact ⟨c, ⟨S, j, hj, hForced, hcmem, hcj, hsupp⟩, hcj⟩

/-- The transport in certificate form (unpacked). -/
theorem forcing_certificate_of_model {adj : AdjMatrix n} {χ : Colouring n} {H : Finset (ι → ZMod 2)}
    {var : ι → Fin n} {gForce : Finset ι → ι → Prop}
    (M : ForcingModel adj χ H var gForce) (S : Finset ι) (j : ι) (hj : j ∉ S) (h : gForce S j) :
    ∃ c ∈ rowspace H, c j ≠ 0 ∧ ∀ k, c k ≠ 0 → k = j ∨ k ∈ S :=
  certificate_of_forced_notMem H S j hj ((M.bridge S j).mp h)

/-! ## 3. Exact recovery — reduces to the carried generation -/

/-- **The generation obligation (Layer C, carried).** The row space is spanned by the forcing-recoverable
codewords — the completeness of the extraction. This is the delicate minimal-circuit content (`IR §11.4a` #2:
`cl_up ≠ cl_lin`, only *minimal* circuits generate) together with the graph realization; it is carried. -/
def RecoversRowspace (H : Finset (ι → ZMod 2)) : Prop :=
  rowspace H ≤ Submodule.span (ZMod 2) {c | Recoverable H c}

/-- **★★ Exact recovery.** The forcing extraction recovers `rowspace H` **exactly**, modulo the carried
generation `RecoversRowspace`: the soundness inclusion (`span recoverable ≤ rowspace`) is discharged here from
P1; the completeness inclusion is `RecoversRowspace`. So P1 (soundness) + P2 (generation, carried) = the recovered
system is exactly `rowspace H`. -/
theorem rowspace_eq_span_recoverable (H : Finset (ι → ZMod 2)) (hgen : RecoversRowspace H) :
    rowspace H = Submodule.span (ZMod 2) {c | Recoverable H c} := by
  refine le_antisymm hgen ?_
  rw [Submodule.span_le]
  intro c hc
  exact recoverable_mem_rowspace hc

end ForcingModel
end ChainDescent
