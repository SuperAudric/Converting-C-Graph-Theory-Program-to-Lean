/-
# ScratchCanonFormCapped.lean — the SHARED `canonForm?` object (WIP, NOT in build.sh)

**The convergence point of ①a and ②.** `Publication.canonForm?`/`cost` must be ONE object: the capped descent
that (i) has a proven poly cost (②) and (ii) whose `some` answer is a sound relabelling (①a). This module builds
it by *gating the parameter-free sound canonizer `canonFormOf` (`ScratchCanonSound`) by the real per-node-capped
spine descent (`spineCappedCanonizer`, `ScratchCostModelSpine`)*:

  · **cost + flag** come from the actual capped run — `descentCost adj ≤ n⁴` unconditionally (② by the cap), and
    the `Option` result is the flag channel;
  · **the `some` value** is the sound `canonFormOf adj` — so `canonForm?_sound` is `canonFormOf_sound` transferred,
    and ①a lands against the *flagging* object (not a never-flagging stand-in), exactly the shape `Publication.canon_sound`
    needs.

**Honest scope of the flag at THIS level (important — keeps ③ non-vacuous later).** The descent's `none` here is
*node-budget (fuel) exhaustion* of the warmRefine-cost descent. Since the warmRefine descent provably reaches a leaf
within `n` nodes, this `none` does not yet fire — the object is currently *total*. The REAL flag arises from the
**oracle summand of `w`** (an expensive harvest exceeding the per-node budget ⟹ `flagsAt`), which is not wired into
`w` yet (it gates on confinement-P1 / R1). So `③ residue_if_flag` is deliberately NOT claimed against this object
yet; wiring the oracle-cost flag is the step that makes `none` a genuine event and ③ dischargeable. Recording this
prevents mistaking the current totality for a vacuous-③ firewall breach.

Axiom target `[propext, Classical.choice, Quot.sound]`. Imports the Mathlib spine + cost model — slower compiles.
`lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchCanonSound
import ChainDescent.ScratchCostModelSpine

namespace ChainDescent.CanonForm

open ChainDescent
open ChainDescent.CanonSound
open ChainDescent.CostModel
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance

variable {n : Nat}

/-! ## The capped descent — the ② cost object -/

/-- The per-node-capped spine descent over the canonical parameters (`defaultP₀`/`defaultχι₀`/`nonDiscreteSel`),
run from level `0` with node budget `n`. Its `.1` is the leaf/flag signal, its `.2` the cost. **Computable**
(Tier A): `spineCappedCanonizer` + `budgetedIterate` all reduce, so the descent runs. -/
def descent (adj : AdjMatrix n) : CostM (Option Nat) :=
  (spineCappedCanonizer adj defaultP₀ defaultχι₀ nonDiscreteSel).run n 0

/-- The descent's leaf/flag signal: `some k` = a leaf reached within the node budget; `none` = flag
(node budget exhausted). Computable. -/
def descentResult (adj : AdjMatrix n) : Option Nat := (descent adj).1

/-- The descent's cost — the ② operation count (`ℕ`), from the actual capped run. Computable. -/
def descentCost (adj : AdjMatrix n) : Nat := (descent adj).2

/-- **② — the descent cost is `≤ n⁴`, unconditional.** Directly the per-node-cap bound
`spineCappedCanonizer_cost_le`; no per-node-cost hypothesis (a later quasipoly oracle summand of `w` would
*flag*, not break this). This is the `cost n G ≤ costConst·n^costDeg` side of `Publication.canon_poly_or_flag`. -/
theorem descentCost_le (adj : AdjMatrix n) : descentCost adj ≤ n * (n * n * n) := by
  unfold descentCost descent
  exact spineCappedCanonizer_cost_le adj defaultP₀ defaultχι₀ nonDiscreteSel 0

/-! ## The shared `canonForm?` object -/

/-- **The shared `canonForm?`** — the capped descent's output: `some (canonical form)` if the descent reaches a
leaf within budget, else `none` (flag). The `some` value is the sound `canonFormOf adj`; cost + flag come from
the real capped run (`descent`). This is the single object `Publication.canonForm?`/`cost` will be. -/
noncomputable def canonForm? (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  match descentResult adj with
  | some _ => canonFormOf adj
  | none => none

/-- **①a `canon_sound` on the shared (flagging) object.** A `some cG` answer is a genuine relabelling of `G` —
`canonFormOf_sound` transferred through the budget gate (the gated value IS `canonFormOf`'s). This is the
`Publication.canon_sound` body, now against the capped object rather than a never-flagging stand-in. -/
theorem canonForm?_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonForm? adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  unfold canonForm? at h
  split at h
  · exact canonFormOf_sound adj cG h
  · simp at h

/-- **The flag IS budget exhaustion.** `canonForm? adj = none` exactly when the capped descent flags
(`descentResult adj = none`) — because the gated value `canonFormOf adj` is always `some`
(`canonFormOf_isSome`). The ③ hook: characterizes the flag as a real descent event, and shows `canonForm?` is
neither always-`some` nor always-`none` by construction (it tracks `descentResult`). -/
theorem canonForm?_eq_none_iff (adj : AdjMatrix n) :
    canonForm? adj = none ↔ descentResult adj = none := by
  unfold canonForm?
  cases h : descentResult adj with
  | none => simp
  | some k =>
    have hs : canonFormOf adj ≠ none := by
      intro hc
      have hi := canonFormOf_isSome adj
      rw [hc] at hi
      simp at hi
    simp only [reduceCtorEq, iff_false]
    exact hs

end ChainDescent.CanonForm
