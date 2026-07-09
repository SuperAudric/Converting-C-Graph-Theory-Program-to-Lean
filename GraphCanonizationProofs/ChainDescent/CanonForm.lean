/-
# ChainDescent.CanonForm — ①a soundness + the ② capped canonizer object (ported)

The soundness content (`canonForm_isLabelledAdj`: a descent leaf's `canonAdj` IS a `labelledAdj`),
the parameter-free canonizer `canonFormOf`, and the SHARED capped object `CanonForm.canonForm?`
(gated by the real capped descent, carrying `descentCost_le : cost ≤ n⁴` for ②).
These are the objects `Publication.{canon_sound, canon_poly_or_flag}` will plug into.

Axiom-clean `[propext, Classical.choice, Quot.sound]`. Ported 2026-07-09 from
ScratchCanonSound, ScratchCanonFormCapped.
-/
import ChainDescent.Spine
import ChainDescent.CostModel


/- ═══════════════════════════ (was ScratchCanonSound.lean) ═══════════════════════════ -/


namespace ChainDescent.CanonSound

open ChainDescent

variable {n : Nat}

/-- **The soundness CONTENT (value level).** The spine's leaf canonical form `canonForm` is a genuine
relabelling of the input adjacency: it equals `labelledAdj π adj` for the rank permutation of the leaf's
warm-refined discrete colouring. Proof: the lex-min `canonForm` is `canonAdj σ` for some `σ`
(`canonForm_mem_image`), and `SpineChain.canonAdj` is *definitionally* `labelledAdj (rankPerm …) adj`. This
is ①a at the value level — no `Option`, no leaf-extraction, reusable regardless of the runtime wrapper. -/
theorem canonForm_isLabelledAdj {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    [Nonempty (DirAssignment P₀ chain.D)] :
    ∃ π : Equiv.Perm (Fin n), canonForm chain isLeaf = labelledAdj π adj := by
  obtain ⟨σ, hσ⟩ := canonForm_mem_image chain isLeaf
  exact ⟨_, hσ⟩

/-! ## The runtime wrapper — extract the leaf, emit `some (canonForm …)`, discharge soundness -/

/-- The leaf level reached by the default descent (classical choice from `defaultSpineChain_reaches_leaf`).
`noncomputable` — the existence proof is `∃`, extracted by `Classical.choose`. -/
noncomputable def leafLevel (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel) : Nat :=
  (defaultSpineChain_reaches_leaf adj P₀ χι₀ hcell hne).choose

/-- The level-`leafLevel` default chain is a leaf (the `choose_spec` payload). -/
theorem leafLevel_isLeaf (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel) :
    (defaultSpineChain adj P₀ χι₀ sel (leafLevel adj P₀ χι₀ hcell hne)).IsLeaf :=
  (defaultSpineChain_reaches_leaf adj P₀ χι₀ hcell hne).choose_spec.2

/-- **The spine-level `canonForm?`.** Descend to the leaf `defaultSpineChain` reaches, and emit
`some (canonForm at that leaf)` — the lex-min canonical adjacency. Never flags (the flag is the budget
cap of the cost model; ①a is only the `some` case). `P₀` antisymmetric witnesses `Nonempty (DirAssignment …)`
(via `DirAssignment.default`), needed for the lex-min. -/
noncomputable def canonForm? (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hP₀ : PMatrix.Antisymmetric P₀) : Option (Fin n → Fin n → Nat) :=
  haveI : Nonempty (DirAssignment P₀
      (defaultSpineChain adj P₀ χι₀ sel (leafLevel adj P₀ χι₀ hcell hne)).D) :=
    ⟨DirAssignment.default hP₀⟩
  some (canonForm (defaultSpineChain adj P₀ χι₀ sel (leafLevel adj P₀ χι₀ hcell hne))
    (leafLevel_isLeaf adj P₀ χι₀ hcell hne))

/-- **①a `canon_sound` on the real spine.** When `canonForm?` answers `some cG`, `cG` is a genuine
relabelling of the input `adj` — the `Publication.canon_sound` obligation, discharged against the actual
descent (not the `opaque` stub). Composes the leaf-extraction wrapper with the value-level content
`canonForm_isLabelledAdj`. -/
theorem canonForm?_sound (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hP₀ : PMatrix.Antisymmetric P₀)
    (cG : Fin n → Fin n → Nat)
    (h : canonForm? adj P₀ χι₀ sel hcell hne hP₀ = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  haveI : Nonempty (DirAssignment P₀
      (defaultSpineChain adj P₀ χι₀ sel (leafLevel adj P₀ χι₀ hcell hne)).D) :=
    ⟨DirAssignment.default hP₀⟩
  have hcG : cG = canonForm (defaultSpineChain adj P₀ χι₀ sel (leafLevel adj P₀ χι₀ hcell hne))
      (leafLevel_isLeaf adj P₀ χι₀ hcell hne) := by
    have h' := h
    unfold canonForm? at h'
    exact (Option.some.inj h').symm
  rw [hcG]
  exact canonForm_isLabelledAdj _ _

/-! ## Closing the carried parameters — a fully parameter-free `AdjMatrix n → Option` canonizer

The wrapper above carries `(P₀, χι₀, sel)` + `hcell/hne/hP₀`. This section discharges all three by fixing
canonical choices, yielding `canonFormOf : AdjMatrix n → Option (…)` (the exact `Publication.canonForm?`
shape) and `canonFormOf_sound` (the exact `canon_sound` shape). `P₀`/`χι₀` are trivial; the selector is the
one carried piece with content, and its `PartitionInvariant`-compatible choice is deliberate (does not block
the ①c iso-invariance argument later). -/

/-- The trivial initial P-matrix: no order decisions (`unknown` everywhere), antisymmetric since
`POE.neg unknown = unknown`. The canonical descent seed. -/
def defaultP₀ : PMatrix n := fun _ _ => POE.unknown

theorem defaultP₀_antisym : PMatrix.Antisymmetric (defaultP₀ (n := n)) := fun _ _ => rfl

/-- The trivial initial colouring: all vertices one colour; `warmRefine` then splits by adjacency. No
predicate is carried on `χι₀`, so any fixed choice is canonical. -/
def defaultχι₀ : Colouring n := fun _ => 0

/-- **The canonical target selector: the whole non-discrete part** — every vertex that shares its colour
with some other vertex. It is `PartitionInvariant` (the condition is pure partition data — the property the
spine's cross-branch sharing needs, and what a raw-colour-min rule would *fail*, ChainDescent.lean §968),
and it trivially `TargetsNonsingletonCell` + is `NonemptyOnNonDiscrete`. It over-individualizes (the descent
reaches a leaf fast, not minimally) — a ② *efficiency* matter, irrelevant to ①a soundness; a single-cell
refinement is the ② selector, and `canonForm_isLabelledAdj` is selector-agnostic so ①a transfers to it. -/
def nonDiscreteSel (χ : Colouring n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ u, u ≠ v ∧ χ u = χ v)

theorem nonDiscreteSel_targets : TargetsNonsingletonCell (nonDiscreteSel (n := n)) := by
  intro χ v hv
  simpa [nonDiscreteSel] using hv

theorem nonDiscreteSel_nonempty : NonemptyOnNonDiscrete (nonDiscreteSel (n := n)) := by
  intro χ hχ
  unfold Discrete at hχ
  push Not at hχ
  obtain ⟨i, j, hχij, hne⟩ := hχ
  apply Finset.nonempty_iff_ne_empty.mp
  refine ⟨i, ?_⟩
  simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, (Ne.symm hne), hχij.symm⟩

/-- **The parameter-free spine canonizer** — `AdjMatrix n → Option (…)`, the exact `Publication.canonForm?`
shape (a function of `G` alone), with the descent parameters fixed to their canonical choices. -/
noncomputable def canonFormOf (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  canonForm? adj defaultP₀ defaultχι₀ nonDiscreteSel
    nonDiscreteSel_targets nonDiscreteSel_nonempty defaultP₀_antisym

/-- **①a `canon_sound`, fully parameter-free.** The exact `Publication.canon_sound` shape against the
concrete `canonFormOf`: a `some cG` answer is a genuine relabelling of `G`. All carried pieces discharged. -/
theorem canonFormOf_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonFormOf adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj :=
  canonForm?_sound adj defaultP₀ defaultχι₀ nonDiscreteSel
    nonDiscreteSel_targets nonDiscreteSel_nonempty defaultP₀_antisym cG h

/-- `canonFormOf` always answers `some` — it emits the leaf canonical form and never flags (flagging is the
cost-model cap, added over this by the shared object). Lets the capped wrapper prove `flag ↔ budget-exhausted`. -/
theorem canonFormOf_isSome (adj : AdjMatrix n) : (canonFormOf adj).isSome = true := rfl

end ChainDescent.CanonSound

/- ═══════════════════════════ (was ScratchCanonFormCapped.lean) ═══════════════════════════ -/


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
