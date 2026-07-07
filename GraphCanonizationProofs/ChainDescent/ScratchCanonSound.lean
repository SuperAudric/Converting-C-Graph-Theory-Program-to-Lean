/-
# ScratchCanonSound.lean — ①a `canon_sound` discharged on the REAL spine (WIP, NOT in build.sh)

**The first `Publication.lean` obligation crossed into the real runtime.** `Publication.lean` states
`canon_sound`: whenever the canonizer answers `some cG`, that `cG` is a genuine relabelling of the input
(`∃ π, cG = labelledAdj π G`). Today `Publication.canonForm?` is `opaque … := none`, so the obligation is a
`sorry`. This module *defines* a real spine-level `canonForm?` off `defaultSpineChain` and proves the
soundness obligation against it — turning ①a from a stub into a proof, and connecting the runtime object to
the descent substrate (the "value-side IS descended" direction of the cost/runtime co-development).

**Two pieces.**
  · `canonForm_isLabelledAdj` — the soundness CONTENT, at the value level: the spine's leaf lex-min
    `canonForm` equals `labelledAdj π adj`. It is *definitional* — `SpineChain.canonAdj` is literally
    `labelledAdj (rankPerm …) adj`, and the lex-min `canonForm` is one of those `canonAdj` images
    (`canonForm_mem_image`). Independent of how the runtime extracts the leaf / wraps `Option`.
  · `canonForm?` + `canonForm?_sound` — the runtime wrapper: extract the leaf reached by the default descent
    (`defaultSpineChain_reaches_leaf`, classical choice), emit `some (canonForm at that leaf)`, and discharge
    the `canon_sound` shape. This `canonForm?` never flags — flagging is the *cost* side (the budget cap of
    `ScratchCostModelPerNode`); ①a is only about the `some` case, so soundness is complete here.

**Remaining wiring to Publication (noted, not this increment).** `Publication.canonForm?` takes only `(n, G)`;
this one carries the descent parameters `(P₀, χι₀, sel)` + their well-formedness (`hcell`, `hne`, `hP₀`).
Replacing the opaque = fixing canonical choices of those parameters from `G` and discharging the three
hypotheses for them. The soundness *content* proved here is reused verbatim.

Axiom target `[propext, Classical.choice, Quot.sound]` (uses `Classical.choose` for leaf extraction).
Imports the Mathlib spine — slower compiles. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.Spine

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

end ChainDescent.CanonSound
