/-
# ScratchConfinementCompleteness.lean — toward ①b `canon_complete` (WIP, NOT in build.sh)

**Context.** The confinement core (`ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt`) gives
`SelectedCellIsOrbit` at flagging nodes; with the witness case it yields `SinglePathDisposition` ⟹
`CertifiedSinglePath` — the single-path canonizer visits single-orbit cells and terminates in `≤ n` nodes. What
remains for **①b `canon_complete`** (`Iso G H ↔ cG = cH`, a complete iso-invariant) is the transport seam. This
module scopes ①b, lands the achievable **← direction**, and pins the one open lemma of the **→ direction**.

## Scoping — the pieces between here and a completed ①b

`canon_complete : Iso G H ↔ cG = cH` splits:

- **(←) `cG = cH → Iso G H`** — **LANDED here** (`canonForm?_complete_mpr`). Pure consequence of ①a soundness:
  each output is a relabelling of its input (`canonForm?_sound`), so equal outputs force the inputs isomorphic
  (`iso_of_labelledAdj_eq`). No transport needed.

- **(→) `Iso G H → cG = cH`** — the hard direction, = "the single-path canonizer is iso-invariant". Three pieces:
  - **(X1) cross-graph partition equivariance** — for `H = π·G`, the descent on `H` is the `π`-image of a descent
    on `G` (at the partition level). Substrate LANDED: the `RouteCTransport` `…_transport_iso` tower
    (`warmRefine_transport_iso` &c.).
  - **(X2) representative-choice invariance** — the single path *picks* a representative at each single-orbit cell;
    different picks must give the same canonical. Substrate LANDED at the partition level:
    `NodeCountBridge.baseTransport` (a global automorphism `g` carries the whole descent subtree) + the confinement
    single-orbit property (`SelectedCellIsOrbit`, this thread).
  - **(X3) the partition→canonical lift — CORRECTLY ROUTED 2026-07-08 (cont.): lex-min invariance of an iso-invariant
    image Finset. The two earlier framings below are both SUPERSEDED.** ~~"samePartition ⟹ equal canonForm"~~ is FALSE
    (trivially true at every discrete leaf, yet distinct discrete colourings give distinct `canonForm`); and
    ~~"make `individualizedColouring` `g`-equivariant"~~ is the WRONG fix — that seed is index-based *by design*, used
    across 14 modules incl. the sealed build (catastrophic ripple), AND **a lex-min needs no equivariant seed at all.**
    `canonForm = ofMatrixLex ((canonFormImages …).min' …)` = the lex-smallest `canonAdj` over all `DirAssignment`s; the
    lex-min of an **iso-invariant image Finset** is iso-invariant regardless of seed labelling (the index-based colour
    values wash out under the min). So X3 reduces — cleanly, LANDED below — to **`CanonFormImagesIsoInvariant`**:
    `G ≅ H ⟹ canonFormImages(descent G) = canonFormImages(descent H)` as Finsets, provable from the BANKED
    `Cascade.forcedNode_relabel` (selector equivariant under arbitrary relabel) + `RouteCTransport.warmRefine_transport_iso`
    (WL fixpoint transports cross-graph). `canonForm_eq_of_canonFormImages_eq` (the min'-of-equal-Finsets step) +
    `canonForm?_eq_dCanonForm` (the `canonForm?`→leaf `canonForm` bridge) + `canonPartitionInvariant_of_imagesIsoInvariant`
    are all landed axiom-clean. (X1)/(X2)'s transport substrate feeds the residual.
  - **(X4) assembly** — compose into `Iso G H → canonForm? G = canonForm? H` (⟹ `cG = cH`): DONE modulo X3 via
    `canonForm?_complete_of_imagesIsoInvariant`.

So **①b = {← LANDED} + {→ = `CanonFormImagesIsoInvariant` (a finite, structural residual)}**, with the min'-reduction,
the `canonForm?`→leaf bridge, and the (X1)/(X2) transport substrate all banked. The remaining mathematical content is
that ONE residual: the descent's candidate-matrix Finset is iso-invariant — no change to `individualizedColouring`.

Imports `ScratchCanonFormCapped` (the shared `canonForm?` + ①a `canonForm?_sound`). Axiom target `[propext,
Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchCanonFormCapped

namespace ChainDescent.ConfinementCompleteness

open ChainDescent
open ChainDescent.CanonSound
open ChainDescent.CanonForm

variable {n : Nat}

/-- **Graph isomorphism** (matching `Publication.Iso` unfolded): some relabelling of `G` is `H`. -/
def GraphIso (G H : AdjMatrix n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), labelledAdj π G = H.adj

/-! ## The ← direction — LANDED (from ①a soundness) -/

/-- **Two graphs with a common labelled image are isomorphic.** If `labelledAdj πG G = labelledAdj πH H` then `G`
and `H` are relabellings of one another (`π = (πH.trans πG.symm).symm`, i.e. `π.symm = πG.symm ∘ πH`). Pure
`Equiv.Perm` bookkeeping on `labelledAdj π adj i j = adj (π.symm i) (π.symm j)`. -/
theorem iso_of_labelledAdj_eq {G H : AdjMatrix n} {πG πH : Equiv.Perm (Fin n)}
    (h : labelledAdj πG G = labelledAdj πH H) :
    GraphIso G H := by
  refine ⟨(πH.trans πG.symm).symm, funext fun i => funext fun j => ?_⟩
  simp only [labelledAdj, Equiv.symm_symm, Equiv.trans_apply]
  have hEq := congrFun (congrFun h (πH i)) (πH j)
  simp only [labelledAdj, Equiv.symm_apply_apply] at hEq
  exact hEq

/-- **①b, the ← direction, on the real shared object.** If the canonizer answers on `G` and `H` with equal
canonical forms, the inputs are isomorphic. Discharged by ①a (`CanonForm.canonForm?_sound`: each output is a
relabelling of its input) + `iso_of_labelledAdj_eq`. This is the `canon_complete.mpr` half — the direction the
headline uses, and it needs no transport. -/
theorem canonForm?_complete_mpr {G H : AdjMatrix n} {cG cH : Fin n → Fin n → Nat}
    (hG : CanonForm.canonForm? G = some cG) (hH : CanonForm.canonForm? H = some cH)
    (hEq : cG = cH) :
    GraphIso G H := by
  obtain ⟨πG, hπG⟩ := CanonForm.canonForm?_sound G cG hG
  obtain ⟨πH, hπH⟩ := CanonForm.canonForm?_sound H cH hH
  exact iso_of_labelledAdj_eq (hπG.symm.trans (hEq.trans hπH))

/-! ## The → direction — pinned to (X3), the honest canonForm-design piece

`CanonPartitionInvariant` is the honest → target: the canonizer is iso-invariant (isomorphic inputs get equal
canonical forms). It is NOT the (false) `samePartition ⟹ equal canonForm`; the genuine open content (X3) is that
the lex-min `canonForm` survives the transport `g`-relabel despite index-based individualization (see the header
correction). Kept as a `Prop` so the → assembly's dependency is explicit. The value-level *literal*-relabel lift is
landed (`NodeCountBridge.labelledAdj_rankPerm_transport`); (X1)/(X2) supply the transport at the partition level. -/

/-- **The → obligation (X3 + assembly): the canonizer's output is iso-invariant.** Isomorphic inputs get equal
canonical forms. This is the honest `canon_complete.mp` target; its content is the (X3) canonForm-design piece
(make the descent's canonical invariant under the transport `g` — §15.7), fed by the banked (X1) cross-graph and
(X2) representative-choice transport substrate. Deliberately the *output-level* statement (not the false
`samePartition ⟹ equal canonForm`, which is refuted at discrete leaves). -/
def CanonPartitionInvariant : Prop :=
  ∀ (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
    GraphIso G H → CanonForm.canonForm? G = some cG → CanonForm.canonForm? H = some cH → cG = cH

/-- **①b assembled, modulo (X3).** With `CanonPartitionInvariant` (the open partition-invariance of `canonForm`, fed
by the landed (X1) cross-graph + (X2) representative-choice partition equivariance), the canonizer is a complete
iso-invariant: `Iso G H ↔ cG = cH`. The ← direction is `canonForm?_complete_mpr` (landed); the → direction is
exactly `CanonPartitionInvariant`. So ①b reduces to that one lemma. -/
theorem canonForm?_complete (hInv : CanonPartitionInvariant (n := n))
    {G H : AdjMatrix n} {cG cH : Fin n → Fin n → Nat}
    (hG : CanonForm.canonForm? G = some cG) (hH : CanonForm.canonForm? H = some cH) :
    GraphIso G H ↔ cG = cH :=
  ⟨fun hiso => hInv G H cG cH hiso hG hH, fun hEq => canonForm?_complete_mpr hG hH hEq⟩

/-! ## X3, CORRECTLY ROUTED — lex-min invariance of an iso-invariant image Finset

**Route correction (2026-07-08, cont.).** The prior pin — "make `individualizedColouring` `g`-equivariant so
transport is a *literal* relabel" — is the WRONG route: `individualizedColouring` is index-based *by design* and
used across 14 modules (incl. the sealed build), so changing it ripples catastrophically; and, more to the point,
**a lex-min does not need an equivariant seed.** `canonForm` is `ofMatrixLex ((canonFormImages …).min' …)` — the
lex-smallest `canonAdj` over all `DirAssignment`s. The lex-min of an **iso-invariant image Finset** is itself
iso-invariant *regardless of how the seed labels vertices*: two isomorphic graphs induce the SAME set of candidate
labelled matrices, and `min'` of a set depends only on the set. The index-based colour values wash out under the min.

So X3 reduces cleanly to **`CanonFormImagesIsoInvariant`**: `G ≅ H ⟹ canonFormImages(descent G) = canonFormImages(descent H)`
as Finsets of `MatrixLex n`. That residual is a *finite, structural* statement provable from the BANKED substrate —
`Cascade.forcedNode_relabel` (the descent's selector is equivariant under arbitrary relabelling — full cross-graph
iso-invariance of the individualization choice) + `RouteCTransport.warmRefine_transport_iso` (the WL fixpoint
transports cross-graph) — via the `canonAdj`-value / `DirAssignment`-bijection assembly. This subsection lands the
reduction (the min'-of-equal-Finsets step, graph-agnostic and true) and pins that one residual. -/

/-- **`min'` of equal Finsets agree** (proof-irrelevant in the nonempty witness). Pure `Finset` fact, via
`le_antisymm` on `min'_le` + `min'_mem`. The engine that lets an iso-invariant image set force an equal lex-min. -/
private theorem min'_eq_of_eq {α : Type*} [LinearOrder α] {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (h : s = t) :
    s.min' hs = t.min' ht := by
  apply le_antisymm
  · exact Finset.min'_le s (t.min' ht) (h ▸ Finset.min'_mem t ht)
  · exact Finset.min'_le t (s.min' hs) (h ▸ Finset.min'_mem s hs)

/-- **The lex-min reduction (graph-agnostic).** If two leaf descents — *on possibly different graphs* — have equal
`canonFormImages` Finsets, their `canonForm`s coincide. This is the whole "index-based seed washes out" content: the
canonical output is a function of the image *set* only. Immediate from `min'_eq_of_eq` under `ofMatrixLex`. -/
theorem canonForm_eq_of_canonFormImages_eq
    {adjG adjH : AdjMatrix n} {P₀G P₀H : PMatrix n} {χιG χιH : Colouring n}
    {selG selH : Colouring n → Finset (Fin n)} {kG kH : Nat}
    (chainG : SpineChain adjG P₀G χιG selG kG) (isLeafG : chainG.IsLeaf)
    (chainH : SpineChain adjH P₀H χιH selH kH) (isLeafH : chainH.IsLeaf)
    [Nonempty (DirAssignment P₀G chainG.D)] [Nonempty (DirAssignment P₀H chainH.D)]
    (h : canonFormImages chainG isLeafG = canonFormImages chainH isLeafH) :
    canonForm chainG isLeafG = canonForm chainH isLeafH := by
  unfold canonForm
  exact congrArg ofMatrixLex (min'_eq_of_eq _ _ h)

/-! ### Connecting `CanonForm.canonForm?` to the default-descent leaf `canonForm` -/

/-- The default descent's reached-leaf level under the canonical parameters (`defaultP₀`/`defaultχι₀`/`nonDiscreteSel`). -/
noncomputable def dLeaf (adj : AdjMatrix n) : Nat :=
  leafLevel adj defaultP₀ defaultχι₀ nonDiscreteSel_targets nonDiscreteSel_nonempty

/-- The default reference chain at its reached leaf. -/
noncomputable def dChain (adj : AdjMatrix n) :
    SpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel (dLeaf adj) :=
  defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel (dLeaf adj)

theorem dChain_isLeaf (adj : AdjMatrix n) : (dChain adj).IsLeaf :=
  leafLevel_isLeaf adj defaultP₀ defaultχι₀ nonDiscreteSel_targets nonDiscreteSel_nonempty

/-- The `DirAssignment` nonempty instance for the default leaf (from `defaultP₀` antisymmetry) — the SAME witness
`CanonSound.canonForm?` uses internally, so the `canonForm` values match definitionally. -/
noncomputable instance dChain_dirNonempty (adj : AdjMatrix n) :
    Nonempty (DirAssignment defaultP₀ (dChain adj).D) :=
  ⟨DirAssignment.default defaultP₀_antisym⟩

/-- The canonical leaf form of the default descent — the payload of `canonFormOf adj`. -/
noncomputable def dCanonForm (adj : AdjMatrix n) : Fin n → Fin n → Nat :=
  canonForm (dChain adj) (dChain_isLeaf adj)

/-- **Bridge: a `some cG` answer of the shared object IS the default-leaf `canonForm`.** Unfolds
`CanonForm.canonForm?` (the budget gate) → `canonFormOf` → `CanonSound.canonForm?`, all definitional, so `cG` is
exactly `dCanonForm adj`. -/
theorem canonForm?_eq_dCanonForm {adj : AdjMatrix n} {cG : Fin n → Fin n → Nat}
    (h : CanonForm.canonForm? adj = some cG) :
    cG = dCanonForm adj := by
  unfold CanonForm.canonForm? at h
  cases hr : CanonForm.descentResult adj with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some k =>
    rw [hr] at h
    have hval : canonFormOf adj = some (dCanonForm adj) := rfl
    rw [hval] at h
    exact (Option.some.inj h).symm

/-- **The sharper → obligation (X3 residual): the descent's `canonFormImages` is iso-invariant.** For `G ≅ H`, the
two default descents reach leaves whose candidate-matrix Finsets coincide. This is the ONE remaining piece — finite
and structural, provable from `forcedNode_relabel` + `warmRefine_transport_iso` (both BANKED), NOT from any change to
`individualizedColouring`. -/
def CanonFormImagesIsoInvariant : Prop :=
  ∀ (G H : AdjMatrix n), GraphIso G H →
    canonFormImages (dChain G) (dChain_isLeaf G) = canonFormImages (dChain H) (dChain_isLeaf H)

/-- **X3 reduced.** `CanonFormImagesIsoInvariant ⟹ CanonPartitionInvariant` — i.e. the honest → target follows from
the lex-min image-set invariance, via `canonForm_eq_of_canonFormImages_eq` + the `canonForm?`→`dCanonForm` bridge. So
**①b's → direction now reduces to `CanonFormImagesIsoInvariant`** (a finite structural statement), the correct
replacement for the refuted "samePartition ⟹ equal canonForm" / the mis-routed seed-equivariance pin. -/
theorem canonPartitionInvariant_of_imagesIsoInvariant
    (hImg : CanonFormImagesIsoInvariant (n := n)) :
    CanonPartitionInvariant (n := n) := by
  intro G H cG cH hiso hG hH
  rw [canonForm?_eq_dCanonForm hG, canonForm?_eq_dCanonForm hH]
  unfold dCanonForm
  exact canonForm_eq_of_canonFormImages_eq (dChain G) (dChain_isLeaf G)
    (dChain H) (dChain_isLeaf H) (hImg G H hiso)

/-- **①b assembled, modulo the sharper (X3) residual `CanonFormImagesIsoInvariant`.** Composes
`canonPartitionInvariant_of_imagesIsoInvariant` into `canonForm?_complete`: with the image-set invariance, the
canonizer is a complete iso-invariant. So `canon_complete` reduces to `CanonFormImagesIsoInvariant`. -/
theorem canonForm?_complete_of_imagesIsoInvariant
    (hImg : CanonFormImagesIsoInvariant (n := n))
    {G H : AdjMatrix n} {cG cH : Fin n → Fin n → Nat}
    (hG : CanonForm.canonForm? G = some cG) (hH : CanonForm.canonForm? H = some cH) :
    GraphIso G H ↔ cG = cH :=
  canonForm?_complete (canonPartitionInvariant_of_imagesIsoInvariant hImg) hG hH

end ChainDescent.ConfinementCompleteness
