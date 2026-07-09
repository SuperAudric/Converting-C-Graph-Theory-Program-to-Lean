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
  - **(X3) the partition→canonical lift — ROUTE IS `ScratchConfinementX3.lean` (THE INDEX-FREE CUT). The lex-min
    reduction below is SUPERSEDED (its residual is FALSE).** History (three dead routes): "samePartition ⟹ equal
    canonForm" is FALSE; "make `individualizedColouring` `g`-equivariant" is a 14-module ripple; and **"the lex-min
    washes out the index" is ALSO FALSE** — `DirAssignment` `σ` breaks ties only between *equal-colour* vertices, but
    individualization gives committed vertices *distinct index colours* (`v.val`), so `σ` never re-orders them ⟹ the
    lex-min cannot remove the baked-in index order ⟹ the current `canonForm` is genuinely not iso-invariant when
    `D ≠ ∅`, and `CanonFormImagesIsoInvariant` (defined below over that `canonForm`) is a **false** residual. **THE
    LIVE ROUTE = the index-free cut** (`ScratchConfinementX3.lean`): commit ONE vertex at a time with an index-free
    colour, ordering the committed set by descent *level* (not `v.val`), so the seed transports **literally** and the
    banked value-lift closes X3. P1–P6 landed axiom-clean there; sole remaining proof = `hrec` (confinement
    `SelectedCellIsOrbit` ⟹ the reconciling automorphism). The lex-min lemmas below (`min'_eq_of_eq`,
    `canonForm_eq_of_canonFormImages_eq`, `canonForm?_eq_dCanonForm`, `canonPartitionInvariant_of_imagesIsoInvariant`)
    are TRUE as stated and kept as a record, but they reduce ①b→ to a false target, so they are **not** the path.
  - **(X4) assembly** — in `ScratchConfinementX3.lean` (`ifCanon_iso_invariant_of_reconcile`), modulo `hrec`.

So **①b = {← LANDED} + {→ = the index-free cut, `ScratchConfinementX3.lean`, modulo `hrec`}**. The reduction section
below is superseded scaffolding; see that file for the live route.

Imports `ScratchCanonFormCapped` (the shared `canonForm?` + ①a `canonForm?_sound`). Axiom target `[propext,
Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.CanonForm

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

/-- **The sharper → obligation over the CURRENT (index-based) `canonForm`.**
**⚠ SUPERSEDED — this predicate is FALSE (do not attempt to prove it).** The decisive finding (`ScratchConfinementX3`
header): `dChain` commits vertices with **distinct index-based colours** (`IndivStep.default = …+v.val…`), so committed
vertices have no ties, the `DirAssignment` lex-min cannot re-order them, and `canonFormImages` genuinely differs for
isomorphic inputs when `D ≠ ∅`. The lex-min reduction above (`canonForm_eq_of_canonFormImages_eq` etc.) is correct and
kept, but its residual is not provable *for this object*. The real ①b→ target is the **index-free single-vertex descent**
(`ScratchConfinementX3`): P1–P6 landed axiom-clean; iso-invariance is `ifCanon_iso_invariant_of_reconcile` modulo the
confinement reconciliation. Kept here only to document why this route was abandoned. -/
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

/-! ## X3 residual — scoping the genuine difficulty (2026-07-08, cont.)

**Finding (from attempting to close `CanonFormImagesIsoInvariant`): X3 is NOT a mechanical last-lemma; it is the real
§15.7 `canonForm`-design question, deeper than the reduction suggested.** Digging in surfaced three coupled facts:

1. **The descent colouring is index-based one level BELOW `individualizedColouring`.** `defaultColouring` iterates
   `IndivStep.default`, whose `χ'` is `if v ∈ T then 2*(χ v * n + v.val)+1 else 2*χ v` — an explicit `v.val`. So the
   whole descent colouring transports only up to `samePartition` (not literal) under a relabel, not just the seed.
2. **`canonForm` is level-dependent.** `canonAdj σ = labelledAdj (rankPerm (warmRefine σ.σ χ)) adj`, and `rankPerm`
   reads colour *values*; two `samePartition` (e.g. successive-leaf-level) descent colourings give different value
   orderings ⟹ different `rankPerm` ⟹ different `canonAdj`. Since `dLeaf` uses `Classical.choose`, `dLeaf G ≠ dLeaf H`
   is possible even for `G ≅ H`. ⟹ **a canonical (least, `Nat.find`) leaf level is required** so `dLeaf` transports
   exactly (via `IsLeaf` transport, which needs only `samePartition` + `Discrete.of_samePartition`).
3. **The `DirAssignment` lex-min mods out only the order on the committed set `D`, NOT the ambient index-order of the
   non-`D` vertices.** For a rigid residue (`D = ∅` at the leaf) `canonForm` IS iso-invariant (refinement colours are
   structural). The index leaks exactly when individualization is needed (`D ≠ ∅`), and whether the `DirAssignment`
   range is rich enough to wash out `IndivStep.default`'s index-tiebreak on `D` is the crux — and is currently open.

**So finishing X3 requires (in order):** (a) canonicalize the leaf level (least via `Nat.find`, `DecidablePred IsLeaf`
by `Classical.decPred`); (b) the cross-graph descent transport (`samePartition`-level — via `warmRefine_transport_iso`
+ the selector-equivariance below + the `IndivStep.default` `samePartition` transport), giving `IsLeaf` transport ⟹
`dLeaf` invariance + `defaultD H = (defaultD G).image π`; (c) the crux: `canonFormImages` iso-invariance, which reduces
to whether the `DirAssignment` lex-min washes out the index-tiebreak on `D` — the genuine §15.7 open piece (may force a
`canonForm` redesign: a lex-min over a richer order set that stays poly). This is a real design problem, not assembly.

The one brick below is true and reusable regardless of how (c) resolves. -/

/-- **`nonDiscreteSel` is relabel-equivariant** — `nonDiscreteSel (χ ∘ π.symm) = (nonDiscreteSel χ).image π`. Pure
partition data commutes with relabelling; the selector piece of the (b) cross-graph descent-transport step. -/
theorem nonDiscreteSel_equivariant (χ : Colouring n) (π : Equiv.Perm (Fin n)) :
    nonDiscreteSel (fun v => χ (π.symm v)) = (nonDiscreteSel χ).image π := by
  ext w
  simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨u, hune, hueq⟩
    exact ⟨π.symm w, ⟨π.symm u, fun h => hune (π.symm.injective h), hueq⟩, by simp⟩
  · rintro ⟨v, ⟨u, hune, hueq⟩, rfl⟩
    refine ⟨π u, fun h => hune (π.injective h), ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hueq

end ChainDescent.ConfinementCompleteness
