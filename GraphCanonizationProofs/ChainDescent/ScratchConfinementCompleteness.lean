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
  - **(X3) the partition→canonical lift — THE ONE OPEN LEMMA.** (X1)/(X2) both deliver **`samePartition`**, not a
    literal colour relabel, because `individualizedColouring` is index-based (`g` moves colour *values* while
    preserving the partition). `canonForm` reads colour values (`rankPerm`∘`vertexRank`), so the bridge needs
    **`samePartition χ χ' → canonForm(χ) = canonForm(χ')`** — i.e. the lex-min-over-`DirAssignment` canonical
    depends only on the partition + graph. The value-level half is LANDED
    (`NodeCountBridge.labelledAdj_rankPerm_transport`: a literal automorphism relabel is invisible at the labelled
    level); the open content is that the lex-min `canonForm` *is* partition-invariant (the §15.7 `canonForm`
    design). Pinned below as `CanonPartitionInvariant`.
  - **(X4) assembly** — compose (X1)+(X2)+(X3) into `Iso G H → canonForm? G = canonForm? H` (⟹ `cG = cH`).

So **①b = {← LANDED} + {→ modulo the single open lemma (X3) + its assembly}**, with (X1)/(X2)'s partition-level
substrate already banked. The remaining mathematical content is exactly (X3): `canonForm` is partition-invariant.

Imports `ScratchCanonFormCapped` (the shared `canonForm?` + ①a `canonForm?_sound`). Axiom target `[propext,
Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchCanonFormCapped

namespace ChainDescent.ConfinementCompleteness

open ChainDescent

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

/-! ## The → direction — pinned to the one open lemma (X3)

`CanonPartitionInvariant` is the open content: the descent's canonical form depends only on the leaf *partition*
(not the colour values), so partition-equal descents — which (X1) cross-graph and (X2) representative-choice both
produce — yield equal canonicals. Kept as a `Prop` so the → assembly's dependency on it is explicit and it is not
silently assumed. Discharging it is the §15.7 `canonForm` job (the value-level half is landed:
`NodeCountBridge.labelledAdj_rankPerm_transport`). -/

/-- **The open lemma (X3): the canonizer's output is partition-invariant.** Abstractly: whenever two inputs' single
paths reach leaves with the same partition, the canonical forms coincide. Concretely it is
`samePartition χ χ' → canonForm(χ) = canonForm(χ')` for the lex-min-over-`DirAssignment` `canonForm`; here as a
`Prop` placeholder for the § 15.7 canonForm design. The → direction of ①b is `(X1) ∧ (X2) ∧ CanonPartitionInvariant`. -/
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

end ChainDescent.ConfinementCompleteness
