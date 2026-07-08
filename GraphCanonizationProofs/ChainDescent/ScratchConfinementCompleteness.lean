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
  - **(X3) the partition→canonical lift — the genuine open piece, DEEPER than a `samePartition` lemma
    (correction 2026-07-08).** (X1)/(X2) deliver only **`samePartition`** of the reached leaves, not a literal
    colour relabel, because `individualizedColouring n S v = if v ∈ S then v.val+1 else 0` is **index-based**: a
    transport `g` moves the pinned-vertex colour *values* (`v.val+1` vs `(g v).val+1`) while preserving the
    partition. **`samePartition` is INSUFFICIENT to close X3** — it is *trivially* true at every discrete leaf (all
    singletons are `samePartition`), yet distinct discrete colourings give distinct `canonForm` (different orderings
    ⟹ different `rankPerm` ⟹ different relabel). So "`samePartition ⟹ equal canonForm`" is **false**; the real open
    content is that the lex-min-over-`DirAssignment` `canonForm` is invariant under the specific `g`-relabel-with-
    index-shift the transport produces. What IS landed is the **literal**-relabel value lift
    (`NodeCountBridge.labelledAdj_rankPerm_transport`: an automorphism relabel is invisible at the labelled level);
    the gap is precisely the index-shift between "`samePartition` via transport" and "literal relabel". Closing it is
    a **§15.7 `canonForm`/individualization design** question — either make `individualizedColouring` `g`-equivariant
    (a canonical, non-index seed) so transport gives a *literal* relabel and `labelledAdj_rankPerm_transport`
    applies, or prove the lex-min absorbs the index-shift. Pinned below as `CanonPartitionInvariant` (the honest →
    target, NOT the false `samePartition` form).
  - **(X4) assembly** — compose (X1)+(X2)+(X3) into `Iso G H → canonForm? G = canonForm? H` (⟹ `cG = cH`).

So **①b = {← LANDED} + {→ = the genuine (X3) canonForm-design piece + its assembly}**, with (X1)/(X2)'s
partition-level substrate and the *literal*-relabel value lift already banked. The remaining mathematical content is
(X3): make the descent's canonical invariant under the transport `g` despite index-based individualization.

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

end ChainDescent.ConfinementCompleteness
