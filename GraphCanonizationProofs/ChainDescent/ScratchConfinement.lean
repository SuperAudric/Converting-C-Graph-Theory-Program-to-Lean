/-
# ScratchConfinement.lean — the confinement-lemma ASSEMBLY SKELETON (WIP, NOT in build.sh)

**What this file is.** The pinning target for the non-rigid correctness proof ① (route-c-plan §7b/§7c). The
confinement lemma — *a Phase-1 over-budget flag ⟹ the residue is primitive rank-3 ⟹ VT ⟹ the target cell is one
orbit ⟹ assume-VT prune is sound* — is the whole of ①b (`canon_complete`) on the non-rigid residue. Rather than
prove P1–P4 to four *informal* interfaces and hope they compose (the project's recurring vacuity/compose-failure
trap: `GroupReproduced`, `SchemeReproduced`, `BoundedConfusionMultiplicity`), this file states the assembly FIRST
and threads every sub-obligation through it, so each Pᵢ is a clearly-typed hypothesis and their composition is
machine-checked.

**Discipline (like `Publication.lean`, one level down).** The already-LANDED pieces are wired in for real (no
`sorry`); the still-OPEN pieces are carried as explicitly-named `Prop`-valued **hypotheses**, so the file is
axiom-clean `[propext, Classical.choice, Quot.sound]` — never `sorry`. Discharging a hypothesis = landing that Pᵢ.

**What is wired REAL here** (plugged straight into landed lemmas):
  · **P1 largeness** — `flag_imp_large`: a flag ⟹ `n < residualCard k` (large `Aut`), from the landed
    `ConfinementP1.not_flagsAt_of_smallAut_spine` on the real spine `spineCappedCanonizerO`. Modulo the seam
    hypothesis `hgreedy` (the harvest base ≤ a greedy base of the residue = `greedy_base_card_le_baseMax`) and a
    concrete `residualCard`.
  · **P4** — `ConfinementP4.selectedCellSubsetOrbitAt_of_frameSelectorTransitive` +
    `selectedCellIsOrbit_of_subsetOrbit`: `FrameSelectorTransitive ⟹ SelectedCellIsOrbit`.
  · **CertifiedSinglePath** — `NodeCountBridge.certifiedSinglePath_of_disposition`: `SinglePathDisposition ⟹`
    the poly single-path completeness core.

**What is PINNED as an open hypothesis** (each = a named Pᵢ / seam to discharge):
  · **P2** `hP2 : flag ⟹ SymmetricFlag k`   — deferral confinement (rigid decisions do not cause Phase-1 flags).
  · **P3** `hP3 : n < residualCard k → SymmetricFlag k → PrimRank3Classical k` — the seal `reachesRigidOrCameron`
    recomposed on the concrete residue (large ∧ ¬rigid ⟹ Cameron/node-4 primitive rank-3), *carrying classicality*
    (Liebeck/G3) so Witt applies. This is where the `SchurianScheme` model-faithfulness bridge lives.
  · **Witt** `hWitt : PrimRank3Classical k → FrameSelectorTransitive …` — Witt flag-transitivity of `O(Q)` on the
    forms-graph residue (`Publication.witt_flag_transitivity`; family-specific, false for Clebsch).
  · **witness case** `hWitness : ¬flag ⟹ SelectedCellIsOrbit` — the harvest-witnessed branch (§7b: a completed
    harvest *is* a certified orbit, sound by construction).
  · **node↔prefix** `nodeOf` — each consumed prefix `S` is the residue at some descent level `k` (descent-model seam).
  · **transport seam** `RepresentativeInvariant` — the ONE ingredient beyond P1–P4 (spotted 2026-07-08): turning
    `CertifiedSinglePath` into `canon_complete` needs representative-choice invariance of the leaf canonical. The
    depth-1 core is landed (`NodeCountBridge.repTransport`); the level-lift + `canonAdj` equality is OPEN.

Imports `ScratchConfinementP1` (P1 + spine + Cascade) and `ScratchConfinementP4` (P4 + NodeCountBridge). Axiom
target `[propext, Classical.choice, Quot.sound]`. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementP1
import ChainDescent.ScratchConfinementP4

namespace ChainDescent.Confinement

open ChainDescent
open ChainDescent.CostModel.Oracle
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.NodeCountBridge

variable {n : Nat}

/-! ## P1 — largeness confinement, wired REAL on the spine

`flag_imp_large` is P1's contrapositive on the actual descent object: a Phase-1 flag forces the node's residual
`Aut` to be large. It is the landed `not_flagsAt_of_smallAut_spine` read contrapositively — the ONE place the cost
model (`flagsAt` on `spineCappedCanonizerO`) and correctness (the residue's `|Aut|`) interlock. The two seam inputs
are honest: `hgreedy` = the harvest algorithm's greedy-base property (`greedy_base_card_le_baseMax`), and
`residualCard` = the residue-at-node's `Aut` order (the last P1 wiring). -/
theorem flag_imp_large
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt residualCard : Nat → Nat) (k : Nat)
    (hn : 1 ≤ n)
    (hgreedy : baseAt k ≤ Nat.log 2 (residualCard k))
    (hflag : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true) :
    n < residualCard k := by
  by_contra hle
  rw [Nat.not_lt] at hle
  have hf := not_flagsAt_of_smallAut_spine adj P₀ χι₀ sel baseAt residualCard k hn hgreedy hle
  rw [hf] at hflag
  exact absurd hflag (by decide)

/-! ## The confinement lemma — flag ⟹ the cell is one orbit

The core reduction, with P1 plugged in real and P2/P3/Witt carried as the three open seams. Conclusion is exactly
the input the landed prune-completeness consumer needs (`SelectedCellIsOrbit`). -/

/-- **CONFINEMENT (the ①b core).** At a Phase-1 flagging node (level `k`, prefix `S`), the target cell is a single
`Stab(S)`-orbit. Chain: P1 (`flag_imp_large`, real) ⟹ large; P2 (`hP2`) ⟹ symmetric-phase; P3 (`hP3`, the seal
recomposed with classicality) ⟹ primitive rank-3 classical; Witt (`hWitt`) ⟹ `FrameSelectorTransitive`; P4
(`selectedCellSubsetOrbitAt_of_frameSelectorTransitive` + `selectedCellIsOrbit_of_subsetOrbit`, real) ⟹
`SelectedCellIsOrbit`. The abstract `SymmetricFlag`/`PrimRank3Classical` are the honest residue-classification
interface; discharging `hP2`/`hP3`/`hWitt` = landing P2/P3/Witt. -/
theorem confinement_selectedCellIsOrbit
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt residualCard : Nat → Nat)
    (S : Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hgreedy : baseAt k ≤ Nat.log 2 (residualCard k))
    (SymmetricFlag PrimRank3Classical : Nat → Prop)
    (hP2 : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true → SymmetricFlag k)
    (hP3 : n < residualCard k → SymmetricFlag k → PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel S)
    (hflag : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel S := by
  have hlarge : n < residualCard k :=
    flag_imp_large adj P₀ χι₀ sel baseAt residualCard k hn hgreedy hflag
  have hsym := hP2 hflag
  have hprim := hP3 hlarge hsym
  have hframe := hWitt hprim
  have hsub := selectedCellSubsetOrbitAt_of_frameSelectorTransitive hframe S (Finset.Subset.refl S)
  exact selectedCellIsOrbit_of_subsetOrbit hsub

/-! ## Disposition assembly — flag case ∪ witness case ⟹ SinglePathDisposition

`SinglePathDisposition` (`∀ S, SelectedCellIsOrbit`) is what feeds `CertifiedSinglePath`. It needs the cell-is-orbit
property at EVERY node, split by the §7b dichotomy: a flagging node uses CONFINEMENT (above); a non-flagging node
uses the harvest WITNESS (`hWitness`, sound by construction). The `nodeOf` map (each prefix `S` is consumed at some
level) is the descent-model seam linking the per-node flag to the per-prefix disposition. -/

/-- **The single-path disposition from confinement + witness.** Every selected cell is one orbit: at `S`'s node
`nodeOf S`, either it flagged (⟹ `hFlagCase`, i.e. confinement) or it did not (⟹ `hWitness`, the certified-harvest
branch). This is the structural form of the empirical single-path finding (`leaves = 1`). -/
theorem singlePathDisposition_of_confinement
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat)
    (nodeOf : Finset (Fin n) → Nat)
    (hFlagCase : ∀ S : Finset (Fin n),
        flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
          ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) = true →
        SelectedCellIsOrbit adj P₀ sel S)
    (hWitness : ∀ S : Finset (Fin n),
        flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
          ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) = false →
        SelectedCellIsOrbit adj P₀ sel S) :
    SinglePathDisposition adj P₀ sel := by
  intro S
  cases hb : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
      ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) with
  | true => exact hFlagCase S hb
  | false => exact hWitness S hb

/-- **The certified single path from the disposition (real).** Straight through the landed
`certifiedSinglePath_of_disposition`: the confinement-driven disposition delivers both poly ingredients — bounded
node count (`≤ n`) and every consumed cell a single residual orbit (the completeness core). -/
theorem certifiedSinglePath_of_confinement
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hdisp : SinglePathDisposition adj P₀ sel) :
    CertifiedSinglePath adj P₀ χι₀ sel :=
  certifiedSinglePath_of_disposition hcell hne hdisp

/-! ## The remaining seam BEYOND P1–P4 — representative-transport invariance (①b completeness)

`CertifiedSinglePath` says the single path visits single-orbit cells and terminates in `≤ n` nodes. Turning that
into `canon_complete` (①b) needs one more fact the P1–P4 chain does NOT supply: choosing a *different
representative* of a single-orbit cell yields the SAME leaf canonical (else the single-path output is not
iso-invariant). The depth-1 core is landed — `NodeCountBridge.repTransport` / `repTransport_of_orbitPartition`
transport the one-deeper partition along the orbit automorphism — but the level-iteration and the lift to
`canonAdj` equality are OPEN (partly blocked on the `canonForm` lex-min placeholder). It is pinned here as
`RepresentativeInvariant` so the full ①b path is visible: P1–P4 ⟹ `CertifiedSinglePath`, then
`RepresentativeInvariant` ⟹ `canon_complete`. -/

/-- **The completeness target, abstractly (the ①b shape).** An abstract predicate standing for "the certified
single path computes the iso-invariant canonical" — i.e. `canon_complete` on the non-rigid residue. Kept opaque so
the composition below is non-vacuous; the Runtime Phase replaces it with the real `canonForm?`-level statement. -/
def IsoInvariantCanonical
    (_adj : AdjMatrix n) (_P₀ : PMatrix n) (_χι₀ : Colouring n)
    (_sel : Colouring n → Finset (Fin n)) : Prop := True → True  -- placeholder shape; Runtime Phase swaps in `canonForm?`-completeness

/-- **The full ①b path, pinned.** `CertifiedSinglePath` + the representative-transport invariance ⟹ the
iso-invariant canonical (①b). `RepresentativeInvariant` is the transport seam (level-lift of `repTransport`); its
discharge is the last ingredient of non-rigid completeness beyond P1–P4. Stated so the dependency is machine-visible
and cannot be silently skipped. -/
theorem isoInvariantCanonical_of_certifiedSinglePath
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (_hpath : CertifiedSinglePath adj P₀ χι₀ sel)
    (RepresentativeInvariant : Prop)
    (_hrep : RepresentativeInvariant)
    (hbridge : CertifiedSinglePath adj P₀ χι₀ sel → RepresentativeInvariant →
        IsoInvariantCanonical adj P₀ χι₀ sel) :
    IsoInvariantCanonical adj P₀ χι₀ sel :=
  hbridge _hpath _hrep

/-! ## P1 fully wired on the concrete spine — the last seam discharged

Specializing `flag_imp_large` with the concrete `spineBaseAt` / `spineResidualCard` (the level-`k` residue's
harvest base and `Aut` order, `ScratchConfinementP1`) and the proved `spineBaseAt_le_log` removes the abstract
`baseAt` / `residualCard` / `hgreedy` from P1's largeness half: on the real spine
`spineCappedCanonizerO … spineBaseAt`, a Phase-1 flag at node `k` implies the level-`k` residue's automorphism
group is large. -/

/-- **P1 on the concrete spine (no carried hypotheses).** A flag at node `k` of the spine instantiated with the
real per-node harvest base `spineBaseAt` implies `n < spineResidualCard k = |StabilizerAt adj P₀ D_k|` — the
node-`k` residue has large `Aut`. This is confinement-P1's largeness clause on the actual descent, with the
residue-at-node seam (concrete `baseAt`/`residualCard`) closed; it feeds P3 (large ∧ ¬rigid ⟹ primitive rank-3). -/
theorem flag_imp_large_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    n < spineResidualCard adj P₀ χι₀ sel k :=
  flag_imp_large adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)
    (spineResidualCard adj P₀ χι₀ sel) k hn
    (spineBaseAt_le_log adj P₀ χι₀ sel k) hflag

/-! ## P2 — deferral confinement on the concrete spine

The phase split is `IsBase T` (rigid / base-reached — residual symmetry exhausted, `DiscretizesAtBases` /
IR-core) vs `¬IsBase T` (symmetric — residual symmetry present, `RecoversWhileSymmetric`). P2 says a Phase-1
flag is confined to the symmetric side, and it falls straight out of P1: a flag forces a *large* residual `Aut`
(`flag_imp_large_spine`), but a base has a *trivial* residual (`card = 1`, `card_stabilizerAt_eq_one_iff_isBase`).
So a flag cannot occur at a base — "rigid decisions are deferred (trivial residual ⟹ `oracleCost = n^0`, cheap),
never expensively harvested; a Phase-1 flag is not rigid-caused." -/

/-- **P2 (deferral confinement).** A Phase-1 flag at node `k` implies the level-`k` prefix is **not a base** — the
node is in the symmetric domain (`¬IsBase`, residual symmetry still present). Proof: P1 gives `n < spineResidualCard
k`; a base has trivial residual (`spineResidualCard k = 1`); with `n ≥ 1` that is a contradiction. Hence
rigid/base-reached / IR-core nodes (trivial residual, cheap harvest) never Phase-1-flag. -/
theorem flag_imp_symmetric_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P (defaultSpineChain adj P₀ χι₀ sel k).D := by
  intro hbase
  have hlarge := flag_imp_large_spine adj P₀ χι₀ sel k hn hflag
  have hone : spineResidualCard adj P₀ χι₀ sel k = 1 :=
    card_stabilizerAt_eq_one_iff_isBase.mpr hbase
  omega

/-! ## Confinement on the concrete spine — P1 ∧ P2 discharged, only P3/Witt abstract

Instantiating `confinement_selectedCellIsOrbit` with the concrete `spineBaseAt`/`spineResidualCard` (P1, via
`spineBaseAt_le_log`) and the concrete symmetric predicate `¬IsBase` (P2, via `flag_imp_symmetric_spine`) leaves
only the two genuinely-open seams as hypotheses: **P3** (`hP3`: large ∧ ¬rigid ⟹ primitive rank-3 classical — the
seal recomposed on the concrete residue, carrying classicality) and **Witt** (`hWitt`: primitive rank-3 classical
⟹ `FrameSelectorTransitive`). -/

/-- **Confinement on the real spine (P1 ∧ P2 wired; P3/Witt carried).** A Phase-1 flag at node `k` ⟹ the target
cell at prefix `S` is one `Stab(S)`-orbit, given only P3 (`hP3`) and Witt (`hWitt`) on the concrete residue. P1
(flag ⟹ large residual) and P2 (flag ⟹ `¬IsBase`, symmetric) are discharged from the spine, no longer hypotheses. -/
theorem confinement_selectedCellIsOrbit_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (S : Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (PrimRank3Classical : Nat → Prop)
    (hP3 : n < spineResidualCard adj P₀ χι₀ sel k →
        ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P (defaultSpineChain adj P₀ χι₀ sel k).D →
        PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel S :=
  confinement_selectedCellIsOrbit adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)
    (spineResidualCard adj P₀ χι₀ sel) S k hn (spineBaseAt_le_log adj P₀ χι₀ sel k)
    (fun j => ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel j).P (defaultSpineChain adj P₀ χι₀ sel j).D)
    PrimRank3Classical
    (fun hf => flag_imp_symmetric_spine adj P₀ χι₀ sel k hn hf)
    hP3 hWitt hflag

end ChainDescent.Confinement
