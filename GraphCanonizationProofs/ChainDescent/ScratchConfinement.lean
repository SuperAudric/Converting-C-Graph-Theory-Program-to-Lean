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
`Stab(S)`-orbit. Chain: P1 (`hP1`) ⟹ `Large`; P2 (`hP2`) ⟹ `SymmetricFlag`; P3 (`hP3`, the seal recomposed with
classicality) ⟹ `PrimRank3Classical`; Witt (`hWitt`) ⟹ `FrameSelectorTransitive`; P4
(`selectedCellSubsetOrbitAt_of_frameSelectorTransitive` + `selectedCellIsOrbit_of_subsetOrbit`, real) ⟹
`SelectedCellIsOrbit`. Largeness is abstracted into `Large` + `hP1` — the concrete instantiation supplies the
*delivered* bound (`flag_imp_pow_baseMax_lt`: `2^(baseMax n) < residual`, super-poly), decoupling the assembly from
the threshold. The abstract `Large`/`SymmetricFlag`/`PrimRank3Classical` are the honest interface; discharging
`hP1`/`hP2`/`hP3`/`hWitt` = landing P1/P2/P3/Witt. -/
theorem confinement_selectedCellIsOrbit
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat)
    (S : Finset (Fin n)) (k : Nat)
    (Large SymmetricFlag PrimRank3Classical : Nat → Prop)
    (hP1 : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true → Large k)
    (hP2 : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true → SymmetricFlag k)
    (hP3 : Large k → SymmetricFlag k → PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel S)
    (hflag : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel S :=
  selectedCellIsOrbit_of_subsetOrbit
    (selectedCellSubsetOrbitAt_of_frameSelectorTransitive
      (hWitt (hP3 (hP1 hflag) (hP2 hflag))) S (Finset.Subset.refl S))

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
`RepresentativeInvariant` ⟹ `canon_complete`.

**★ SUPERSEDED (2026-07-08) — the real ①b lives in `ScratchConfinementCompleteness.lean`.** That module lands the
①b **← direction** (`canonForm?_complete_mpr`) and pins the → direction to the honest **X3** open lemma
(`CanonPartitionInvariant`; the `samePartition ⟹ equal canonForm` framing in the prose above turned out FALSE — X3
is a §15.7 `canonForm`/individualization design piece, see that file's header). The two placeholder decls below
(`IsoInvariantCanonical = True → True`, `isoInvariantCanonical_of_certifiedSinglePath`) are the earlier skeleton;
keep for the `CertifiedSinglePath` shape, but the authoritative ①b interface is `ScratchConfinementCompleteness`. -/

/-- **[SUPERSEDED placeholder — see `ScratchConfinementCompleteness` for the real ①b.]** An abstract predicate for
"the certified single path computes the iso-invariant canonical". Kept only for the skeleton shape below. -/
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

/-- **P1, the STRONG delivered bound (threshold-explicit largeness).** A Phase-1 flag at node `k` implies the
residual `Aut` exceeds `2^(baseMax n)` — the honest largeness the flag delivers, set by the threshold `baseMax n =
(log₂ n)²`, giving `2^(baseMax n) = n^{log₂ n}` (super-poly). **This is what makes the seal's super-poly
`IsLargeScheme` satisfiable** (P3's `hLargeBridge`); the weaker `flag_imp_large_spine` (`n < residual`) is a
corollary. Proof: the flag gives `oracleBudget n < oracleCost n (spineBaseAt k)` = `n^{baseMax n} < n^{spineBaseAt
k}` ⟹ (`n ≥ 2`) `baseMax n < spineBaseAt k ≤ log₂(residual)` ⟹ `2^{baseMax n} < 2^{log₂ residual} ≤ residual`. -/
theorem flag_imp_pow_baseMax_lt (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k := by
  have hiff := (spineCappedCanonizerO_flagsAt_iff adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) k).mp hflag
  simp only [oracleBudget, oracleCost] at hiff
  rw [Nat.pow_lt_pow_iff_right hn] at hiff
  have hlt : baseMax n < Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) :=
    lt_of_lt_of_le hiff (spineBaseAt_le_log adj P₀ χι₀ sel k)
  have hpos : 0 < spineResidualCard adj P₀ χι₀ sel k := card_stabilizerAt_pos
  calc 2 ^ baseMax n
      < 2 ^ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) :=
        (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hlt
    _ ≤ spineResidualCard adj P₀ χι₀ sel k := Nat.pow_log_le_self 2 hpos.ne'

/-- **Satisfiability / soundness: a residue with `|Aut| ≤ 2^(baseMax n)` does NOT flag.** The exact converse of
`flag_imp_pow_baseMax_lt` — only residues with super-poly `Aut` (`> 2^(baseMax n) = n^{log₂ n}`) flag. So every
**poly-`Aut`** residue (`|Aut| ≤ n^c ≤ 2^(baseMax n)` once `c ≤ log₂ n`) is below threshold and is NOT
assume-VT-pruned. This is precisely why the non-Schurian-SRG danger is excluded: a Chang graph
(`|Aut| = 384`, poly-bounded, non-VT) never Phase-1-flags, so it is never unsoundly pruned — the soundness the
threshold raise buys. Proof: `spineBaseAt k ≤ log₂(residual) ≤ log₂(2^{baseMax n}) = baseMax n` ⟹ not_flagsAt. -/
theorem not_flagsAt_of_residualCard_le_pow (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hle : spineResidualCard adj P₀ χι₀ sel k ≤ 2 ^ baseMax n) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = false := by
  apply not_flagsAt_of_base_le_spine adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) k hn
  calc spineBaseAt adj P₀ χι₀ sel k
      ≤ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) := spineBaseAt_le_log adj P₀ χι₀ sel k
    _ ≤ Nat.log 2 (2 ^ baseMax n) := Nat.log_mono_right hle
    _ = baseMax n := Nat.log_pow (by norm_num : (1:ℕ) < 2) (baseMax n)

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

Instantiating `confinement_selectedCellIsOrbit` with the STRONG largeness `Large k := 2^(baseMax n) <
spineResidualCard k` (P1, via `flag_imp_pow_baseMax_lt` — the super-poly delivered bound that makes the seal's
`IsLargeScheme` satisfiable) and the concrete symmetric predicate `¬IsBase` (P2, via `flag_imp_symmetric_spine`)
leaves only the two genuinely-open seams as hypotheses: **P3** (`hP3`: large ∧ ¬rigid ⟹ primitive rank-3 classical)
and **Witt** (`hWitt`). Requires `2 ≤ n` (the threshold arithmetic; `n ≤ 1` is trivially canonical). -/

/-- **Confinement on the real spine (P1 ∧ P2 wired; P3/Witt carried).** A Phase-1 flag at node `k` ⟹ the target
cell at prefix `S` is one `Stab(S)`-orbit, given only P3 (`hP3`, now consuming the **super-poly** bound `2^(baseMax
n) < residual`) and Witt (`hWitt`). P1 (via `flag_imp_pow_baseMax_lt`) and P2 (via `flag_imp_symmetric_spine`) are
discharged from the spine. -/
theorem confinement_selectedCellIsOrbit_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    (PrimRank3Classical : Nat → Prop)
    (hP3 : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k →
        ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P (defaultSpineChain adj P₀ χι₀ sel k).D →
        PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel S :=
  confinement_selectedCellIsOrbit adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) S k
    (fun j => 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel j)
    (fun j => ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel j).P (defaultSpineChain adj P₀ χι₀ sel j).D)
    PrimRank3Classical
    (fun hf => flag_imp_pow_baseMax_lt adj P₀ χι₀ sel k hn hf)
    (fun hf => flag_imp_symmetric_spine adj P₀ χι₀ sel k (by omega) hf)
    hP3 hWitt hflag

end ChainDescent.Confinement
