/-
# ScratchConfinementP3.lean — P3 of the confinement lemma: the seal recomposition (WIP, NOT in build.sh)

**Context (route-c-plan §7c, sub-obligation P3).** After P1 (`flag ⟹ n < spineResidualCard k`, large residual)
and P2 (`flag ⟹ ¬IsBase D_k`, symmetric), P3 must conclude the flagging residue is a **primitive rank-3
classical** scheme (node-4/Cameron) — the object on which Witt (P4) delivers flag-transitivity ⟹ VT ⟹ the
selected cell is one orbit ⟹ the assume-VT prune is sound.

**P3 is a CARRIED reduction, not a clean recomposition** — scoping (2026-07-08) found five pieces, three carried:
  1. **Model bridge** `ResidueSchemeModel` — the residue `StabilizerAt adj P₀ D_k` is presented by a
     `SchurianScheme n` `S_k` whose `SchemeAutGroup` order equals the residual order. This is the documented-
     infeasible `SchurianScheme` model-faithfulness gap; the endgame absorbs a non-schurian residue via the D0
     `residueNonSchurian` atom (`Publication.lean`), so it is carried here, never fake-discharged.
  2. **Threshold — RESOLVED (2026-07-08).** The mismatch was: P1 delivered only `residual > n` (`baseMax = log₂ n`)
     but the seal's `IsLargeScheme` needs **super-poly** `|Aut|`. **Fixed by raising `baseMax n := (log₂ n)²`**
     (`ScratchCostModelOracle`), so the flag delivers `2^(baseMax n) = n^{log₂ n} < residual` (super-poly,
     `flag_imp_pow_baseMax_lt`). At this threshold `hLargeBridge` is not just honest but **provable**
     (`largeBridge_confinementLargeScheme`, via `M.hcard`) — see the satisfiability section below. The raise is
     also a **soundness** requirement, not just a matching nicety: at `baseMax = log₂ n` a poly-`Aut` non-Schurian
     SRG (Chang graph, `|Aut|=384 > 28=n`) would flag and be assume-VT-pruned *incorrectly*; the superlogarithmic
     threshold excludes every poly-`Aut` residue from flagging (`not_flagsAt_of_residualCard_le_pow`).
  3. **Primitivity** `hprim : S_k.IsPrimitive` — the seal itself carries `hImprim` (block-tower infra, deferred);
     P3 inherits it.
  4. **Seal application** — `exhaustiveObstruction_scheme` (primitive ∧ rank ≥ 2 ∧ large ⟹ `IsCameronScheme`,
     modulo the cited `PrimitiveCCClassification` = G3). **This is the provable core, wired REAL below.**
  5. **Classicality** — `IsCameronScheme ⟹ classical forms scheme ⟹ Witt-transitive`: the Liebeck citation, the
     P3→Witt boundary (lives in `hWitt`, the assembly's carried Witt hypothesis).

**Deliverable here:** the reduction that consumes {model, largeness-bridge, primitivity, G3} and produces
`PrimRank3Classical` (= `∃` a Cameron model of the residue) via the real seal — pinning P3's interface exactly
like the assembly skeleton pins the whole confinement lemma. Discharging the carried pieces (2–3, and the model)
is downstream Seal/Runtime work; wiring `PrimRank3Classical ⟹ FrameSelectorTransitive` (piece 5) is the Witt step.

Imports `ScratchConfinement` (spineResidualCard + the assembly) — pulls Cascade (`exhaustiveObstruction_scheme`,
`PrimitiveCCClassification`, `SchurianScheme`, `IsPrimitive`). Axiom target `[propext, Classical.choice,
Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinement

namespace ChainDescent.ConfinementP3

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.Confinement
open ChainDescent.NodeCountBridge
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **The residue-scheme model at node `k` (the model bridge — carried).** A `SchurianScheme n` `S_k` presenting
the level-`k` residue: all relations occur (`hne`), rank ≥ 2 (`hrank`), and its scheme-automorphism order equals
the residue's residual `Aut` order (`hcard`), so P1's largeness transfers onto the scheme side. This is the
`SchurianScheme` model-faithfulness gap; a residue for which no such faithful `S_k` exists is *non-schurian* and is
honestly flagged into `UnhandledResidue` (D0), never assume-VT-pruned. The `hcard` field keeps the model non-vacuous
(it must match the actual residue, not be an arbitrary scheme). -/
structure ResidueSchemeModel (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) where
  S : SchurianScheme n
  hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true
  hrank : 2 ≤ S.rank
  hcard : Nat.card S.toAssociationScheme.SchemeAutGroup = spineResidualCard adj P₀ χι₀ sel k

/-- **`PrimRank3Classical` — the predicate P3 produces and Witt (P4) consumes.** The residue is presented by a
scheme model `M` that the seal classifies as a **Cameron section** (`IsCameronScheme n M.S`) — the primitive
rank-3 node-4/hidden-Johnson residue. Parameterized by the seal's `IsCameronScheme` (the endgame supplies "what
counts as Cameron"). The subsequent classicality step (Liebeck) + Witt turns this into `FrameSelectorTransitive`
(the assembly's `hWitt`). -/
def PrimRank3Classical (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop) (k : Nat) : Prop :=
  ∃ M : ResidueSchemeModel adj P₀ χι₀ sel k, IsCameronScheme n M.S

/-- **P3 — the seal recomposition (provable core wired REAL).** Given the residue-scheme model `M`, the largeness
bridge `hLargeBridge` (piece 2, the threshold carrier), primitivity `hprim` (piece 3, `hImprim`-inherited), and the
cited classification `hClassify` (G3), a flag's large residual (`n < spineResidualCard k`) makes the residue a
**Cameron section** via the landed `exhaustiveObstruction_scheme`. Produces exactly the assembly's `hP3` shape
(`n < spineResidualCard k → ¬IsBase D_k → PrimRank3Classical k`). The `¬IsBase` (symmetric) input is part of the
interface but is subsumed by largeness (P2 *derived* `¬IsBase` from it), so it is unused in the derivation. -/
theorem residue_primRank3Classical (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat)
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hLargeBridge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hlarge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k)
    (_hsym : ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D) :
    PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k :=
  ⟨M, exhaustiveObstruction_scheme hClassify M.S M.hne hprim M.hrank (hLargeBridge hlarge)⟩

/-! ## Confinement on the real spine — P1 ∧ P2 ∧ P3 all wired, only Witt + the P3 carriers remaining

Feeding `residue_primRank3Classical` (P3, via the real seal) into `confinement_selectedCellIsOrbit_spine`
(P1 ∧ P2 wired) leaves as hypotheses exactly: the cited classification `hClassify` (G3), the residue-scheme model
`M` (the `SchurianScheme` gap, D0-absorbed), the largeness bridge `hLargeBridge` (the threshold decision), the
primitivity `hprim` (`hImprim`), and Witt `hWitt` (`PrimRank3Classical ⟹ FrameSelectorTransitive` — Liebeck +
Witt). Everything else — P1, P2, P3's composition, P4's producer — is proved. -/

/-- **Confinement on the real spine, P1 ∧ P2 ∧ P3 wired.** A Phase-1 flag at node `k` ⟹ the target cell at prefix
`S` is one `Stab(S)`-orbit, carrying only the P3 pieces (`hClassify`/`M`/`hLargeBridge`/`hprim`) and Witt
(`hWitt`). The whole confinement chain now composes through the real seal `exhaustiveObstruction_scheme`; the
remaining obligations are the carried citations/gaps, not project logic. -/
theorem confinement_selectedCellIsOrbit_spine_P3 (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hLargeBridge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine adj P₀ χι₀ sel χsel S k hn
    (PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme)
    (fun hlarge hsym =>
      residue_primRank3Classical adj P₀ χι₀ sel k hClassify M hLargeBridge hprim hlarge hsym)
    hWitt hflag

/-! ## Satisfiability of `hLargeBridge` — it is DISCHARGEABLE at the raised threshold

The threshold decision's payoff: with `baseMax = (log₂ n)²`, the flag delivers `2^(baseMax n) < residual`
(super-poly), and the seal's largeness predicate can be instantiated at exactly that threshold — at which the
largeness bridge is not merely *assumable* but **provable** (from `M.hcard`). With the old `baseMax = log₂ n`
(delivering only `residual > n`) the same bridge would be *false* for a super-poly `IsLargeScheme` (a residue with
`n < |Aut| ≤ n^{log₂ n}` satisfies the flag's bound but not super-poly largeness). So the raise is exactly what
makes the P3 input satisfiable. -/

/-- **The confinement's largeness predicate at the delivered threshold** — `|Aut| > 2^(baseMax n) = n^{log₂ n}`, a
super-polynomial threshold. A genuine Cameron classification (G3) holds at any super-poly threshold, so `hClassify`
at this predicate is the real citation. -/
def confinementLargeScheme (n : Nat) : ∀ (m : Nat), SchurianScheme m → Prop :=
  IsLargeSchemeViaAut (fun c => 2 ^ baseMax n < c)

/-- **`hLargeBridge` is DISCHARGEABLE (the satisfiability check).** With `IsLargeScheme := confinementLargeScheme n`,
the largeness bridge `2^(baseMax n) < spineResidualCard k → IsLargeScheme n M.S` is *provable*: the residual order
IS the scheme-Aut order (`M.hcard`), so the delivered super-poly bound transfers verbatim. So the P3 largeness input
is real, not a placeholder — the raised threshold made it so. -/
theorem largeBridge_confinementLargeScheme (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (h : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k) :
    confinementLargeScheme n n M.S := by
  show 2 ^ baseMax n < Nat.card M.S.toAssociationScheme.SchemeAutGroup
  rw [M.hcard]; exact h

/-- **Confinement with `hLargeBridge` DISCHARGED** — carries only the genuine citations/gaps: `hClassify` (G3 at the
super-poly `confinementLargeScheme`), the model `M`, primitivity `hprim`, and Witt `hWitt`. The largeness bridge is
gone (proved by `largeBridge_confinementLargeScheme`). This is the confinement chain at its tightest: P1 ∧ P2 ∧ P3
wired, largeness satisfiable, only the named external results remaining. -/
theorem confinement_selectedCellIsOrbit_spine_P3_discharged (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine_P3 adj P₀ χι₀ sel χsel S k hn hClassify M
    (largeBridge_confinementLargeScheme adj P₀ χι₀ sel k M) hprim hWitt hflag

end ChainDescent.ConfinementP3
