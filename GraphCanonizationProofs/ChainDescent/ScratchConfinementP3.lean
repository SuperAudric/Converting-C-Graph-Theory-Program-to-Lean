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
  2. **★ Threshold mismatch (the key finding)** — P1 delivers only `residual > n` (`baseMax = log₂ n`), but the
     seal's `PrimitiveCCClassification` / `IsLargeSchemeViaAut` needs **super-polynomial** `|Aut|` (the Cameron
     driver; `> n` is far weaker). So `hLargeBridge : n < spineResidualCard k → IsLargeScheme n S_k` is only
     honest if either (a) `IsLargeScheme` is instantiated at "`> n`" AND a classification valid at that threshold
     is used, or (b) `baseMax` is tuned **up** (e.g. `(log₂ n)²` or `n^ε`) so the flag fires only for super-poly
     residual. This is a genuine **cost-model decision** — the §7c "tuning fact" made concrete — surfaced as the
     explicit `hLargeBridge` carrier so it cannot be silently assumed.
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
    (hLargeBridge : n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hlarge : n < spineResidualCard adj P₀ χι₀ sel k)
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
    (sel : Colouring n → Finset (Fin n)) (S : Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hLargeBridge : n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel S :=
  confinement_selectedCellIsOrbit_spine adj P₀ χι₀ sel S k hn
    (PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme)
    (fun hlarge hsym =>
      residue_primRank3Classical adj P₀ χι₀ sel k hClassify M hLargeBridge hprim hlarge hsym)
    hWitt hflag

end ChainDescent.ConfinementP3
