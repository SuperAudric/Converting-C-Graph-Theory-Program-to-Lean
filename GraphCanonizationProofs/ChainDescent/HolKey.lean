import ChainDescent.DeckSupply

/-!
# `F3a` — `holKey` : the HOLONOMY key (force side), and the `KeySeparates` firing infrastructure

## What F3 is, after the scoping pass (`docs/chain-descent-fold-tower-plan.md` §5b)

The genuine force-side residue of the fold family is **distinguishable-but-WL-merged** cells: twisted covers
where a pin leaves ties (the within-copy mirror survives), the histogram/leaf branches of `lookaheadKey` are
blind, and no consume supply can help (there is no automorphism to certify — the vertices really are
inequivalent). The twist invariant is **coset/solvability** data — kernels, ranks and local forcing profiles
are identical for twisted and untwisted covers, which is why neither propagation signatures (the C# B1d
unit-propagation ceiling) nor rank profiles can rank it.

Its structurally-readable form is the **holonomy** of the fold: compose the vertical matchings (F2a's
unique-fiber-partner maps) around closed walks of the copy graph. The composite is a partial permutation of
the start copy — identity for straight cycles, the mirror/deck twist otherwise; gauge-independent (no
reference pairing is ever chosen — only canonical unique-partner lookups compose) and arbitrary-arity (a
`Z_s` twist appears as an order-`s` composite). It is exactly the object the Smith solve canonicalizes
(§11.13a), read combinatorially.

**MEASURED (F3 probes, 2026-07-18, n = 30 `U3 ⊔ T3` — vfold3 unioned with its one-pair-twisted variant;
non-isomorphic by twist parity, 1-WL merges the components):** branch cell = all 6 pendants across both
components; `lookaheadKey` keeps 6 (dead); the L = 3 holonomy signature computes `{0, 5}` on every U-pendant
and `{2, 5}` on every T-pendant — a clean 3|3 split, uniform within each orbit, at ~0.5 s interpreted.

## The key (v1 grading: L = 3 — digon-free triangle walks; the ladder extends like every other oracle's `d`)

`holSig adj χ v` = the sorted, deduplicated set of *moved-counts* of the holonomy composites
`copy(v) → copy(t₁) → copy(t₂) → copy(v)` over ALL target-vertex pairs `(t₁, t₂)` (full enumeration — no
walk, tree, or representative is ever chosen: standing trap #7). A composite that leaves the copy or hits a
missing partner counts as moved — validity is part of the value, not a side condition.

## Obligations

- ① = `KeyEquivariant holKey` (the only soundness obligation of a force key). Proof route: the partner
  lookups conjugate (`uniqueMem_transport` + `mem_relComp_transport`, the F2a toolkit), the walk enumeration
  reindexes bijectively, and the dedup+sort is invariant under reindexing. STAGED — see the build-state note
  below.
- Firing = `KeySeparates` (defined here: force's dual of `CellIsOrbit`): the key values separate every
  non-`Aut`-equivalent pair, so `keepMin` keeps a subset of ONE orbit (`keepMin_pairwise_aut_of_separates`)
  — which the consume side then collapses. Graded and measured, never claimed globally.
- ② = the cost field, billed flat.

## Build state (2026-07-18)

Definitional core + `KeySeparates` infrastructure + firing theorem LANDED (this file, compile-clean,
axiom-clean). The evaluation twins and the `KeyEquivariant` proof are STAGED: both need the component-closure
lemma set (`relComp` of a symmetric relation is membership-equivalence — closedness after `n` monotone
rounds), which F2a deliberately never needed and F3a genuinely does (well-definedness of copy-designators).
Until they land, `holKey` is the reasoned-about object; do NOT `#eval` the spec forms at `n ≥ 15` (the
relation memberships recompute `relComp` per lookup — trap #1's shape; the probe used materialised id-tables).
-/

namespace ChainDescent
namespace Hol

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (IsColAut)
open ChainDescent.Fold (relComp sameCellRel crossCellRel uniqueMem)
open ChainDescent.Force (Key keyV keyCost KeyEquivariant keepMin kmin? keepMin_none keepMin_some
  kmin?_eq_none_iff)

variable {n : Nat}

/-! ## 1. `KeySeparates` — force's firing predicate (the dual of consume's `CellIsOrbit`) -/

/-- **The force-side firing predicate**: on this node, equal key values occur only on `Aut`-equivalent
branches. (The contrapositive is the useful reading: the key SEPARATES every genuinely-different pair.)
Graded per node, like `CellIsOrbit` — never claimed globally. -/
def KeySeparates (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    keyV key adj χ u = keyV key adj χ w →
      ∃ ρ : Equiv.Perm (Fin n), IsColAut adj χ ρ ∧ ρ u = w

/-- Members of the narrowed set all attain the minimum key value. -/
theorem keyV_eq_of_mem_keepMin {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {B : List (Fin n)} {u w : Fin n} (hB : B ≠ [])
    (hu : u ∈ keepMin key adj χ B) (hw : w ∈ keepMin key adj χ B) :
    keyV key adj χ u = keyV key adj χ w := by
  cases hk : kmin? (B.map (keyV key adj χ)) with
  | none =>
      exact absurd (List.map_eq_nil_iff.mp ((kmin?_eq_none_iff _).mp hk)) hB
  | some m =>
      rw [keepMin_some hk] at hu hw
      have hu' := of_decide_eq_true (List.mem_filter.mp hu).2
      have hw' := of_decide_eq_true (List.mem_filter.mp hw).2
      rw [hu', hw']

/-- **★ THE FORCE FIRING THEOREM.** If the key separates, the kept branches are pairwise `Aut`-equivalent —
the narrowed set is inside ONE orbit, which is exactly what the consume side can then collapse
(`forceThenConsume`). This is the graded mirror of `cellIsOrbit_*`. -/
theorem keepMin_pairwise_aut_of_separates {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    (hsep : KeySeparates key adj χ) :
    ∀ u ∈ keepMin key adj χ (branches χ), ∀ w ∈ keepMin key adj χ (branches χ),
      ∃ ρ : Equiv.Perm (Fin n), IsColAut adj χ ρ ∧ ρ u = w := by
  intro u hu w hw
  have hsub : ∀ x ∈ keepMin key adj χ (branches χ), x ∈ branches χ := by
    intro x hx
    cases hk : kmin? ((branches χ).map (keyV key adj χ)) with
    | none => rw [keepMin_none hk] at hx; exact hx
    | some m => rw [keepMin_some hk] at hx; exact (List.mem_filter.mp hx).1
  have hne : branches χ ≠ [] := by
    intro hnil
    rw [hnil] at hsub
    have := hsub u (by
      cases hk : kmin? (([] : List (Fin n)).map (keyV key adj χ)) with
      | none => rw [hnil] at hu; rwa [keepMin_none hk] at hu ⊢
      | some m => simp [kmin?] at hk)
    cases this
  exact hsep u (hsub u hu) w (hsub w hw)
    (keyV_eq_of_mem_keepMin hne (by rwa [] at hu) hw)

/-! ## 2. The holonomy composite — spec form (relations only; no ids, no representatives) -/

/-- The unique fiber partner of `x` in the copy of `t` — F2a's one-sided lookup, with the target copy
designated by a VERTEX (never an id or a representative). `none` when absent or ambiguous. -/
def partnerTo (adj : AdjMatrix n) (χ : Colouring n) (x t : Fin n) : Option (Fin n) :=
  uniqueMem (fun w => decide (w ∈ relComp (sameCellRel adj χ) x)
    && decide (w ∈ relComp (crossCellRel adj χ) t))

/-- A valid L = 3 walk: the three copies are pairwise distinct (membership tests only). -/
def walkOk (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) : Bool :=
  !decide (t₁ ∈ relComp (crossCellRel adj χ) v)
    && !decide (t₂ ∈ relComp (crossCellRel adj χ) v)
    && !decide (t₂ ∈ relComp (crossCellRel adj χ) t₁)

/-- **The holonomy moved-count** of the walk `copy(v) → copy(t₁) → copy(t₂) → copy(v)`: how many vertices of
`v`'s copy fail to return to themselves under the composed partner maps. A missing/ambiguous partner counts
as moved — validity is part of the value. -/
def holMoved (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) : Nat :=
  ((List.finRange n).filter
    (fun x => decide (x ∈ relComp (crossCellRel adj χ) v))).countP (fun x =>
      match partnerTo adj χ x t₁ with
      | none => true
      | some y₁ =>
          match partnerTo adj χ y₁ t₂ with
          | none => true
          | some y₂ =>
              match partnerTo adj χ y₂ v with
              | none => true
              | some y₃ => !decide (y₃ = x))

/-- **The holonomy signature**: the sorted set of moved-counts over ALL valid target pairs. Full enumeration
plus dedup+sort make it representative-free (trap #7) and multiplicity-free (so the evaluation twin may
enumerate per copy instead of per vertex, once the component-closure bridge lands). -/
def holSig (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  (((List.finRange n).flatMap (fun t₁ => (List.finRange n).filterMap (fun t₂ =>
      if walkOk adj χ v t₁ t₂ then some (holMoved adj χ v t₁ t₂) else none))).dedup).mergeSort (· ≤ ·)

/-- **★ THE HOLONOMY KEY.** Ranks a branch by its copy's holonomy signature — the coset/monodromy data the
1-WL look-ahead cannot see. Cost billed flat at `n⁵` per evaluation (walk pairs × copy sweep × partner scans,
honestly priced for the naive spec; the staged evaluation twin is a constant-factor item). -/
def holKey : Key n := fun adj χ v =>
  (holSig adj χ v, n * n * n * n * n)

@[simp] theorem keyV_holKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (holKey (n := n)) adj χ v = holSig adj χ v := rfl

@[simp] theorem keyCost_holKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (holKey (n := n)) adj χ v = n * n * n * n * n := rfl

end Hol
end ChainDescent
