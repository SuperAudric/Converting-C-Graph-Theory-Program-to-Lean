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

## Build state (2026-07-18: F3a COMPLETE — all tranches landed, axiom-clean; guards `Regression` §12)

- §1 `KeySeparates` + the firing theorem `keepMin_pairwise_aut_of_separates`.
- §2 the **component-closure lemma set**: `relComp_closed` (monotone-rounds pigeonhole),
  `mem_relComp_self/trans/symm`, `mem_relComp_congr` = copy-designator well-definedness — the convergence
  content F2a deliberately never needed, generic over any SYMMETRIC relation (hence §3).
- §3 the **symmetrized** cell relations `symSame`/`symCross` (weakly-connected components: `AdjMatrix`
  guarantees no symmetry, and symmetrizing makes the closure lemmas unconditional; matches the C#).
- §4–5 the spec key: `partnerTo`/`walkOk`/`holMoved`/`holHas`/`holSig`/`holKey`. `holSig` is the **indicator
  vector over `[0, n]`, presence-first** (`0` = attained, so the lex-least key prefers the straightest copy —
  which is also the side a fully-symmetric consume supply can then collapse) — canonical BY CONSTRUCTION (no
  sort, no dedup), so equivariance is pure existential reindexing rather than sorted-permutation plumbing.
- §6 **`keyEquivariant_holKey`** — the whole ① obligation: `partnerTo_conj` (`uniqueMem_transport` +
  `mem_relComp_transport`), `walkOk_conj`, `holMoved_conj` (`countP` fused over the filter, reindexed via
  `(finRange n).map σ ~ finRange n`), `holHas_conj` (existential reindexing), `holSig_conj`.
- §7 the **evaluation twins**: `compIdx`/`compTbl` (min-member id-tables, INTERNAL ids — `compIdx_eq_iff`
  proves id-equality is exactly component membership), `pfT`/`walkOkT`/`holMovedT`, `holSigFast`/`holKeyFast`
  with value-equality bridges (`holSigFast_eq`/`holKeyFast_eq`). Do NOT `#eval` the spec forms at `n ≥ 15`
  (they recompute `relComp` per membership test — trap #1's shape); the twin does the full `n = 30` witness
  `keepMin` in ~10 s interpreted.
- §8 capstones: `holKey_canonizer` (pure force), `holKey_foldDeck_guarded_canonizer` and
  `holKey_foldDeck_selNode_canonizer` (**the F3a canonizers of record for the fold family**: force = holonomy,
  consume = `foldSupply ++ deckSupply`).

**Measured (Regression §12, n = 30 `U3 ⊔ T3`):** branch cell = all 6 pendants (WL-merged), `lookaheadKey`
keeps 6, `holKeyFast` keeps exactly the straight triple `[4, 9, 14]` — one genuine orbit, which `foldSupply`
collapses (measured at n = 15, §10's family). ✅ **The n = 30 composite is now MEASURED**
(`PerformanceTest` §10, 2026-07-18): the F2a evaluation constant landed as `FoldFast.foldSupplyFast`
(membership-ROW tables, not §7's id-tables — `compIdx_eq_iff` needs symmetry and F2a's closures are
directed), and one `forceThenConsume holKeyFast (foldSupplyFast ++ deckSupply)` step narrows the 6-fan to
`[4]` in ~40 s interpreted. **F3b (Smith/CRT coset)** stays gated on a measured holonomy-failure witness —
plan §5b; the multipede double's rigid gauge pair (`MultipedeWitness.lean`) is that shape, gated until
force-critical.
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
Graded per node, like `CellIsOrbit` — never claimed globally.

⚠ **This predicate has a later twin.** `KeyComplete.KeySeparatesAt` (2026-07-27) is the same thing
written contrapositively, and `KeyComplete.keySeparatesAt_iff_hol` is the bridge; consequently
`KeyComplete.forcedSet_single_orbit_of_keySeparatesAt` re-proves `keepMin_pairwise_aut_of_separates`
below (`Composite.forcedSet key adj χ` *is* `keepMin key adj χ (branches χ)`). The genuinely new part
of that later work is `ForcePick.forceThenPick`, which discards on the **uncomputed** automorphism;
this file's theorem still routes its conclusion through consume. Prefer the bridge over re-deriving
either side. -/
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

/-! ## 2. Component closure — `relComp` of a symmetric relation is a membership-equivalence

F2a deliberately proved nothing about `relComp` beyond transport (every statement was relative to the computed
value). F3a genuinely needs more: copy-designators are VERTICES, and their well-definedness (any vertex of a
copy designates the same copy) is component theory — closedness after the `n` monotone rounds, then
symmetry/transitivity of membership. Proved here once, generically. -/

section Closure

variable (rel : Fin n → Fin n → Bool)

private theorem nodup_iterate_relStep (b : Fin n) :
    ∀ k : Nat, ((Fold.relStep rel)^[k] [b]).Nodup
  | 0 => List.nodup_singleton b
  | (k + 1) => by
      rw [Function.iterate_succ_apply']
      exact (List.nodup_dedup _)

private theorem mem_iterate_relStep_mono {b x : Fin n} {k : Nat}
    (h : x ∈ (Fold.relStep rel)^[k] [b]) : x ∈ (Fold.relStep rel)^[k + 1] [b] := by
  rw [Function.iterate_succ_apply']
  exact Fold.mem_relStep_iff.mpr (Or.inl h)

private theorem stab_succ {b : Fin n} {k : Nat}
    (h : ∀ x, x ∈ (Fold.relStep rel)^[k] [b] ↔ x ∈ (Fold.relStep rel)^[k + 1] [b]) :
    ∀ x, x ∈ (Fold.relStep rel)^[k + 1] [b] ↔ x ∈ (Fold.relStep rel)^[k + 2] [b] := by
  intro x
  rw [Function.iterate_succ_apply' _ (k + 1)]
  constructor
  · intro hx
    exact Fold.mem_relStep_iff.mpr (Or.inl hx)
  · intro hx
    rcases Fold.mem_relStep_iff.mp hx with hx' | ⟨v, hv, hrv⟩
    · exact hx'
    · have hv' : v ∈ (Fold.relStep rel)^[k] [b] := (h v).mpr hv
      rw [Function.iterate_succ_apply']
      exact Fold.mem_relStep_iff.mpr (Or.inr ⟨v, hv', hrv⟩)

private theorem exists_stab (b : Fin n) :
    ∃ k ≤ n, ∀ x, x ∈ (Fold.relStep rel)^[k] [b] ↔ x ∈ (Fold.relStep rel)^[k + 1] [b] := by
  by_contra hcon
  have hcon' : ∀ k, k ≤ n →
      ¬ ∀ x, (x ∈ (Fold.relStep rel)^[k] [b] ↔ x ∈ (Fold.relStep rel)^[k + 1] [b]) :=
    fun k hk hP => hcon ⟨k, hk, hP⟩
  -- every level ≤ n grows strictly, so the toFinset cards climb past `n`
  have hgrow : ∀ k ≤ n, ((Fold.relStep rel)^[k] [b]).toFinset
      ⊂ ((Fold.relStep rel)^[k + 1] [b]).toFinset := by
    intro k hk
    obtain ⟨x, hx⟩ := not_forall.mp (hcon' k hk)
    refine Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.mpr ?_
    · exact List.mem_toFinset.mpr (mem_iterate_relStep_mono rel (List.mem_toFinset.mp hy))
    · have hx' : x ∈ (Fold.relStep rel)^[k + 1] [b] ∧ x ∉ (Fold.relStep rel)^[k] [b] := by
        by_cases hmem : x ∈ (Fold.relStep rel)^[k] [b]
        · exact absurd (iff_of_true hmem (mem_iterate_relStep_mono rel hmem)) hx
        · by_cases hmem' : x ∈ (Fold.relStep rel)^[k + 1] [b]
          · exact ⟨hmem', hmem⟩
          · exact absurd (iff_of_false hmem hmem') hx
      exact ⟨x, List.mem_toFinset.mpr hx'.1, fun hc => hx'.2 (List.mem_toFinset.mp hc)⟩
  have hcard : ∀ k ≤ n + 1, k + 1 ≤ ((Fold.relStep rel)^[k] [b]).toFinset.card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have h1 := ih (Nat.le_of_succ_le hk)
        have h2 := Finset.card_lt_card (hgrow k (Nat.lt_succ_iff.mp (Nat.lt_of_succ_le hk)))
        omega
  have hle : ((Fold.relStep rel)^[n + 1] [b]).toFinset.card ≤ n := by
    have := Finset.card_le_univ ((Fold.relStep rel)^[n + 1] [b]).toFinset
    simpa using this
  have := hcard (n + 1) le_rfl
  omega

/-- The closure really is closed: a `rel`-step out of `relComp` stays inside. -/
theorem relComp_closed {b v w : Fin n} (hv : v ∈ relComp rel b) (hw : rel v w = true) :
    w ∈ relComp rel b := by
  obtain ⟨k, hk, hstab⟩ := exists_stab rel b
  have hall : ∀ j, (∀ x, x ∈ (Fold.relStep rel)^[k] [b] ↔ x ∈ (Fold.relStep rel)^[k + 1] [b]) →
      ∀ x, x ∈ (Fold.relStep rel)^[k + j] [b] ↔ x ∈ (Fold.relStep rel)^[k + j + 1] [b] := by
    intro j
    induction j with
    | zero => intro h; exact h
    | succ j ih => intro h; exact stab_succ rel (ih h)
  have hn : ∀ x, x ∈ (Fold.relStep rel)^[n] [b] ↔ x ∈ (Fold.relStep rel)^[n + 1] [b] := by
    have := hall (n - k) hstab
    rwa [Nat.add_sub_cancel' hk] at this
  have hw' : w ∈ (Fold.relStep rel)^[n + 1] [b] := by
    rw [Function.iterate_succ_apply']
    exact Fold.mem_relStep_iff.mpr (Or.inr ⟨v, hv, hw⟩)
  exact (hn w).mpr hw'

/-- Anything reachable from a member of a closed set is in it. -/
theorem relComp_subset_of_closed {C : List (Fin n)}
    (hC : ∀ v ∈ C, ∀ w, rel v w = true → w ∈ C) {b : Fin n} (hb : b ∈ C) :
    ∀ x ∈ relComp rel b, x ∈ C := by
  suffices h : ∀ k, ∀ x ∈ (Fold.relStep rel)^[k] [b], x ∈ C from h n
  intro k
  induction k with
  | zero =>
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact hb
  | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rcases Fold.mem_relStep_iff.mp hx with hx' | ⟨v, hv, hrv⟩
      · exact ih x hx'
      · exact hC v (ih v hv) x hrv

theorem mem_relComp_self (b : Fin n) : b ∈ relComp rel b := by
  suffices h : ∀ k, b ∈ (Fold.relStep rel)^[k] [b] from h n
  intro k
  induction k with
  | zero => exact List.mem_singleton_self b
  | succ k ih => exact mem_iterate_relStep_mono rel ih

/-- Membership is transitive. -/
theorem mem_relComp_trans {a b c : Fin n} (hb : b ∈ relComp rel a) (hc : c ∈ relComp rel b) :
    c ∈ relComp rel a :=
  relComp_subset_of_closed rel (fun _ hv _ hw => relComp_closed rel hv hw) hb c hc

/-- Membership is symmetric — for a symmetric relation. -/
theorem mem_relComp_symm (hsym : ∀ a b, rel a b = rel b a) {a b : Fin n}
    (h : b ∈ relComp rel a) : a ∈ relComp rel b := by
  suffices hk : ∀ k, ∀ x ∈ (Fold.relStep rel)^[k] [a], a ∈ relComp rel x from hk n b h
  intro k
  induction k with
  | zero =>
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact mem_relComp_self rel a
  | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      rcases Fold.mem_relStep_iff.mp hx with hx' | ⟨v, hv, hrv⟩
      · exact ih x hx'
      · have hvx : v ∈ relComp rel x :=
          relComp_closed rel (mem_relComp_self rel x) (by rw [hsym x v]; exact hrv)
        exact mem_relComp_trans rel hvx (ih v hv)

/-- **★ Copy-designator well-definedness**: any member of a component designates the same component. -/
theorem mem_relComp_congr (hsym : ∀ a b, rel a b = rel b a) {t t' : Fin n}
    (h : t' ∈ relComp rel t) (x : Fin n) :
    x ∈ relComp rel t' ↔ x ∈ relComp rel t :=
  ⟨fun hx => mem_relComp_trans rel h hx,
   fun hx => mem_relComp_trans rel (mem_relComp_symm rel hsym h) hx⟩

end Closure

/-! ## 3. The symmetrized cell relations

`AdjMatrix` carries no symmetry guarantee, so the key's copy/fiber notion is the `‖`-closure — weakly-connected
components, matching the C# — which makes the closure lemmas above apply unconditionally. -/

/-- Symmetrized same-cell (vertical) adjacency. -/
def symSame (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) : Bool :=
  sameCellRel adj χ v w || sameCellRel adj χ w v

/-- Symmetrized cross-cell (horizontal) adjacency. -/
def symCross (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) : Bool :=
  crossCellRel adj χ v w || crossCellRel adj χ w v

theorem symSame_symm (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    symSame adj χ v w = symSame adj χ w v := Bool.or_comm _ _

theorem symCross_symm (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) :
    symCross adj χ v w = symCross adj χ w v := Bool.or_comm _ _

theorem symSame_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b : Fin n) :
    symSame (relabelAdj σ adj) (transportColouring σ χ) (σ a) (σ b) = symSame adj χ a b := by
  unfold symSame
  rw [Fold.sameCellRel_transport, Fold.sameCellRel_transport]

theorem symCross_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b : Fin n) :
    symCross (relabelAdj σ adj) (transportColouring σ χ) (σ a) (σ b) = symCross adj χ a b := by
  unfold symCross
  rw [Fold.crossCellRel_transport, Fold.crossCellRel_transport]

/-! ## 4. The holonomy composite — spec form (relations only; no ids, no representatives) -/

/-- The unique fiber partner of `x` in the copy of `t` — F2a's one-sided lookup, with the target copy
designated by a VERTEX (never an id or a representative). `none` when absent or ambiguous. -/
def partnerTo (adj : AdjMatrix n) (χ : Colouring n) (x t : Fin n) : Option (Fin n) :=
  uniqueMem (fun w => decide (w ∈ relComp (symSame adj χ) x)
    && decide (w ∈ relComp (symCross adj χ) t))

/-- A valid L = 3 walk: the three copies are pairwise distinct (membership tests only). -/
def walkOk (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) : Bool :=
  !decide (t₁ ∈ relComp (symCross adj χ) v)
    && !decide (t₂ ∈ relComp (symCross adj χ) v)
    && !decide (t₂ ∈ relComp (symCross adj χ) t₁)

/-- **The holonomy moved-count** of the walk `copy(v) → copy(t₁) → copy(t₂) → copy(v)`: how many vertices of
`v`'s copy fail to return to themselves under the composed partner maps. A missing/ambiguous partner counts
as moved — validity is part of the value. -/
def holMoved (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) : Nat :=
  ((List.finRange n).filter
    (fun x => decide (x ∈ relComp (symCross adj χ) v))).countP (fun x =>
      match partnerTo adj χ x t₁ with
      | none => true
      | some y₁ =>
          match partnerTo adj χ y₁ t₂ with
          | none => true
          | some y₂ =>
              match partnerTo adj χ y₂ v with
              | none => true
              | some y₃ => !decide (y₃ = x))

/-- Is some valid walk's moved-count equal to `c`? (The signature's membership test.) -/
def holHas (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) (c : Nat) : Bool :=
  (List.finRange n).any (fun t₁ => (List.finRange n).any (fun t₂ =>
    walkOk adj χ v t₁ t₂ && decide (holMoved adj χ v t₁ t₂ = c)))

/-- **The holonomy signature**: the indicator vector, over the value range `[0, n]` (a moved-count never
exceeds the copy size), of which moved-counts are attained by some valid walk — encoded presence-first
(`0` = attained), so the lex-LEAST key prefers the branch whose holonomy is trivial-est (the straightest
copy). Full enumeration makes it representative-free (trap #7); the indicator form makes it **canonical by
construction** — no sorting, no dedup — so equivariance is pure existential reindexing. -/
def holSig (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  (List.range (n + 1)).map (fun c => if holHas adj χ v c then 0 else 1)

/-- **★ THE HOLONOMY KEY.** Ranks a branch by its copy's holonomy signature — the coset/monodromy data the
1-WL look-ahead cannot see. Cost billed flat at `n⁵` per evaluation (walk pairs × copy sweep × partner scans,
honestly priced for the naive spec; the staged evaluation twin is a constant-factor item). -/
def holKey : Key n := fun adj χ v =>
  (holSig adj χ v, n * n * n * n * n)

@[simp] theorem keyV_holKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (holKey (n := n)) adj χ v = holSig adj χ v := rfl

@[simp] theorem keyCost_holKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (holKey (n := n)) adj χ v = n * n * n * n * n := rfl

/-! ## 6. `①` — the key is EQUIVARIANT (the whole soundness obligation of a force key) -/

private theorem finRange_map_perm (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map σ).Perm (List.finRange n) := by
  refine List.perm_of_nodup_nodup_toFinset_eq
    ((List.nodup_finRange n).map σ.injective) (List.nodup_finRange n) ?_
  ext u
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, iff_true]
  exact ⟨σ.symm u, by simp⟩

private theorem countP_reindex (σ : Equiv.Perm (Fin n)) (f : Fin n → Bool) :
    (List.finRange n).countP (fun x => f (σ x)) = (List.finRange n).countP f := by
  have h1 : ((List.finRange n).map σ).countP f = (List.finRange n).countP f :=
    (finRange_map_perm σ).countP_eq f
  rw [← h1, List.countP_map]
  rfl

theorem partnerTo_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (x t : Fin n) :
    partnerTo (relabelAdj σ adj) (transportColouring σ χ) (σ x) (σ t)
      = (partnerTo adj χ x t).map σ := by
  unfold partnerTo
  refine Fold.uniqueMem_transport σ (fun w => ?_)
  rw [decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symSame_transport σ adj χ) x w),
      decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symCross_transport σ adj χ) t w)]

theorem walkOk_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v t₁ t₂ : Fin n) :
    walkOk (relabelAdj σ adj) (transportColouring σ χ) (σ v) (σ t₁) (σ t₂)
      = walkOk adj χ v t₁ t₂ := by
  unfold walkOk
  rw [decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symCross_transport σ adj χ) v t₁),
      decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symCross_transport σ adj χ) v t₂),
      decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symCross_transport σ adj χ) t₁ t₂)]

theorem holMoved_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v t₁ t₂ : Fin n) :
    holMoved (relabelAdj σ adj) (transportColouring σ χ) (σ v) (σ t₁) (σ t₂)
      = holMoved adj χ v t₁ t₂ := by
  unfold holMoved
  rw [List.countP_filter, List.countP_filter, ← countP_reindex σ]
  congr 1
  funext x
  congr 1
  · -- the composed-partner chain transports pointwise (re-expose each hop after the previous one reduces)
    simp only [partnerTo_conj]
    cases hp₁ : partnerTo adj χ x t₁ with
    | none => rfl
    | some y₁ =>
        simp only [Option.map_some, partnerTo_conj]
        cases hp₂ : partnerTo adj χ y₁ t₂ with
        | none => rfl
        | some y₂ =>
            simp only [Option.map_some, partnerTo_conj]
            cases hp₃ : partnerTo adj χ y₂ v with
            | none => rfl
            | some y₃ =>
                simp only [Option.map_some]
                rw [decide_eq_decide.mpr
                  ⟨fun h => σ.injective h, fun h => congrArg σ h⟩]
  · -- the copy-membership filter transports pointwise
    rw [decide_eq_decide.mpr (Fold.mem_relComp_transport σ (symCross_transport σ adj χ) v x)]

theorem holHas_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) (c : Nat) :
    holHas (relabelAdj σ adj) (transportColouring σ χ) (σ v) c = holHas adj χ v c := by
  unfold holHas
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨t₁, -, h₁⟩
    obtain ⟨t₂, -, h₂⟩ := List.any_eq_true.mp h₁
    refine ⟨σ.symm t₁, List.mem_finRange _, List.any_eq_true.mpr
      ⟨σ.symm t₂, List.mem_finRange _, ?_⟩⟩
    rw [show t₁ = σ (σ.symm t₁) from (σ.apply_symm_apply t₁).symm,
        show t₂ = σ (σ.symm t₂) from (σ.apply_symm_apply t₂).symm,
        walkOk_conj, holMoved_conj] at h₂
    exact h₂
  · rintro ⟨t₁, -, h₁⟩
    obtain ⟨t₂, -, h₂⟩ := List.any_eq_true.mp h₁
    refine ⟨σ t₁, List.mem_finRange _, List.any_eq_true.mpr
      ⟨σ t₂, List.mem_finRange _, ?_⟩⟩
    rw [walkOk_conj, holMoved_conj]
    exact h₂

theorem holSig_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    holSig (relabelAdj σ adj) (transportColouring σ χ) (σ v) = holSig adj χ v := by
  unfold holSig
  exact List.map_congr_left (fun c _ => by rw [holHas_conj])

/-- **★★ THE HOLONOMY KEY IS EQUIVARIANT** — the whole `①` obligation of a force key discharged: the partner
lookups conjugate (`uniqueMem_transport` on the transported component memberships), the walk enumeration and
the copy sweep reindex bijectively, and the indicator signature is canonical by construction. -/
theorem keyEquivariant_holKey : KeyEquivariant (holKey (n := n)) := by
  intro σ adj χ v
  show holSig (relabelAdj σ adj) (transportColouring σ χ) (σ v) = holSig adj χ v
  exact holSig_conj σ adj χ v

/-! ## 7. The evaluation twin — materialised component-id tables

The spec forms recompute `relComp` inside every membership test (trap #1's shape — do not `#eval` them at
`n ≥ 15`). The twin materialises, per key call, two id-tables (`compTbl` — the least member index of each
vertex's component, an INTERNAL id: outputs consult only id-equality, which `compIdx_eq_iff` proves is exactly
component membership) and reads everything off the forced tables. Value-equal (`holSigFast_eq` /
`holKeyFast_eq`), so every theorem transfers. -/

private theorem foldr_min_le (L : List Nat) (x : Nat) (hx : x ∈ L) : L.foldr min n ≤ x := by
  induction L with
  | nil => cases hx
  | cons a t ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hx')

private theorem foldr_min_mem (L : List Nat) (hne : L ≠ []) (hlt : ∀ x ∈ L, x < n) :
    L.foldr min n ∈ L := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a t ih =>
      cases t with
      | nil =>
          show min a ([].foldr min n) ∈ [a]
          rw [List.foldr_nil, min_eq_left (le_of_lt (hlt a (List.mem_cons_self ..)))]
          exact List.mem_cons_self ..
      | cons b t' =>
          have hmem := ih (by simp) (fun x hx => hlt x (List.mem_cons_of_mem a hx))
          show min a ((b :: t').foldr min n) ∈ a :: b :: t'
          rcases le_total a ((b :: t').foldr min n) with h | h
          · rw [min_eq_left h]
            exact List.mem_cons_self ..
          · rw [min_eq_right h]
            exact List.mem_cons_of_mem a hmem

private theorem foldr_min_congr {L L' : List Nat} (hmem : ∀ x, x ∈ L ↔ x ∈ L')
    (hne : L ≠ []) (hlt : ∀ x ∈ L, x < n) : L.foldr min n = L'.foldr min n := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
  have hne' : L' ≠ [] := List.ne_nil_of_mem ((hmem a).mp ha)
  have hlt' : ∀ x ∈ L', x < n := fun x hx => hlt x ((hmem x).mpr hx)
  exact Nat.le_antisymm
    (foldr_min_le L _ ((hmem _).mpr (foldr_min_mem L' hne' hlt')))
    (foldr_min_le L' _ ((hmem _).mp (foldr_min_mem L hne hlt)))

/-- The component id: the least member index — INTERNAL (outputs consult only id-equality). -/
def compIdx (rel : Fin n → Fin n → Bool) (u : Fin n) : Nat :=
  ((relComp rel u).map Fin.val).foldr min n

/-- **★ Ids test exactly component membership** (for a symmetric relation) — the well-definedness that lets
the twin replace every `relComp` membership scan with an `O(1)` id comparison. -/
theorem compIdx_eq_iff (rel : Fin n → Fin n → Bool) (hsym : ∀ a b, rel a b = rel b a)
    (v w : Fin n) : compIdx rel v = compIdx rel w ↔ w ∈ relComp rel v := by
  have hmemv : ∀ u : Fin n, compIdx rel u ∈ (relComp rel u).map Fin.val := fun u =>
    foldr_min_mem _ (List.ne_nil_of_mem (List.mem_map_of_mem (mem_relComp_self rel u)))
      (fun x hx => by
        obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
        exact m.isLt)
  constructor
  · intro hEq
    obtain ⟨m, hm, hmv⟩ := List.mem_map.mp (hmemv v)
    obtain ⟨m', hm', hmv'⟩ := List.mem_map.mp (hmemv w)
    have hmm : m = m' := Fin.val_injective (by rw [hmv, hmv', hEq])
    subst hmm
    exact mem_relComp_trans rel hm (mem_relComp_symm rel hsym hm')
  · intro hw
    unfold compIdx
    refine foldr_min_congr (fun x => ?_)
      (List.ne_nil_of_mem (List.mem_map_of_mem (mem_relComp_self rel v)))
      (fun x hx => by
        obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
        exact m.isLt)
    rw [List.mem_map, List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, (mem_relComp_congr rel hsym hw m).mpr hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, (mem_relComp_congr rel hsym hw m).mp hm, rfl⟩

/-- The forced id-table (data, not a function — trap #1). -/
def compTbl (rel : Fin n → Fin n → Bool) : Vector Nat n :=
  Vector.ofFn (compIdx rel)

theorem compTbl_get (rel : Fin n → Fin n → Bool) (u : Fin n) :
    (compTbl rel).get u = compIdx rel u := by
  simp [compTbl, Vector.get]

/-- Table-level partner lookup (`c` = the target copy's id). -/
def pfT (sT cT : Vector Nat n) (x : Fin n) (c : Nat) : Option (Fin n) :=
  Deck.uniqueFilter (fun w => decide (sT.get w = sT.get x) && decide (cT.get w = c))

/-- Table-level walk validity. -/
def walkOkT (cT : Vector Nat n) (cv : Nat) (t₁ t₂ : Fin n) : Bool :=
  !decide (cT.get t₁ = cv) && !decide (cT.get t₂ = cv) && !decide (cT.get t₂ = cT.get t₁)

/-- Table-level holonomy moved-count. -/
def holMovedT (sT cT : Vector Nat n) (cv : Nat) (t₁ t₂ : Fin n) : Nat :=
  ((List.finRange n).filter (fun x => decide (cT.get x = cv))).countP (fun x =>
    match pfT sT cT x (cT.get t₁) with
    | none => true
    | some y₁ =>
        match pfT sT cT y₁ (cT.get t₂) with
        | none => true
        | some y₂ =>
            match pfT sT cT y₂ cv with
            | none => true
            | some y₃ => !decide (y₃ = x))

private theorem pfT_eq (adj : AdjMatrix n) (χ : Colouring n) (x t : Fin n) :
    pfT (compTbl (symSame adj χ)) (compTbl (symCross adj χ)) x
        ((compTbl (symCross adj χ)).get t)
      = partnerTo adj χ x t := by
  unfold pfT partnerTo
  rw [Deck.uniqueFilter_eq_uniqueMem]
  congr 1
  funext w
  rw [compTbl_get, compTbl_get, compTbl_get, compTbl_get,
      decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symSame_symm adj χ) x w)),
      decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symCross_symm adj χ) t w))]

private theorem walkOkT_eq (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) :
    walkOkT (compTbl (symCross adj χ)) ((compTbl (symCross adj χ)).get v) t₁ t₂
      = walkOk adj χ v t₁ t₂ := by
  unfold walkOkT walkOk
  rw [compTbl_get, compTbl_get, compTbl_get,
      decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symCross_symm adj χ) v t₁)),
      decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symCross_symm adj χ) v t₂)),
      decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symCross_symm adj χ) t₁ t₂))]

private theorem tbl_filter_eq (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (List.finRange n).filter
        (fun x => decide ((compTbl (symCross adj χ)).get x = (compTbl (symCross adj χ)).get v))
      = (List.finRange n).filter (fun x => decide (x ∈ relComp (symCross adj χ) v)) := by
  refine List.filter_congr (fun x _ => ?_)
  rw [compTbl_get, compTbl_get]
  exact decide_eq_decide.mpr (eq_comm.trans (compIdx_eq_iff _ (symCross_symm adj χ) v x))

private theorem holMovedT_eq (adj : AdjMatrix n) (χ : Colouring n) (v t₁ t₂ : Fin n) :
    holMovedT (compTbl (symSame adj χ)) (compTbl (symCross adj χ))
        ((compTbl (symCross adj χ)).get v) t₁ t₂
      = holMoved adj χ v t₁ t₂ := by
  unfold holMovedT holMoved
  rw [tbl_filter_eq]
  congr 1
  funext x
  simp only [pfT_eq]

private theorem any_walkVals_eq_holHas (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n)
    (c : Nat) :
    (((List.finRange n).flatMap (fun t₁ => (List.finRange n).filterMap (fun t₂ =>
        if walkOk adj χ v t₁ t₂ then some (holMoved adj χ v t₁ t₂) else none))).any
      (fun m => decide (m = c))) = holHas adj χ v c := by
  unfold holHas
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨m, hm, hmc⟩
    obtain ⟨t₁, ht₁, hm₁⟩ := List.mem_flatMap.mp hm
    obtain ⟨t₂, ht₂, hm₂⟩ := List.mem_filterMap.mp hm₁
    refine ⟨t₁, ht₁, List.any_eq_true.mpr ⟨t₂, ht₂, ?_⟩⟩
    by_cases hok : walkOk adj χ v t₁ t₂
    · rw [if_pos hok] at hm₂
      rw [hok, Bool.true_and, Option.some.inj hm₂]
      exact hmc
    · rw [if_neg hok] at hm₂
      cases hm₂
  · rintro ⟨t₁, ht₁, h₁⟩
    obtain ⟨t₂, ht₂, h₂⟩ := List.any_eq_true.mp h₁
    rw [Bool.and_eq_true] at h₂
    refine ⟨holMoved adj χ v t₁ t₂,
      List.mem_flatMap.mpr ⟨t₁, ht₁, List.mem_filterMap.mpr ⟨t₂, ht₂, by rw [if_pos h₂.1]⟩⟩,
      h₂.2⟩

/-- **The runnable signature** — two forced id-tables per call, then `O(1)` reads everywhere. -/
def holSigFast (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  let sT := compTbl (symSame adj χ)
  let cT := compTbl (symCross adj χ)
  let cv := cT.get v
  let vals := (List.finRange n).flatMap (fun t₁ => (List.finRange n).filterMap (fun t₂ =>
    if walkOkT cT cv t₁ t₂ then some (holMovedT sT cT cv t₁ t₂) else none))
  (List.range (n + 1)).map (fun c => if vals.any (fun m => decide (m = c)) then 0 else 1)

/-- **The runnable signature computes exactly the reasoned-about one.** -/
theorem holSigFast_eq (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    holSigFast adj χ v = holSig adj χ v := by
  unfold holSigFast holSig
  simp only [walkOkT_eq, holMovedT_eq]
  exact List.map_congr_left (fun c _ => by rw [any_walkVals_eq_holHas])

/-- The runnable key — value-equal to `holKey` (`holKeyFast_eq`), so every theorem transfers. -/
def holKeyFast : Key n := fun adj χ v =>
  (holSigFast adj χ v, n * n * n * n * n)

theorem holKeyFast_eq : (holKeyFast : Key n) = holKey := by
  funext adj χ v
  show (holSigFast adj χ v, n * n * n * n * n) = (holSig adj χ v, n * n * n * n * n)
  rw [holSigFast_eq]

theorem keyEquivariant_holKeyFast : KeyEquivariant (holKeyFast (n := n)) := by
  rw [holKeyFast_eq]
  exact keyEquivariant_holKey

/-! ## 8. ★★★ THE CAPSTONES — no carried hypotheses -/

/-- **★★★ The pure-force canonizer over the holonomy key** — sound, iso-invariant, and it always answers. -/
theorem holKey_canonizer :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n))
          (Force.forceBy (holKeyFast (n := n))))
      ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n))
          (Force.forceBy (holKeyFast (n := n))) adj ≠ none :=
  Force.force_canonizer_fast keyEquivariant_holKeyFast

/-- **★★★ THE F3a CANONIZER OF RECORD for the fold family (guarded blind object)**: force = the holonomy key
(separates WL-merged distinguishable copies), consume = `foldSupply ++ deckSupply` (collapses the kept
orbit). -/
theorem holKey_foldDeck_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (holKeyFast (n := n))
          (Deck.appendSupply (Fold.foldSupply (n := n)) (Deck.deckSupply (n := n)))))) :=
  SupplyTransport.guarded_mixed_canonizer keyEquivariant_holKeyFast
    (Deck.supplyEquivariant_appendSupply Fold.gensEquivariant_foldSupply
      Deck.gensEquivariant_deckSupply)

/-- **★★★ The FUSED (resolver-aware) mirror** — the selector probes every cell with the same force + supply
pair. -/
theorem holKey_foldDeck_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (holKeyFast (n := n))
          (Deck.appendSupply (Fold.foldSupply (n := n)) (Deck.deckSupply (n := n))))) :=
  Select.selNode_canonizer keyEquivariant_holKeyFast
    (Deck.supplyEquivariant_appendSupply Fold.gensEquivariant_foldSupply
      Deck.gensEquivariant_deckSupply)

end Hol
end ChainDescent
