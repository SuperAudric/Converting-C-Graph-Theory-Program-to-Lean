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

## Build state (2026-07-18, handoff — the STAGED items are the pickup; the proof routes are worked out)

**LANDED (this file, compile-clean, axiom-clean):** §1 `KeySeparates` + the firing theorem
`keepMin_pairwise_aut_of_separates`; §2 the **component-closure lemma set** (`relComp_closed` via the
monotone-rounds pigeonhole, `mem_relComp_self/trans/symm`, `mem_relComp_congr` = copy-designator
well-definedness — for a SYMMETRIC relation, hence §3); §3 the **symmetrized** cell relations
`symSame`/`symCross` (weakly-connected components: `AdjMatrix` guarantees no symmetry, and symmetrizing makes
the closure lemmas unconditional; matches the C#) with `_symm`/`_transport` lemmas; §4 the spec key:
`partnerTo`/`walkOk`/`holMoved`/`holHas`/`holSig`/`holKey`. `holSig` is the **indicator vector over `[0, n]`**
— canonical BY CONSTRUCTION (no sort, no dedup), chosen so equivariance is pure existential reindexing
rather than sorted-permutation plumbing.

**STAGED — the next tranche, in order, with routes:**
1. **`KeyEquivariant holKey`.** Route: `partnerTo_conj` (= `uniqueMem_transport` +
   `mem_relComp_transport` + `symSame_transport`/`symCross_transport` — the `swapFun_conj` pattern);
   `walkOk_conj` (three `decide_eq_decide.mpr (mem_relComp_transport …)` rewrites); `holMoved_conj`
   (`List.countP_filter` to fuse filter into countP, reindex over `finRange` via
   `(finRange n).map σ ~ finRange n` + `List.Perm.countP_eq` + `List.countP_map`, then pointwise cases on
   the `partnerTo_conj`-rewritten match chain, `σ.injective` for the final `decide`); `holHas_conj`
   (`List.any_eq_true` both sides, reindex the two existentials by `σ`/`σ.symm` — no perm plumbing, which
   is what the indicator form buys); `holSig_conj` = `map`-congruence pointwise; `keyEquivariant_holKey`
   is then `holSig_conj` verbatim.
2. **The evaluation twins.** The spec forms recompute `relComp` per membership test — trap #1's shape; do
   NOT `#eval` them at `n ≥ 15` (the F3 probes measured the table form at ~0.5 s for six vertices,
   `n = 30`). Twin design: per key call materialise min-member id-tables
   `compTbl rel := Vector.ofFn (fun v => ((relComp rel v).map Fin.val).foldr min n)` for both relations;
   partner/walk tests by `Nat` id-equality; enumerate walks over the DEDUPED id set (~s² instead of n²
   pairs). Bridges: `compTbl_get_eq_iff : (compTbl rel).get v = (compTbl rel).get w ↔ w ∈ relComp rel v`
   (fold-min of the member-val list is a member and a lower bound, then §2's membership-equivalence), and
   id-pair-walk vs vertex-pair-walk value-set equality via `mem_relComp_congr` — exactly what §2 exists for.
3. **Witness guards + capstones.** Witness = `U3 ⊔ T3` (recipe + measured numbers in plan §5b: U-side
   attains moved-counts `{0, 5}`, T-side `{2, 5}`). ⚠ With the indicator signature the T-side is lex-LEAST
   (indicator 0 at position 0), so expect `keepMin holKeyFast = [19, 24, 29]` (T-pendants) where
   `lookaheadKey` keeps all 6 — and on the T-side `foldSupply` verifies only the (0,1)-swap, so
   `forceThenConsume` lands at 2 there, not 1; the clean `= 1` composite needs the kept side fully
   symmetric (flip the indicator polarity, or guard `≤ 2` honestly). MEASURE FIRST in scratch (standing
   steer), then port the confirmed numbers. Capstones: `force_canonizer` / `guarded_mixed_canonizer` /
   `Select.selNode_canonizer` instances over `holKey`, hypothesis = `keyEquivariant_holKey` only.
4. **F3b (Smith/CRT coset)** stays gated on a measured holonomy-failure witness — plan §5b.
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
exceeds the copy size), of which moved-counts are attained by some valid walk. Full enumeration makes it
representative-free (trap #7); the indicator form makes it **canonical by construction** — no sorting, no
dedup — so equivariance is pure existential reindexing. -/
def holSig (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  (List.range (n + 1)).map (fun c => if holHas adj χ v c then 1 else 0)

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
