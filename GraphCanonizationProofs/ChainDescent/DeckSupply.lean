import ChainDescent.FoldSupply

/-!
# `F2b` — `deckSupply` : the propagation harvest (deck transformations of ANY order)

## Why F2a is not enough (`docs/chain-descent-fold-tower-plan.md` §4b)

Every consume-side constructor so far emits **involutions only**: `matchCol`'s rank swap, F1's support-local
matcher, F2a's fiber-wise copy swap, and the C#'s `CopySwapAut`/`BuildParallelMatching` (the doubling peel is
`s % 2 ≠ 0 → null` by construction). But a `Z_s` tower with odd `s` — a voltage cover whose deck group is cyclic
of odd order, with orientation-rigid gadgets — has **no involutions in `Aut` at all**: the generator the cell
needs is an order-`s` rotation. Force cannot substitute (the cell is one `Aut`-orbit and an equivariant key is
constant on orbits, `keyV_aut_invariant`). This is the arbitrary-arity gap, and it is why "F2 closes the `Z_pᵏ`
gauge" was overstated for odd `p`.

## The supply

`deckSupply` seeds every branch-cell pair `(u₁ ↦ u₂)` and runs **constraint propagation**: an unassigned vertex
is forced exactly when a *unique* candidate matches its colour and agrees — edges, non-edges, full weight
equality, injectivity — with **every already-assigned vertex**; `n` rounds; then the two-sided-inverse gate
(forward + reverse propagation) builds the `Equiv.Perm`, and `Consume.verified` re-checks `IsColAut` as always.
No choice is ever made (standing trap #7): forcing fires only on unique candidates, and the seed enumeration is
the whole cell. This generalizes the C# induced-4-cycle rule (arc-consistency including non-edges is a strict
superset of its constraints) and emits generators of **any order** — measured: the order-3 rotation of a `Z₃`
voltage ring and the order-`s` rotations of weighted cycles `C_{3s}`, all `n^{O(1)}` with **no refinement**.

* **Soundness** (`propagate_sound`): any colour-automorphism `ρ` extending the seed satisfies every forcing
  constraint, so each forced value equals `ρ`'s — the invariant `m ⊆ ρ` survives every round. Corollary
  (`deckCand_eq_of_isColAut`): when both propagations complete, the candidate **is** `ρ` — and hence at most one
  automorphism extends a completed seed.
* **Equivariance** (`gensEquivariant_deckSupply`): the forcing rule is a structural function of `(adj, χ)`;
  `candPred`/`uniqueMem`/rounds all transport (`mconj`), so the emitted set conjugates — feeding both
  `SupplyTransport.guarded_mixed_canonizer` and the fused `Select.selNode_canonizer`.
* **Firing is graded and measured, not claimed**: propagation completes exactly when forcing reaches local
  uniqueness everywhere — guaranteed-in-practice for regular deck actions over rigid cores (towers of any arity
  and height: the full order-`p^k` rotation is constructed in ONE propagation), measured per family
  (`Regression` §11, `PerformanceTest` §9). A seed whose stabilizer is nontrivial (e.g. per-copy twin gauges —
  a *wreath*, not a ring) stalls and emits nothing: correct, and outside the linear-over-a-ring leg by design.

## The evaluation twins (trap #1, hit live AGAIN this build)

A round must be **data → data** (`roundVecD : Vector _ n → Vector _ n`, the `Refine.roundVec` pattern). The
function-typed round (`… → Fin n → Option (Fin n)`) re-materialises its table per lookup and the iterate
compounds it **exponentially** — measured: 2 rounds ≈ 1 s, 9 rounds > 300 s at `n = 9`; the Vector form does the
full `n = 15` supply in ~4 s. The bridge back to the spec is `propagateVec_eq` (the `iterate_roundVec` shape),
so every theorem transfers; `uniqueFilter` replaces `uniqueMem`'s `Finset.choose` at evaluation
(`uniqueFilter_eq_uniqueMem`).

## Scope

With F1 + F2a + F2b: symmetric folds any `k` (refinement-visible or blind), and cyclic/abelian deck gauges of
**arbitrary arity and height** wherever seed-stabilizers are trivial. Still F3's (force): ordering genuinely
**distinguishable** copies (here every seed propagation contradicts and emits nothing — the cell is not an
orbit, correctly) and native ring arity. `appendSupply` (§10) composes supplies so ONE object covers the
mirror-tied folds (F2a's) and the cyclic towers (F2b's) simultaneously — guarded on both witness families.
-/

namespace ChainDescent
namespace Deck

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach CellIsOrbit)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.Fold (uniqueMem uniqueMem_eq_some uniqueMem_transport)

variable {n : Nat}

/-! ## 1. The forcing rule — spec form (functions; proofs live here) -/

/-- `w` is a viable image for `v` under partial map `m`: colour agrees, and adjacency (both directions, full
weight equality) plus injectivity agree with **every** already-assigned vertex. Non-edges count: `adj.adj w w₃ =
adj.adj v v₃` for a non-adjacent pair is the `¬F x d` half of the C# 4-cycle rule, generalized. -/
def candPred (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n))
    (v w : Fin n) : Bool :=
  decide (χ w = χ v) &&
  (List.finRange n).all (fun v₃ =>
    match m v₃ with
    | none => true
    | some w₃ =>
        decide (adj.adj w w₃ = adj.adj v v₃) && decide (adj.adj w₃ w = adj.adj v₃ v)
          && !decide (w₃ = w))

/-- One forcing round: an unassigned vertex is assigned iff its candidate set is a singleton (`uniqueMem` — so
no choice is ever made; ambiguity just waits for more assignments, or stalls). -/
def forceRound (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n)) :
    Fin n → Option (Fin n) :=
  fun v =>
    match m v with
    | some w => some w
    | none => uniqueMem (candPred adj χ m v)

/-- The seed: `u₁ ↦ u₂`, nothing else. -/
def seedMap (u₁ u₂ : Fin n) : Fin n → Option (Fin n) :=
  fun v => if v = u₁ then some u₂ else none

/-- `n` forcing rounds from the seed (`n` suffices: rounds are monotone and a round that assigns nothing is a
fixpoint — no convergence proof is needed, every statement is relative to what this computes). -/
def propagate (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Fin n → Option (Fin n) :=
  (forceRound adj χ)^[n] (seedMap u₁ u₂)

/-- The candidate map: propagated image where assigned, identity elsewhere (junk is caught by the gates). -/
def deckFun (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) (v : Fin n) : Fin n :=
  (propagate adj χ u₁ u₂ v).getD v

/-- **The propagation candidate**: forward and reverse propagations must be two-sided inverses (decidable);
`Consume.verified` still re-checks `IsColAut`. A stalled or contradictory propagation simply fails the gate. -/
def deckCand (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  if h : (∀ v, deckFun adj χ u₂ u₁ (deckFun adj χ u₁ u₂ v) = v)
       ∧ (∀ v, deckFun adj χ u₁ u₂ (deckFun adj χ u₂ u₁ v) = v) then
    some ⟨deckFun adj χ u₁ u₂, deckFun adj χ u₂ u₁, h.1, h.2⟩
  else none

/-! ## 2. The evaluation twins — Vector-state rounds (data → data; the `roundVec` pattern) -/

/-- List-based unique lookup — value-equal to `uniqueMem` (`uniqueFilter_eq_uniqueMem`), without the
`Finset.choose`/`∃!`-decide overhead at evaluation. -/
def uniqueFilter (P : Fin n → Bool) : Option (Fin n) :=
  match (List.finRange n).filter P with
  | [w] => some w
  | _ => none

theorem uniqueFilter_eq_uniqueMem (P : Fin n → Bool) : uniqueFilter P = uniqueMem P := by
  by_cases h : ∃! w : Fin n, P w = true
  · obtain ⟨w, hw, hu⟩ := h
    have hfil : (List.finRange n).filter P = [w] := by
      have hmem : w ∈ (List.finRange n).filter P :=
        List.mem_filter.mpr ⟨List.mem_finRange w, hw⟩
      have hall : ∀ x ∈ (List.finRange n).filter P, x = w :=
        fun x hx => hu x (List.mem_filter.mp hx).2
      have hnd : ((List.finRange n).filter P).Nodup := (List.nodup_finRange n).filter _
      cases hcase : (List.finRange n).filter P with
      | nil =>
          rw [hcase] at hmem
          cases hmem
      | cons a t =>
          have ha : a = w := hall a (by rw [hcase]; exact List.mem_cons_self ..)
          cases t with
          | nil => rw [ha]
          | cons b t' =>
              exfalso
              have hb : b = w := hall b (by
                rw [hcase]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
              rw [hcase] at hnd
              exact (List.nodup_cons.mp hnd).1 ((ha.trans hb.symm) ▸ List.mem_cons_self ..)
    unfold uniqueFilter
    rw [hfil, uniqueMem_eq_some hw hu]
  · have hnone : uniqueMem P = none := by rw [uniqueMem, dif_neg h]
    unfold uniqueFilter
    rw [hnone]
    cases hcase : (List.finRange n).filter P with
    | nil => rfl
    | cons a t =>
        cases t with
        | nil =>
            exfalso
            apply h
            refine ⟨a, (List.mem_filter.mp (hcase ▸ List.mem_cons_self ..)).2, fun x hx => ?_⟩
            have hxmem : x ∈ (List.finRange n).filter P :=
              List.mem_filter.mpr ⟨List.mem_finRange x, hx⟩
            rw [hcase] at hxmem
            simpa using hxmem
        | cons b t' => rfl

/-- Vector-state candidate predicate — all reads are `.get` on forced data. -/
def candPredV (adj : AdjMatrix n) (χ : Colouring n) (m : Vector (Option (Fin n)) n)
    (v w : Fin n) : Bool :=
  decide (χ w = χ v) &&
  (List.finRange n).all (fun v₃ =>
    match m.get v₃ with
    | none => true
    | some w₃ =>
        decide (adj.adj w w₃ = adj.adj v v₃) && decide (adj.adj w₃ w = adj.adj v₃ v)
          && !decide (w₃ = w))

/-- One forcing round, **data → data**. The function-typed round is the eta trap (see header): its table
re-materialises per lookup and the iterate compounds it exponentially — measured live this build. -/
def roundVecD (adj : AdjMatrix n) (χ : Colouring n) (m : Vector (Option (Fin n)) n) :
    Vector (Option (Fin n)) n :=
  Vector.ofFn (fun v =>
    match m.get v with
    | some w => some w
    | none => uniqueFilter (candPredV adj χ m v))

/-- The runnable propagation — `propagateVec_eq` transfers every spec theorem. -/
def propagateVec (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Vector (Option (Fin n)) n :=
  (roundVecD adj χ)^[n] (Vector.ofFn (seedMap u₁ u₂))

theorem candPredV_ofFn (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n))
    (v w : Fin n) : candPredV adj χ (Vector.ofFn m) v w = candPred adj χ m v w := by
  unfold candPredV candPred
  have hfun : (fun v₃ : Fin n =>
      match (Vector.ofFn m).get v₃ with
      | none => true
      | some w₃ =>
          decide (adj.adj w w₃ = adj.adj v v₃) && decide (adj.adj w₃ w = adj.adj v₃ v)
            && !decide (w₃ = w))
    = (fun v₃ : Fin n =>
      match m v₃ with
      | none => true
      | some w₃ =>
          decide (adj.adj w w₃ = adj.adj v v₃) && decide (adj.adj w₃ w = adj.adj v₃ v)
            && !decide (w₃ = w)) := by
    funext v₃
    simp [Vector.get]
  rw [hfun]

theorem roundVecD_ofFn (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n)) :
    roundVecD adj χ (Vector.ofFn m) = Vector.ofFn (forceRound adj χ m) := by
  apply Vector.ext
  intro i hi
  simp only [roundVecD, Vector.getElem_ofFn]
  have hg : (Vector.ofFn m).get ⟨i, hi⟩ = m ⟨i, hi⟩ := by
    simp [Vector.get]
  rw [hg]
  unfold forceRound
  cases hm : m ⟨i, hi⟩ with
  | some w => rfl
  | none =>
      rw [uniqueFilter_eq_uniqueMem]
      show uniqueMem (candPredV adj χ (Vector.ofFn m) ⟨i, hi⟩)
          = uniqueMem (candPred adj χ m ⟨i, hi⟩)
      congr 1
      funext w
      exact candPredV_ofFn adj χ m ⟨i, hi⟩ w

theorem iterate_roundVecD (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ (k : Nat) (m : Fin n → Option (Fin n)),
      (roundVecD adj χ)^[k] (Vector.ofFn m) = Vector.ofFn ((forceRound adj χ)^[k] m) := by
  intro k
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, roundVecD_ofFn adj χ m]
      exact ih (forceRound adj χ m)

/-- **The runnable propagation computes exactly the reasoned-about one** — the `warmRefineVec_col_eq` shape. -/
theorem propagateVec_eq (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    propagateVec adj χ u₁ u₂ = Vector.ofFn (propagate adj χ u₁ u₂) := by
  unfold propagateVec propagate
  exact iterate_roundVecD adj χ n (seedMap u₁ u₂)

/-- The runnable candidate — value-equal to `deckCand` (`deckCandFast_eq`); the `let`s bind forced Vectors
(data, not functions), so each propagation runs once per candidate. -/
def deckCandFast (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  let mf := propagateVec adj χ u₁ u₂
  let mb := propagateVec adj χ u₂ u₁
  let f := fun v => (mf.get v).getD v
  let g := fun v => (mb.get v).getD v
  if h : (∀ v, g (f v) = v) ∧ (∀ v, f (g v) = v) then some ⟨f, g, h.1, h.2⟩ else none

theorem deckCandFast_eq (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    deckCandFast adj χ u₁ u₂ = deckCand adj χ u₁ u₂ := by
  have hget : ∀ (a b v : Fin n), ((propagateVec adj χ a b).get v).getD v = deckFun adj χ a b v := by
    intro a b v
    rw [propagateVec_eq]
    unfold deckFun
    simp [Vector.get]
  simp only [deckCandFast, deckCand, hget]

/-! ## 3. Soundness — the invariant `m ⊆ ρ` survives every round -/

/-- One round preserves the invariant: a forced value is the unique constraint-satisfier, and `ρ`'s value
satisfies the constraints (it is an automorphism agreeing with everything assigned), so they coincide. -/
theorem forceRound_sound {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsColAut adj χ ρ) {m : Fin n → Option (Fin n)}
    (hm : ∀ v w, m v = some w → w = ρ v) :
    ∀ v w, forceRound adj χ m v = some w → w = ρ v := by
  intro v w h
  unfold forceRound at h
  cases hmv : m v with
  | some w' =>
      rw [hmv] at h
      exact (Option.some.inj h) ▸ hm v w' hmv
  | none =>
      rw [hmv] at h
      by_cases hex : ∃! x : Fin n, candPred adj χ m v x = true
      · obtain ⟨y, hy, hu⟩ := hex
        rw [uniqueMem_eq_some hy hu] at h
        have hcand : candPred adj χ m v (ρ v) = true := by
          unfold candPred
          rw [Bool.and_eq_true]
          refine ⟨decide_eq_true (hρ.2 v), ?_⟩
          rw [List.all_eq_true]
          intro v₃ _
          cases hm3 : m v₃ with
          | none => simp
          | some w₃ =>
              have hw3 : w₃ = ρ v₃ := hm v₃ w₃ hm3
              have hne : v₃ ≠ v := by
                intro hc
                rw [hc, hmv] at hm3
                cases hm3
              subst hw3
              simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
                decide_eq_false_iff_not]
              exact ⟨⟨hρ.1 v v₃, hρ.1 v₃ v⟩, fun hc => hne (ρ.injective hc)⟩
        exact (Option.some.inj h) ▸ (hu (ρ v) hcand).symm
      · rw [uniqueMem, dif_neg hex] at h
        cases h

/-- **★ SOUNDNESS OF THE PROPAGATION.** Everything the propagation assigns agrees with ANY colour-automorphism
extending the seed. (Corollary: at most one automorphism extends a seed whose propagation completes.) -/
theorem propagate_sound {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsColAut adj χ ρ) {u₁ u₂ : Fin n} (hseed : ρ u₁ = u₂) :
    ∀ v w, propagate adj χ u₁ u₂ v = some w → w = ρ v := by
  have hstep : ∀ (k : Nat) (m : Fin n → Option (Fin n)),
      (∀ v w, m v = some w → w = ρ v) →
      ∀ v w, (forceRound adj χ)^[k] m v = some w → w = ρ v := by
    intro k
    induction k with
    | zero => intro m hm; exact hm
    | succ k ih =>
        intro m hm
        rw [Function.iterate_succ_apply]
        exact ih (forceRound adj χ m) (forceRound_sound hρ hm)
  refine hstep n (seedMap u₁ u₂) ?_
  intro v w h
  unfold seedMap at h
  by_cases hv : v = u₁
  · rw [if_pos hv] at h
    subst hv
    exact (Option.some.inj h) ▸ hseed.symm
  · rw [if_neg hv] at h
    cases h

/-- The seed survives every round (rounds are monotone on assignments). -/
theorem propagate_seed (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    propagate adj χ u₁ u₂ u₁ = some u₂ := by
  unfold propagate
  have hkeep : ∀ (k : Nat) (m : Fin n → Option (Fin n)) (v w : Fin n),
      m v = some w → (forceRound adj χ)^[k] m v = some w := by
    intro k
    induction k with
    | zero => intro m v w h; exact h
    | succ k ih =>
        intro m v w h
        rw [Function.iterate_succ_apply]
        refine ih _ v w ?_
        unfold forceRound
        rw [h]
  exact hkeep n _ u₁ u₂ (by unfold seedMap; rw [if_pos rfl])

/-- **★★ THE RECONSTRUCTION.** If some colour-automorphism `ρ` extends the seed and both propagations complete,
the candidate is exactly `ρ` — the hypotheses are the cover geometry (regular deck action ⟹ unique extension ⟹
forcing can complete), and completion itself is decidable and measured, never assumed. -/
theorem deckCand_eq_of_isColAut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    {u₁ u₂ : Fin n} (hρ : IsColAut adj χ ρ) (hseed : ρ u₁ = u₂)
    (hf : ∀ v, (propagate adj χ u₁ u₂ v).isSome)
    (hb : ∀ v, (propagate adj χ u₂ u₁ v).isSome) :
    deckCand adj χ u₁ u₂ = some ρ := by
  have hfe : ∀ v, deckFun adj χ u₁ u₂ v = ρ v := by
    intro v
    unfold deckFun
    cases hp : propagate adj χ u₁ u₂ v with
    | none => exact absurd (hp ▸ hf v) (by simp)
    | some w => simp [propagate_sound hρ hseed v w hp]
  have hbe : ∀ v, deckFun adj χ u₂ u₁ v = ρ⁻¹ v := by
    intro v
    unfold deckFun
    cases hp : propagate adj χ u₂ u₁ v with
    | none => exact absurd (hp ▸ hb v) (by simp)
    | some w =>
        have hseed' : ρ⁻¹ u₂ = u₁ := by
          rw [← hseed]
          exact ρ.symm_apply_apply u₁
        simp [propagate_sound hρ.inv hseed' v w hp]
  have hcheck : (∀ v, deckFun adj χ u₂ u₁ (deckFun adj χ u₁ u₂ v) = v)
      ∧ (∀ v, deckFun adj χ u₁ u₂ (deckFun adj χ u₂ u₁ v) = v) := by
    constructor
    · intro v
      rw [hfe, hbe]
      exact ρ.symm_apply_apply v
    · intro v
      rw [hbe, hfe]
      exact ρ.apply_symm_apply v
  rw [deckCand, dif_pos hcheck]
  exact congrArg some (Equiv.ext hfe)

/-! ## 4. Equivariance of the constructor -/

/-- Conjugated partial map: the transported assignment state. -/
def mconj (σ : Equiv.Perm (Fin n)) (m : Fin n → Option (Fin n)) : Fin n → Option (Fin n) :=
  fun v => (m (σ.symm v)).map σ

theorem candPred_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (m : Fin n → Option (Fin n)) (v w : Fin n) :
    candPred (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m) (σ v) (σ w)
      = candPred adj χ m v w := by
  unfold candPred
  congr 1
  · simp [transportColouring]
  · rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h v₃ _
      have hh := h (σ v₃) (List.mem_finRange _)
      simp only [mconj, Equiv.symm_apply_apply] at hh
      cases hm3 : m v₃ with
      | none => simp
      | some w₃ =>
          rw [hm3] at hh
          simp only [Option.map_some, relabelAdj_adj, Equiv.symm_apply_apply,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not] at hh
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not]
          exact ⟨hh.1, fun hc => hh.2 (congrArg σ hc)⟩
    · intro h v₃ _
      have hh := h (σ.symm v₃) (List.mem_finRange _)
      simp only [mconj]
      cases hm3 : m (σ.symm v₃) with
      | none => simp
      | some w₃ =>
          rw [hm3] at hh
          simp only [Option.map_some, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not]
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not] at hh
          have hv₃ : v₃ = σ (σ.symm v₃) := (σ.apply_symm_apply v₃).symm
          rw [hv₃]
          simp only [relabelAdj_adj, Equiv.symm_apply_apply]
          exact ⟨hh.1, fun hc => hh.2 (σ.injective hc)⟩

theorem forceRound_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (m : Fin n → Option (Fin n)) :
    forceRound (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m)
      = mconj σ (forceRound adj χ m) := by
  funext x
  show forceRound (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m) x
      = (forceRound adj χ m (σ.symm x)).map σ
  unfold forceRound
  cases hm : m (σ.symm x) with
  | some w =>
      have h1 : mconj σ m x = some (σ w) := by simp [mconj, hm]
      rw [h1]
      rfl
  | none =>
      have h1 : mconj σ m x = none := by simp [mconj, hm]
      rw [h1]
      show uniqueMem (candPred (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m) x)
          = (uniqueMem (candPred adj χ m (σ.symm x))).map σ
      exact uniqueMem_transport σ (fun w => by
        conv_lhs => rw [show x = σ (σ.symm x) from (σ.apply_symm_apply x).symm]
        exact candPred_conj σ adj χ m (σ.symm x) w)

theorem seedMap_conj (σ : Equiv.Perm (Fin n)) (u₁ u₂ : Fin n) :
    seedMap (σ u₁) (σ u₂) = mconj σ (seedMap u₁ u₂) := by
  funext x
  show (if x = σ u₁ then some (σ u₂) else none)
      = ((if σ.symm x = u₁ then some u₂ else none) : Option (Fin n)).map σ
  by_cases hx : x = σ u₁
  · rw [if_pos hx, if_pos (by rw [hx]; exact σ.symm_apply_apply u₁)]
    rfl
  · rw [if_neg hx, if_neg (fun hc => hx ((σ.apply_symm_apply x) ▸ congrArg σ hc))]
    rfl

theorem propagate_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) :
    propagate (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂)
      = mconj σ (propagate adj χ u₁ u₂) := by
  unfold propagate
  rw [seedMap_conj]
  have hiter : ∀ (k : Nat) (m : Fin n → Option (Fin n)),
      (forceRound (relabelAdj σ adj) (transportColouring σ χ))^[k] (mconj σ m)
        = mconj σ ((forceRound adj χ)^[k] m) := by
    intro k
    induction k with
    | zero => intro m; rfl
    | succ k ih =>
        intro m
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          forceRound_conj σ adj χ m, ih (forceRound adj χ m)]
  exact hiter n (seedMap u₁ u₂)

theorem deckFun_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) (x : Fin n) :
    deckFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) x
      = σ (deckFun adj χ u₁ u₂ (σ.symm x)) := by
  unfold deckFun
  rw [propagate_conj]
  simp only [mconj]
  cases propagate adj χ u₁ u₂ (σ.symm x) with
  | none => simp
  | some w => simp

private theorem deck_check_one (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b c d : Fin n) :
    (∀ v, deckFun (relabelAdj σ adj) (transportColouring σ χ) (σ a) (σ b)
        (deckFun (relabelAdj σ adj) (transportColouring σ χ) (σ c) (σ d) v) = v)
      ↔ (∀ v, deckFun adj χ a b (deckFun adj χ c d v) = v) := by
  constructor
  · intro h v
    have hh := h (σ v)
    rw [deckFun_conj, deckFun_conj] at hh
    simp only [Equiv.symm_apply_apply] at hh
    exact σ.injective hh
  · intro h v
    rw [deckFun_conj, deckFun_conj]
    simp only [Equiv.symm_apply_apply]
    rw [h (σ.symm v)]
    exact σ.apply_symm_apply v

/-- The candidate transports up to conjugation, **including its failure mode** — the `swapCand_conj` analogue,
so the supply equivariance proof is the standard one. -/
theorem deckCand_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) :
    deckCand (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂)
      = (deckCand adj χ u₁ u₂).map (fun t => σ * t * σ⁻¹) := by
  unfold deckCand
  by_cases h : (∀ v, deckFun adj χ u₂ u₁ (deckFun adj χ u₁ u₂ v) = v)
      ∧ (∀ v, deckFun adj χ u₁ u₂ (deckFun adj χ u₂ u₁ v) = v)
  · rw [dif_pos h, dif_pos ⟨(deck_check_one σ adj χ u₂ u₁ u₁ u₂).mpr h.1,
      (deck_check_one σ adj χ u₁ u₂ u₂ u₁).mpr h.2⟩, Option.map_some]
    refine congrArg some (Equiv.ext fun x => ?_)
    show deckFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) x
        = σ (deckFun adj χ u₁ u₂ (σ⁻¹ x))
    rw [deckFun_conj]
    rfl
  · rw [dif_neg h, dif_neg (fun hc => h ⟨(deck_check_one σ adj χ u₂ u₁ u₁ u₂).mp hc.1,
      (deck_check_one σ adj χ u₁ u₂ u₂ u₁).mp hc.2⟩)]
    rfl

/-! ## 5. The supply -/

/-- **★ THE PROPAGATION SUPPLY.** Every branch-cell pair seeds a propagation candidate; the two-sided-inverse
gate and `Consume.verified` filter the junk. Cost billed flat at `|cell|² · n⁵` (the naive rounds × scans —
honest for this first implementation). -/
def deckSupply : Supply n := fun adj χ =>
  let B := branches χ
  (B.flatMap (fun u₁ => B.filterMap (fun u₂ => deckCandFast adj χ u₁ u₂)),
   B.length * B.length * (n * n * n * n * n))

theorem mem_gens_deckSupply_iff {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)} :
    g ∈ gens (deckSupply (n := n)) adj χ ↔
      ∃ u₁ ∈ branches χ, ∃ u₂ ∈ branches χ, deckCand adj χ u₁ u₂ = some g := by
  constructor
  · intro hg
    obtain ⟨u₁, h₁, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨u₂, h₂, hc⟩ := List.mem_filterMap.mp hq
    rw [deckCandFast_eq] at hc
    exact ⟨u₁, h₁, u₂, h₂, hc⟩
  · rintro ⟨u₁, h₁, u₂, h₂, hc⟩
    rw [← deckCandFast_eq] at hc
    exact List.mem_flatMap.mpr ⟨u₁, h₁, List.mem_filterMap.mpr ⟨u₂, h₂, hc⟩⟩

/-! ## 6. `①c` — the supply is equivariant -/

/-- **★★ THE PROPAGATION SUPPLY IS EQUIVARIANT** — the pair enumeration is the branch cell (which transports),
and the candidate conjugates (`deckCand_conj`). Forcing consults only structural constraints and canonical
unique lookups, so no representative is ever chosen (standing trap #7). -/
theorem gensEquivariant_deckSupply : GensEquivariant (deckSupply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_deckSupply_iff]
  constructor
  · rintro ⟨u₁, h₁, u₂, h₂, hc⟩
    obtain ⟨v₁, hv₁, rfl⟩ := (hbr u₁).mp h₁
    obtain ⟨v₂, hv₂, rfl⟩ := (hbr u₂).mp h₂
    rw [deckCand_conj] at hc
    rcases hcase : deckCand adj χ v₁ v₂ with _ | t
    · rw [hcase] at hc; simp at hc
    · rw [hcase] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact ⟨t, ⟨v₁, hv₁, v₂, hv₂, hcase⟩, hc.symm⟩
  · rintro ⟨h, ⟨u₁, h₁, u₂, h₂, hc⟩, rfl⟩
    refine ⟨σ u₁, (hbr _).mpr ⟨u₁, h₁, rfl⟩, σ u₂, (hbr _).mpr ⟨u₂, h₂, rfl⟩, ?_⟩
    rw [deckCand_conj, hc]
    rfl

theorem supplyEquivariant_deckSupply : SupplyEquivariant (deckSupply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_deckSupply

/-! ## 7. Firing -/

/-- **Graded firing, per pair:** a verified propagation candidate carrying `u₁` to `u₂` puts the pair into the
verified `WordReach` — and words of caught generators reach the rest (powers of one rotation come free). -/
theorem wordReach_deckSupply {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : Fin n}
    {τ : Equiv.Perm (Fin n)}
    (h₁ : u₁ ∈ branches χ) (h₂ : u₂ ∈ branches χ) (hτ : IsColAut adj χ τ)
    (hcand : deckCand adj χ u₁ u₂ = some τ) (hval : τ u₁ = u₂) :
    WordReach (verified (deckSupply (n := n)) adj χ) u₁ u₂ := by
  have hmem : τ ∈ verified (deckSupply (n := n)) adj χ := by
    refine List.mem_filter.mpr ⟨?_, by simpa using hτ⟩
    exact mem_gens_deckSupply_iff.mpr ⟨u₁, h₁, u₂, h₂, hcand⟩
  have hstep := (Consume.WordReach.refl
    (G := verified (deckSupply (n := n)) adj χ) u₁).step hmem
  rwa [hval] at hstep

/-- **★★★ THE ORACLE FIRES.** If every branch-cell pair is connected by a verified propagation candidate, the
cell is certified as one orbit and `consume` collapses it to a single branch — with **no refinement involved**,
at any generator order (the odd-arity case no other supply reaches). -/
theorem cellIsOrbit_deckSupply {adj : AdjMatrix n} {χ : Colouring n}
    (h : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ τ : Equiv.Perm (Fin n),
      IsColAut adj χ τ ∧ deckCand adj χ u w = some τ ∧ τ u = w) :
    CellIsOrbit (deckSupply (n := n)) adj χ := by
  intro u hu w hw
  obtain ⟨τ, hτ, hcand, hval⟩ := h u hu w hw
  exact wordReach_deckSupply hu hw hτ hcand hval

/-! ## 8. ★★★ THE CAPSTONES — both objects, no carried hypotheses -/

/-- **★★★ The guarded (blind) mixed canonizer over the propagation supply.** -/
theorem deckSupply_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n)) (deckSupply (n := n))))) :=
  SupplyTransport.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    supplyEquivariant_deckSupply

/-- **★★★ The FUSED (resolver-aware) canonizer over the propagation supply.** -/
theorem deckSupply_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (deckSupply (n := n)))) :=
  Select.selNode_canonizer Force.keyEquivariant_lookahead supplyEquivariant_deckSupply

/-! ## 9. Supply concatenation — one supply object, every harvest -/

/-- Concatenate two supplies: generators appended, costs summed. The equivariance obligation splits. -/
def appendSupply (S₁ S₂ : Supply n) : Supply n := fun adj χ =>
  ((S₁ adj χ).1 ++ (S₂ adj χ).1, (S₁ adj χ).2 + (S₂ adj χ).2)

theorem mem_gens_appendSupply_iff {S₁ S₂ : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (appendSupply S₁ S₂) adj χ ↔ g ∈ gens S₁ adj χ ∨ g ∈ gens S₂ adj χ :=
  List.mem_append

theorem gensEquivariant_appendSupply {S₁ S₂ : Supply n}
    (h₁ : GensEquivariant S₁) (h₂ : GensEquivariant S₂) :
    GensEquivariant (appendSupply S₁ S₂) := by
  intro σ adj χ g
  rw [mem_gens_appendSupply_iff, h₁ σ adj χ g, h₂ σ adj χ g]
  constructor
  · rintro (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
    · exact ⟨h, mem_gens_appendSupply_iff.mpr (Or.inl hh), rfl⟩
    · exact ⟨h, mem_gens_appendSupply_iff.mpr (Or.inr hh), rfl⟩
  · rintro ⟨h, hh, rfl⟩
    rcases mem_gens_appendSupply_iff.mp hh with h' | h'
    · exact Or.inl ⟨h, h', rfl⟩
    · exact Or.inr ⟨h, h', rfl⟩

theorem supplyEquivariant_appendSupply {S₁ S₂ : Supply n}
    (h₁ : GensEquivariant S₁) (h₂ : GensEquivariant S₂) :
    SupplyEquivariant (appendSupply S₁ S₂) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant (gensEquivariant_appendSupply h₁ h₂)

/-- **★★★ The fused canonizer over `foldSupply ++ deckSupply`** — ONE supply object covering the mirror-tied
folds (copy swaps) and the cyclic towers (rotations) simultaneously; guarded on both witness families. -/
theorem foldDeckSupply_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (appendSupply (Fold.foldSupply (n := n)) (deckSupply (n := n))))) :=
  Select.selNode_canonizer Force.keyEquivariant_lookahead
    (supplyEquivariant_appendSupply Fold.gensEquivariant_foldSupply gensEquivariant_deckSupply)

end Deck
end ChainDescent
