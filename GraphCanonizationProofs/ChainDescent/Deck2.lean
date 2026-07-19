import ChainDescent.FoldFast

/-!
# `F2c` — `deck2Supply` : second-seed propagation (the commuting-gauge / mirror-composite constructor)

## Why F2b is not enough (remaining-work §1C item C1; `PerformanceTest` §10, measured 2026-07-18)

`Deck.deckSupply` completes exactly in the trivial-seed-stabilizer regime: forcing fires only on **unique**
candidates, so a cover with a symmetry **commuting** with the seeded one leaves ≥ 2 viable images at some
vertex forever — the propagation stalls and emits nothing. That is not hypothetical: on the twisted triple
cover `T3` (and the `U3 ⊔ T3` union), the T-side gauge — **per-copy mirrors composed through the twisted
matchings** — commutes with every copy swap, so *every* deck seed stalls, `foldSupply`'s unique-partner
lookup is ambiguous on the merged twisted fibers, and the matching supplies are 1-WL-chirality-blind at
every pin. A constructible member of the fold family was unhandled: the end-to-end descent flagged below
the root.

## The supply

`deck2Supply` seeds every branch-cell pair as F2b does, runs the propagation, and — where it stalls — reads
the stalled state's **own ambiguity set** as the second-seed enumeration: every still-unassigned vertex ×
every still-viable candidate (`seconds`, an equivariantly-defined set — nothing is chosen, standing trap
#7). Each second seed is added to the **shared** stalled state (trap #2: the base propagation runs once per
first pair) and forcing continues; a completed continuation passes the bijectivity gate (`permOf`) and
`Consume.verified` re-checks `IsColAut` as always. The mirror composed through the twisted matchings is
exactly what the added constraint forces, cell by cell, around the copy graph.

* **Soundness** (`contFrom_sound` + `setSeed_sound`): the F2b invariant `m ⊆ ρ` is preserved from *any*
  sound state, so it survives the stall + reseed; `deck2Cand_eq_of_isColAut`: if a colour-automorphism
  extends **both** seeds and the continuation completes, the candidate **is** that automorphism.
* **Equivariance** (`gensEquivariant_deck2Supply`): the first-seed enumeration is the branch cell, the
  second-seed enumeration is definable from the stalled state (`mem_seconds_conj`), and both the
  continuation (`contFrom_conj`) and the gate (`permOf_conj`, keyed on the labelling-independent predicate
  `Function.Bijective`) transport.
* **Firing is graded and measured, never claimed**: a second seed resolves exactly the ambiguity a
  *single* commuting symmetry creates (measured: `t3` — fold and deck stall at 3, `deck2Supply` collapses
  to 1, `Regression` §14). A gauge needing `k ≥ 2` *independent* extra decisions per seed (wreath-type
  per-copy gauges, `Z₂ ≀ Z_s`) still stalls — that is remaining-work item C2, the next leg, not this one.

## Cost

Billed flat and honest: `|B|² · (1 + n²) · n⁵` — per first pair, one base propagation (`n⁵`, the F2b bill)
plus ≤ `n²` second-seed continuations at the same bound. Poly, no refinement, no depth parameter.
-/

namespace ChainDescent
namespace Deck2

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach CellIsOrbit)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.Deck (candPred forceRound seedMap propagate mconj candPred_conj forceRound_conj
  candPredV roundVecD propagateVec propagateVec_eq iterate_roundVecD appendSupply)

variable {n : Nat}

/-! ## 1. The second-seed machinery — spec forms -/

/-- Continue forcing from an arbitrary partial state (`Deck.propagate` is `contFrom` of the seed map). -/
def contFrom (adj : AdjMatrix n) (χ : Colouring n) (m₀ : Fin n → Option (Fin n)) :
    Fin n → Option (Fin n) :=
  (forceRound adj χ)^[n] m₀

/-- Add a second seed onto a (stalled) state. -/
def setSeed (m : Fin n → Option (Fin n)) (v₁ v₂ : Fin n) : Fin n → Option (Fin n) :=
  fun v => if v = v₁ then some v₂ else m v

/-- **The second-seed enumeration**: every unassigned vertex × every currently-viable candidate — the
stalled state's own ambiguity set. The whole set is enumerated (no vertex or candidate is chosen, standing
trap #7), and it is empty exactly when the first propagation completed. -/
def seconds (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n)) :
    List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun v₁ =>
    match m v₁ with
    | some _ => []
    | none => ((List.finRange n).filter (fun v₂ => candPred adj χ m v₁ v₂)).map (fun v₂ => (v₁, v₂))

theorem mem_seconds_iff {adj : AdjMatrix n} {χ : Colouring n} {m : Fin n → Option (Fin n)}
    {p : Fin n × Fin n} :
    p ∈ seconds adj χ m ↔ m p.1 = none ∧ candPred adj χ m p.1 p.2 = true := by
  unfold seconds
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨v₁, -, hp⟩
    cases hm : m v₁ with
    | some w => rw [hm] at hp; cases hp
    | none =>
        rw [hm] at hp
        obtain ⟨v₂, hv₂, rfl⟩ := List.mem_map.mp hp
        exact ⟨hm, (List.mem_filter.mp hv₂).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p.1, List.mem_finRange _, ?_⟩
    rw [h1]
    exact List.mem_map.mpr ⟨p.2, List.mem_filter.mpr ⟨List.mem_finRange _, h2⟩, rfl⟩

/-! ## 2. The bijectivity gate — a computable `Perm` from a completed table -/

/-- Computable inverse-by-table: the first preimage in enumeration order. The gate below makes the order
irrelevant — it passes exactly when `f` is bijective, and then `invFun f` *is* the inverse. -/
def invFun (f : Fin n → Fin n) : Fin n → Fin n := fun w =>
  ((List.finRange n).find? (fun v => f v = w)).getD w

/-- The gated permutation: `some ⟨f, f⁻¹⟩` iff `f` is bijective (`bijective_of_gate`/`gate_of_bijective`),
`none` otherwise. Replaces F2b's second (backward) propagation — one table inversion instead. -/
def permOf (f : Fin n → Fin n) : Option (Equiv.Perm (Fin n)) :=
  if h : (∀ v, invFun f (f v) = v) ∧ (∀ w, f (invFun f w) = w) then
    some ⟨f, invFun f, h.1, h.2⟩
  else none

theorem gate_of_bijective {f : Fin n → Fin n} (hb : Function.Bijective f) :
    (∀ v, invFun f (f v) = v) ∧ (∀ w, f (invFun f w) = w) := by
  have hfind : ∀ w : Fin n, ∃ x, (List.finRange n).find? (fun v => f v = w) = some x ∧ f x = w := by
    intro w
    obtain ⟨v, hv⟩ := hb.2 w
    have hsome : ((List.finRange n).find? (fun v' => f v' = w)).isSome := by
      rw [List.find?_isSome]
      exact ⟨v, List.mem_finRange v, by simp [hv]⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨x, hx, by simpa using List.find?_some hx⟩
  constructor
  · intro v
    obtain ⟨x, hx, hfx⟩ := hfind (f v)
    unfold invFun
    rw [hx]
    simpa using hb.1 hfx
  · intro w
    obtain ⟨x, hx, hfx⟩ := hfind w
    unfold invFun
    rw [hx]
    simpa using hfx

theorem bijective_of_gate {f : Fin n → Fin n}
    (h : (∀ v, invFun f (f v) = v) ∧ (∀ w, f (invFun f w) = w)) :
    Function.Bijective f :=
  ⟨fun a b hab => by rw [← h.1 a, hab, h.1 b], fun w => ⟨invFun f w, h.2 w⟩⟩

/-- Reconstruction through the gate: a table that pointwise **is** a permutation gates to exactly it. -/
theorem permOf_eq_some_of_eq {f : Fin n → Fin n} {ρ : Equiv.Perm (Fin n)}
    (h : ∀ v, f v = ρ v) : permOf f = some ρ := by
  have hb : Function.Bijective f := by
    have hf : f = fun v => ρ v := funext h
    rw [hf]
    exact ρ.bijective
  rw [permOf, dif_pos (gate_of_bijective hb)]
  exact congrArg some (Equiv.ext h)

theorem bijective_conj_iff (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    Function.Bijective (fun x => σ (f (σ.symm x))) ↔ Function.Bijective f := by
  constructor
  · intro h
    have hf : f = fun v => σ.symm ((fun x => σ (f (σ.symm x))) (σ v)) := by
      funext v; simp
    rw [hf]
    exact σ.symm.bijective.comp (h.comp σ.bijective)
  · intro h
    exact σ.bijective.comp (h.comp σ.symm.bijective)

/-- The gate transports, **including its failure mode**: bijectivity is labelling-independent, and on
success both sides compute the unique inverse. -/
theorem permOf_conj (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    permOf (fun x => σ (f (σ.symm x))) = (permOf f).map (fun t => σ * t * σ⁻¹) := by
  by_cases hb : Function.Bijective f
  · rw [permOf, dif_pos (gate_of_bijective ((bijective_conj_iff σ f).mpr hb)),
      permOf, dif_pos (gate_of_bijective hb), Option.map_some]
    refine congrArg some (Equiv.ext fun x => ?_)
    show σ (f (σ.symm x)) = (σ * ⟨f, invFun f, _, _⟩ * σ⁻¹) x
    rfl
  · rw [permOf, dif_neg (fun hc => hb ((bijective_conj_iff σ f).mp (bijective_of_gate hc))),
      permOf, dif_neg (fun hc => hb (bijective_of_gate hc)), Option.map_none]

/-! ## 3. The candidate -/

/-- The two-seed forced table: continue the first propagation with the second seed added, identity-fill
(junk is caught by the gate + verification). -/
def deck2Fun (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ v₁ v₂ : Fin n) : Fin n → Fin n :=
  fun x => ((contFrom adj χ (setSeed (propagate adj χ u₁ u₂) v₁ v₂)) x).getD x

/-- **The second-seed candidate**: gate the completed table into a `Perm`; `Consume.verified` still
re-checks `IsColAut`. -/
def deck2Cand (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ v₁ v₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  permOf (deck2Fun adj χ u₁ u₂ v₁ v₂)

/-! ## 4. Soundness — the invariant survives the stall + reseed -/

theorem contFrom_sound {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsColAut adj χ ρ) {m₀ : Fin n → Option (Fin n)}
    (hm : ∀ v w, m₀ v = some w → w = ρ v) :
    ∀ v w, contFrom adj χ m₀ v = some w → w = ρ v := by
  have hstep : ∀ (k : Nat) (m : Fin n → Option (Fin n)),
      (∀ v w, m v = some w → w = ρ v) →
      ∀ v w, (forceRound adj χ)^[k] m v = some w → w = ρ v := by
    intro k
    induction k with
    | zero => intro m hm'; exact hm'
    | succ k ih =>
        intro m hm'
        rw [Function.iterate_succ_apply]
        exact ih (forceRound adj χ m) (Deck.forceRound_sound hρ hm')
  exact hstep n m₀ hm

theorem setSeed_sound {m : Fin n → Option (Fin n)} {ρ : Equiv.Perm (Fin n)} {v₁ v₂ : Fin n}
    (hm : ∀ v w, m v = some w → w = ρ v) (h2 : ρ v₁ = v₂) :
    ∀ v w, setSeed m v₁ v₂ v = some w → w = ρ v := by
  intro v w h
  unfold setSeed at h
  by_cases hv : v = v₁
  · rw [if_pos hv] at h
    subst hv
    exact (Option.some.inj h) ▸ h2.symm
  · rw [if_neg hv] at h
    exact hm v w h

/-- **★★ THE RECONSTRUCTION.** If a colour-automorphism `ρ` extends BOTH seeds and the continued
propagation completes, the candidate **is** `ρ`. The second-seed hypothesis is exactly the ambiguity being
resolved: `ρ v₁ = v₂` picks which commuting extension the continuation forces. -/
theorem deck2Cand_eq_of_isColAut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    {u₁ u₂ v₁ v₂ : Fin n}
    (hρ : IsColAut adj χ ρ) (h1 : ρ u₁ = u₂) (h2 : ρ v₁ = v₂)
    (hc : ∀ v, (contFrom adj χ (setSeed (propagate adj χ u₁ u₂) v₁ v₂) v).isSome) :
    deck2Cand adj χ u₁ u₂ v₁ v₂ = some ρ := by
  have hsound : ∀ v w, contFrom adj χ (setSeed (propagate adj χ u₁ u₂) v₁ v₂) v = some w → w = ρ v :=
    contFrom_sound hρ (setSeed_sound (Deck.propagate_sound hρ h1) h2)
  unfold deck2Cand
  refine permOf_eq_some_of_eq fun v => ?_
  unfold deck2Fun
  cases hp : contFrom adj χ (setSeed (propagate adj χ u₁ u₂) v₁ v₂) v with
  | none => exact absurd (hp ▸ hc v) (by simp)
  | some w => simp [hsound v w hp]

/-! ## 5. Equivariance of the constructor -/

theorem contFrom_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (m : Fin n → Option (Fin n)) :
    contFrom (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m)
      = mconj σ (contFrom adj χ m) := by
  unfold contFrom
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
  exact hiter n m

theorem setSeed_conj (σ : Equiv.Perm (Fin n)) (m : Fin n → Option (Fin n)) (v₁ v₂ : Fin n) :
    setSeed (mconj σ m) (σ v₁) (σ v₂) = mconj σ (setSeed m v₁ v₂) := by
  funext x
  show (if x = σ v₁ then some (σ v₂) else mconj σ m x)
      = ((if σ.symm x = v₁ then some v₂ else m (σ.symm x)) : Option (Fin n)).map σ
  by_cases hx : x = σ v₁
  · rw [if_pos hx, if_pos (by rw [hx]; exact σ.symm_apply_apply v₁)]
    rfl
  · rw [if_neg hx, if_neg (fun hc => hx ((σ.apply_symm_apply x) ▸ congrArg σ hc))]
    rfl

theorem mem_seconds_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (m : Fin n → Option (Fin n)) (p : Fin n × Fin n) :
    p ∈ seconds (relabelAdj σ adj) (transportColouring σ χ) (mconj σ m)
      ↔ ∃ q ∈ seconds adj χ m, (σ q.1, σ q.2) = p := by
  rw [mem_seconds_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(σ.symm p.1, σ.symm p.2), mem_seconds_iff.mpr ⟨?_, ?_⟩, by simp⟩
    · have := h1
      simp only [mconj, Option.map_eq_none_iff] at this
      exact this
    · have hc := candPred_conj σ adj χ m (σ.symm p.1) (σ.symm p.2)
      rw [σ.apply_symm_apply, σ.apply_symm_apply] at hc
      rw [← hc]
      exact h2
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2⟩ := mem_seconds_iff.mp hq
    constructor
    · simp [mconj, h1]
    · have hc := candPred_conj σ adj χ m q.1 q.2
      rw [hc]
      exact h2

theorem deck2Fun_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ v₁ v₂ x : Fin n) :
    deck2Fun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) (σ v₁) (σ v₂) x
      = σ (deck2Fun adj χ u₁ u₂ v₁ v₂ (σ.symm x)) := by
  unfold deck2Fun
  rw [Deck.propagate_conj, setSeed_conj, contFrom_conj]
  simp only [mconj]
  cases contFrom adj χ (setSeed (propagate adj χ u₁ u₂) v₁ v₂) (σ.symm x) with
  | none => simp
  | some w => simp

/-- The candidate transports up to conjugation, including its failure mode. -/
theorem deck2Cand_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ v₁ v₂ : Fin n) :
    deck2Cand (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) (σ v₁) (σ v₂)
      = (deck2Cand adj χ u₁ u₂ v₁ v₂).map (fun t => σ * t * σ⁻¹) := by
  unfold deck2Cand
  have hfun : deck2Fun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) (σ v₁) (σ v₂)
      = fun x => σ (deck2Fun adj χ u₁ u₂ v₁ v₂ (σ.symm x)) :=
    funext (deck2Fun_conj σ adj χ u₁ u₂ v₁ v₂)
  rw [hfun, permOf_conj]

/-! ## 6. The evaluation form — shared base state (trap #2), Vector rounds (trap #1) -/

/-- Second-seed enumeration over the Vector state. -/
def secondsV (adj : AdjMatrix n) (χ : Colouring n) (mf : Vector (Option (Fin n)) n) :
    List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun v₁ =>
    match mf.get v₁ with
    | some _ => []
    | none => ((List.finRange n).filter (fun v₂ => candPredV adj χ mf v₁ v₂)).map (fun v₂ => (v₁, v₂))

theorem secondsV_ofFn (adj : AdjMatrix n) (χ : Colouring n) (m : Fin n → Option (Fin n)) :
    secondsV adj χ (Vector.ofFn m) = seconds adj χ m := by
  unfold secondsV seconds
  congr 1
  funext v₁
  have hf : (fun v₂ => candPredV adj χ (Vector.ofFn m) v₁ v₂)
      = (fun v₂ => candPred adj χ m v₁ v₂) :=
    funext fun v₂ => Deck.candPredV_ofFn adj χ m v₁ v₂
  rw [show (Vector.ofFn m).get v₁ = m v₁ by simp [Vector.get], hf]

/-- The per-first-pair batch: ONE base propagation, its ambiguity set, each continuation from the shared
state. `deck2Batch_eq` ties it to the spec candidates. -/
def deck2Batch (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    List (Equiv.Perm (Fin n)) :=
  let mf := propagateVec adj χ u₁ u₂
  (secondsV adj χ mf).filterMap fun p =>
    let m2 := (roundVecD adj χ)^[n] (Vector.ofFn (fun v => if v = p.1 then some p.2 else mf.get v))
    permOf (fun x => (m2.get x).getD x)

theorem deck2Batch_eq (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    deck2Batch adj χ u₁ u₂
      = (seconds adj χ (propagate adj χ u₁ u₂)).filterMap
          (fun p => deck2Cand adj χ u₁ u₂ p.1 p.2) := by
  simp only [deck2Batch, propagateVec_eq, secondsV_ofFn]
  congr 1
  funext p
  have hseed : Vector.ofFn
        (fun v => if v = p.1 then some p.2 else (Vector.ofFn (propagate adj χ u₁ u₂)).get v)
      = Vector.ofFn (setSeed (propagate adj χ u₁ u₂) p.1 p.2) := by
    congr 1
    funext v
    simp [Vector.get, setSeed]
  rw [hseed, iterate_roundVecD]
  unfold deck2Cand deck2Fun contFrom
  congr 1
  funext x
  simp [Vector.get]

/-! ## 7. The supply -/

/-- **★ THE SECOND-SEED PROPAGATION SUPPLY.** Every branch-cell pair seeds a propagation; every stalled
state's ambiguity entry seeds a continuation; the gate and `Consume.verified` filter the junk. Cost billed
flat: per first pair, the F2b propagation bill plus ≤ `n²` continuations at the same bound. -/
def deck2Supply : Supply n := fun adj χ =>
  let B := branches χ
  (B.flatMap fun u₁ => B.flatMap fun u₂ => deck2Batch adj χ u₁ u₂,
   B.length * B.length * (1 + n * n) * (n * n * n * n * n))

theorem mem_gens_deck2Supply_iff {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)} :
    g ∈ gens (deck2Supply (n := n)) adj χ ↔
      ∃ u₁ ∈ branches χ, ∃ u₂ ∈ branches χ,
        ∃ p ∈ seconds adj χ (propagate adj χ u₁ u₂),
          deck2Cand adj χ u₁ u₂ p.1 p.2 = some g := by
  constructor
  · intro hg
    obtain ⟨u₁, h₁, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨u₂, h₂, hb⟩ := List.mem_flatMap.mp hq
    rw [deck2Batch_eq] at hb
    obtain ⟨p, hp, hc⟩ := List.mem_filterMap.mp hb
    exact ⟨u₁, h₁, u₂, h₂, p, hp, hc⟩
  · rintro ⟨u₁, h₁, u₂, h₂, p, hp, hc⟩
    exact List.mem_flatMap.mpr ⟨u₁, h₁, List.mem_flatMap.mpr ⟨u₂, h₂,
      (deck2Batch_eq adj χ u₁ u₂) ▸ List.mem_filterMap.mpr ⟨p, hp, hc⟩⟩⟩

/-! ## 8. `①c` — the supply is equivariant -/

/-- **★★ THE SECOND-SEED SUPPLY IS EQUIVARIANT** — both enumerations transport (the branch cell; the
stalled state's ambiguity set, `mem_seconds_conj`) and the candidate conjugates including its failure mode
(`deck2Cand_conj`). No representative is ever chosen. -/
theorem gensEquivariant_deck2Supply : GensEquivariant (deck2Supply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_deck2Supply_iff]
  constructor
  · rintro ⟨u₁, h₁, u₂, h₂, p, hp, hc⟩
    obtain ⟨w₁, hw₁, rfl⟩ := (hbr u₁).mp h₁
    obtain ⟨w₂, hw₂, rfl⟩ := (hbr u₂).mp h₂
    rw [Deck.propagate_conj] at hp
    obtain ⟨q, hq, hpq⟩ := (mem_seconds_conj σ adj χ (propagate adj χ w₁ w₂) p).mp hp
    rw [← hpq] at hc
    rw [deck2Cand_conj] at hc
    rcases hcase : deck2Cand adj χ w₁ w₂ q.1 q.2 with _ | t
    · rw [hcase] at hc; simp at hc
    · rw [hcase] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact ⟨t, ⟨w₁, hw₁, w₂, hw₂, q, hq, hcase⟩, hc.symm⟩
  · rintro ⟨h, ⟨u₁, h₁, u₂, h₂, p, hp, hc⟩, rfl⟩
    refine ⟨σ u₁, (hbr _).mpr ⟨u₁, h₁, rfl⟩, σ u₂, (hbr _).mpr ⟨u₂, h₂, rfl⟩,
      (σ p.1, σ p.2), ?_, ?_⟩
    · rw [Deck.propagate_conj]
      exact (mem_seconds_conj σ adj χ (propagate adj χ u₁ u₂) _).mpr ⟨p, hp, rfl⟩
    · show deck2Cand (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) (σ p.1) (σ p.2)
          = some (σ * h * σ⁻¹)
      rw [deck2Cand_conj, hc]
      rfl

theorem supplyEquivariant_deck2Supply : SupplyEquivariant (deck2Supply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_deck2Supply

/-! ## 9. Firing -/

/-- **Graded firing, per pair:** a verified second-seed candidate carrying `u₁` to `u₂` puts the pair into
the verified `WordReach`. -/
theorem wordReach_deck2Supply {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ v₁ v₂ : Fin n}
    {τ : Equiv.Perm (Fin n)}
    (h₁ : u₁ ∈ branches χ) (h₂ : u₂ ∈ branches χ)
    (hsec : (v₁, v₂) ∈ seconds adj χ (propagate adj χ u₁ u₂))
    (hτ : IsColAut adj χ τ)
    (hcand : deck2Cand adj χ u₁ u₂ v₁ v₂ = some τ) (hval : τ u₁ = u₂) :
    WordReach (verified (deck2Supply (n := n)) adj χ) u₁ u₂ := by
  have hmem : τ ∈ verified (deck2Supply (n := n)) adj χ := by
    refine List.mem_filter.mpr ⟨?_, by simpa using hτ⟩
    exact mem_gens_deck2Supply_iff.mpr ⟨u₁, h₁, u₂, h₂, (v₁, v₂), hsec, hcand⟩
  have hstep := (Consume.WordReach.refl
    (G := verified (deck2Supply (n := n)) adj χ) u₁).step hmem
  rwa [hval] at hstep

/-- **★★★ THE ORACLE FIRES.** If every branch-cell pair is connected by a verified second-seed candidate,
the cell is certified as one orbit — with no refinement, past the commuting-gauge stall that defeats F2b. -/
theorem cellIsOrbit_deck2Supply {adj : AdjMatrix n} {χ : Colouring n}
    (h : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ (v₁ v₂ : Fin n) (τ : Equiv.Perm (Fin n)),
      (v₁, v₂) ∈ seconds adj χ (propagate adj χ u w) ∧
      IsColAut adj χ τ ∧ deck2Cand adj χ u w v₁ v₂ = some τ ∧ τ u = w) :
    CellIsOrbit (deck2Supply (n := n)) adj χ := by
  intro u hu w hw
  obtain ⟨v₁, v₂, τ, hsec, hτ, hcand, hval⟩ := h u hu w hw
  exact wordReach_deck2Supply hu hw hsec hτ hcand hval

/-! ## 10. ★★★ THE CAPSTONES — both objects, no carried hypotheses -/

/-- **★★★ The guarded (blind) mixed canonizer over the second-seed supply.** -/
theorem deck2Supply_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n)) (deck2Supply (n := n))))) :=
  SupplyTransport.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    supplyEquivariant_deck2Supply

/-- **★★★ The FUSED (resolver-aware) canonizer over the second-seed supply.** -/
theorem deck2Supply_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (deck2Supply (n := n)))) :=
  Select.selNode_canonizer Force.keyEquivariant_lookahead supplyEquivariant_deck2Supply

/-- **★★★ THE F2c CANONIZER OF RECORD for the fold family**: force = the holonomy key, consume =
`foldSupply ++ deckSupply ++ deck2Supply` — the object the `U3 ⊔ T3` end-to-end acceptance runs. -/
theorem holKey_foldDeck2_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (appendSupply (Fold.foldSupply (n := n))
            (appendSupply (Deck.deckSupply (n := n)) (deck2Supply (n := n)))))) :=
  Select.selNode_canonizer Hol.keyEquivariant_holKeyFast
    (Deck.supplyEquivariant_appendSupply Fold.gensEquivariant_foldSupply
      (Deck.gensEquivariant_appendSupply Deck.gensEquivariant_deckSupply
        gensEquivariant_deck2Supply))

/-- **★★★ The all-fast form of the record** (`foldSupplyFast` for the F2a component) — identical by
`foldSupplyFast_eq`; this is the form the measurements run. -/
theorem holKey_foldDeck2Fast_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (appendSupply (Fold.foldSupplyFast (n := n))
            (appendSupply (Deck.deckSupply (n := n)) (deck2Supply (n := n)))))) := by
  rw [Fold.foldSupplyFast_eq]
  exact holKey_foldDeck2_selNode_canonizer

end Deck2
end ChainDescent
