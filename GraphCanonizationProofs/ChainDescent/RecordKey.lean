import ChainDescent.RecordCost
import ChainDescent.ForcePick

/-!
# The LEX-PRODUCT key combinator, and the record object's force key

## Why a combinator, and why `compKey` is not one

`Publication.canonForm?` uses `Hol.holKeyFast` alone. Bringing a second force key into the record —
`Deepen.orbKeyG guardSupply` now, `RigidSeal.compKey`'s solver key later — needs a way to *combine*
keys, and the project's only existing combination is `RigidSeal.compKey`, which is a **case split**
(disjoint tags `0 ::` / `1 ::` on a `Discrete` test), not a product: it runs exactly one of its two
keys at each node. A product runs both and breaks ties with the second.

`Force.keyV` is a `List Nat` ordered by `Descend.lexLeList`, so the product is **concatenation** —
provided the first component has the same length on the two branches being compared. That side
condition is real and is named `ConstLen`; without it concatenation is not a lex product (a shorter
list is `lexLeList`-smaller, so a long first component could be out-ranked by a short one and the
second component would be consulted at the wrong time). ⚠ Length-prefixing (`len a :: a`) removes the
side condition but changes the order on the first component to **shortlex**, which silently re-orders
`holKeyFast`'s own narrowing — worse than carrying `ConstLen`, which every built key satisfies.

## What is proved

* §1 `pairKey`, `keyEquivariant_pairKey` (**unconditional**), and the cost bound (costs add).
* §2 `ConstLen`, `keyV_pairKey_inj`, and the two **separation-transfer** lemmas: the product separates
  whatever *either* component separates. This is the firing gain, and it is why the swap is an
  improvement rather than a lateral move.
* §3 **`keepMin_pairKey_subset`** — the NO-STRENGTH-LOSS theorem: the product's argmin sits inside the
  first key's argmin, so adding a tiebreak never widens the narrowing. (Engine:
  `lexLeList_append_left`, where `ConstLen` does the work.)
* §4 `recordKey := pairKey holKeyFast (orbKeyG guardSupply)` — `①` via
  `Select.selNode_canonizer_of_sameOrbits` (key-generic, so this is *one* `KeyEquivariant` proof), and
  `②` end-to-end, mirroring `RecordCost.descentCostS_selNode_record_le`.

⚠ **What this does NOT claim.** The swap buys *firing coverage* — strictly more separated pairs — not
a new theorem about the residue. `orbKeyG`'s guard is shut on most nodes, and where it is shut the
second component is the constant `[]` and the product is `holKeyFast` verbatim
(`keyV_pairKey_of_guard_shut`). Nor is `Publication.canonForm?` itself edited here: that swap also
wants the `②` bound reshaped into `costConst * n ^ costDeg`, which touches pinned statements.
-/

namespace ChainDescent
namespace RecordKey

open ChainDescent.Descend
open ChainDescent.Consume (Supply gens supplyCost)
open ChainDescent.Force (Key keyV keyCost KeyEquivariant keepMin)
open ChainDescent.KeyComplete (KeySeparatesAt KeySeparatesAll)

variable {n : Nat}

/-! ## 1. The combinator -/

/-- **The lex product of two force keys** — values concatenate, costs add. -/
def pairKey (k₁ k₂ : Key n) : Key n := fun adj χ v =>
  (keyV k₁ adj χ v ++ keyV k₂ adj χ v, keyCost k₁ adj χ v + keyCost k₂ adj χ v)

@[simp] theorem keyV_pairKey (k₁ k₂ : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (pairKey k₁ k₂) adj χ v = keyV k₁ adj χ v ++ keyV k₂ adj χ v := rfl

@[simp] theorem keyCost_pairKey (k₁ k₂ : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (pairKey k₁ k₂) adj χ v = keyCost k₁ adj χ v + keyCost k₂ adj χ v := rfl

/-- **`①` for the product, unconditional** — the sole force-side obligation is componentwise. -/
theorem keyEquivariant_pairKey {k₁ k₂ : Key n} (h₁ : KeyEquivariant k₁) (h₂ : KeyEquivariant k₂) :
    KeyEquivariant (pairKey k₁ k₂) := by
  intro σ adj χ v
  simp only [keyV_pairKey, h₁ σ adj χ v, h₂ σ adj χ v]

theorem keyCost_pairKey_le {k₁ k₂ : Key n} {adj : AdjMatrix n} {χ : Colouring n} {c₁ c₂ : Nat}
    (h₁ : ∀ v : Fin n, keyCost k₁ adj χ v ≤ c₁) (h₂ : ∀ v : Fin n, keyCost k₂ adj χ v ≤ c₂)
    (v : Fin n) : keyCost (pairKey k₁ k₂) adj χ v ≤ c₁ + c₂ :=
  Nat.add_le_add (h₁ v) (h₂ v)

/-- Where the second key defers (constant `[]`), the product IS the first key. -/
theorem keyV_pairKey_of_right_nil {k₁ k₂ : Key n} {adj : AdjMatrix n} {χ : Colouring n} {v : Fin n}
    (h : keyV k₂ adj χ v = []) : keyV (pairKey k₁ k₂) adj χ v = keyV k₁ adj χ v := by
  simp [h]

/-! ## 2. `ConstLen`, and the separation transfer

Concatenation is a genuine lex product exactly when the two branches' **first** components have equal
length; then any difference is decided inside the prefix, and ties fall through to the second. -/

/-- The key's value has the same length at every vertex of a node. -/
def ConstLen (key : Key n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n),
    (keyV key adj χ u).length = (keyV key adj χ w).length

/-- **The product's value determines both components.** -/
theorem keyV_pairKey_inj {k₁ k₂ : Key n} (hc : ConstLen k₁) {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (h : keyV (pairKey k₁ k₂) adj χ u = keyV (pairKey k₁ k₂) adj χ w) :
    keyV k₁ adj χ u = keyV k₁ adj χ w ∧ keyV k₂ adj χ u = keyV k₂ adj χ w := by
  simp only [keyV_pairKey] at h
  exact List.append_inj h (hc adj χ u w)

/-- **The product separates whatever the FIRST component separates.** -/
theorem keySeparatesAt_pairKey_left {k₁ k₂ : Key n} (hc : ConstLen k₁) {adj : AdjMatrix n}
    {χ : Colouring n} (h : KeySeparatesAt k₁ adj χ) : KeySeparatesAt (pairKey k₁ k₂) adj χ :=
  fun u hu w hw hno heq => h u hu w hw hno (keyV_pairKey_inj hc heq).1

/-- **…and whatever the SECOND separates.** Together these are the firing gain of a product over
either component alone: the separated set is the union, never smaller. -/
theorem keySeparatesAt_pairKey_right {k₁ k₂ : Key n} (hc : ConstLen k₁) {adj : AdjMatrix n}
    {χ : Colouring n} (h : KeySeparatesAt k₂ adj χ) : KeySeparatesAt (pairKey k₁ k₂) adj χ :=
  fun u hu w hw hno heq => h u hu w hw hno (keyV_pairKey_inj hc heq).2

theorem keySeparatesAll_pairKey_left {k₁ k₂ : Key n} (hc : ConstLen k₁) {adj : AdjMatrix n}
    (h : KeySeparatesAll k₁ adj) : KeySeparatesAll (pairKey k₁ k₂) adj :=
  fun χ hd => keySeparatesAt_pairKey_left hc (h χ hd)

theorem keySeparatesAll_pairKey_right {k₁ k₂ : Key n} (hc : ConstLen k₁) {adj : AdjMatrix n}
    (h : KeySeparatesAll k₂ adj) : KeySeparatesAll (pairKey k₁ k₂) adj :=
  fun χ hd => keySeparatesAt_pairKey_right hc (h χ hd)

/-! ## 3. ★★ NO STRENGTH LOSS — the product's argmin sits inside the first key's

This is the analogue of `Select.canonFormS?_selNode_dominates` at the key level: a tiebreak can only
*shrink* the narrowing, never widen it. `ConstLen` is exactly what makes it true — with unequal first
components a short one would win on length and the ordering would not refine `k₁`'s. -/

theorem lexLeList_append_left : ∀ (a a' b b' : List Nat), a.length = a'.length →
    lexLeList (a ++ b) (a' ++ b') = true → lexLeList a a' = true := by
  intro a
  induction a with
  | nil =>
      intro a' b b' hlen _
      cases a' with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x as ih =>
      intro a' b b' hlen h
      cases a' with
      | nil => simp at hlen
      | cons y as' =>
          have hlen' : as.length = as'.length := by simpa using hlen
          have h' : (if x < y then true else if y < x then false else
              lexLeList (as ++ b) (as' ++ b')) = true := h
          show (if x < y then true else if y < x then false else lexLeList as as') = true
          by_cases hxy : x < y
          · simp [hxy]
          · by_cases hyx : y < x
            · simp [hxy, hyx] at h'
            · rw [if_neg hxy, if_neg hyx] at h' ⊢
              exact ih as' b b' hlen' h'

/-- **★★ The tiebreak never widens the narrowing.** -/
theorem keepMin_pairKey_subset {k₁ k₂ : Key n} (hc : ConstLen k₁) (adj : AdjMatrix n)
    (χ : Colouring n) (B : List (Fin n)) {v : Fin n} (hv : v ∈ keepMin (pairKey k₁ k₂) adj χ B) :
    v ∈ keepMin k₁ adj χ B := by
  obtain ⟨hvB, hmin⟩ := (Force.mem_keepMin_iff v).mp hv
  refine (Force.mem_keepMin_iff v).mpr ⟨hvB, fun w hw => ?_⟩
  have h := hmin w hw
  simp only [keyV_pairKey] at h
  exact lexLeList_append_left _ _ _ _ (hc adj χ v w) h

/-! ## 4. The record's force key

`holKeyFast` first (the record's current key, so its ranking is preserved by §3), the union-guarded
`orbKeyG` as the tiebreak. `ConstLen` for `holKeyFast` is immediate: `holSigFast` is a `map` over
`List.range (n + 1)`. -/

theorem constLen_holKeyFast : ConstLen (Hol.holKeyFast (n := n)) := by
  intro adj χ u w
  show (Hol.holSigFast adj χ u).length = (Hol.holSigFast adj χ w).length
  simp [Hol.holSigFast]

/-- **The record's force key** — the holonomy key, tie-broken by the union-guarded orbit key. -/
abbrev recordKey : Key n :=
  pairKey (Hol.holKeyFast (n := n)) (Deepen.orbKeyG (Deepen.guardSupply (n := n)))

/-- **`①`'s whole force-side obligation, discharged with no hypothesis.** -/
theorem keyEquivariant_recordKey : KeyEquivariant (recordKey (n := n)) :=
  keyEquivariant_pairKey Hol.keyEquivariant_holKeyFast Deepen.keyEquivariant_orbKeyG_guard

/-- The tiebreak is never a regression: the holonomy key's narrowing is preserved. -/
theorem keepMin_recordKey_subset (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n))
    {v : Fin n} (hv : v ∈ keepMin (recordKey (n := n)) adj χ B) :
    v ∈ keepMin (Hol.holKeyFast (n := n)) adj χ B :=
  keepMin_pairKey_subset constLen_holKeyFast adj χ B hv

/-- The firing gain: wherever the guard is open and the orbit key separates, so does the record key —
even where the holonomy key ties. -/
theorem keySeparatesAt_recordKey_of_certifiedG {adj : AdjMatrix n} {χ : Colouring n}
    (h : Deepen.CertifiedG (Deepen.guardSupply (n := n)) adj χ) :
    KeySeparatesAt (recordKey (n := n)) adj χ :=
  keySeparatesAt_pairKey_right constLen_holKeyFast
    (KeyComplete.keySeparatesAt_orbKeyG_of_certifiedG h)

/-- **★★★ `①` FOR THE RECORD OBJECT AT THE COMPOSED KEY.** Same supply, same refiner, same capstone —
`Select.selNode_canonizer_of_sameOrbits` is key-generic, so the swap costs exactly the
`KeyEquivariant` proof above. -/
theorem recordKey_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (recordKey (n := n))
          (RecordCost.recordSupplyFast (n := n)))) := by
  show CanonSpec.IsCanonicalFormOpt
    (Select.canonFormS? (Refine.encodeFreeFast (n := n))
      (Select.selNode (Refine.encodeFreeFast (n := n)) (recordKey (n := n))
        (Deck.appendSupply (Fold.foldSupplyFast (n := n))
          (Deck.appendSupply (Deck.deckSupply (n := n))
            (Deck.appendSupply (Deck2.deck2Supply (n := n)) (Kernel.kernelSupply (n := n)))))))
  rw [Fold.foldSupplyFast_eq]
  exact Select.selNode_canonizer_of_sameOrbits keyEquivariant_recordKey
    Kernel.supplyEquivariant_recordRefSupply Kernel.sameOrbits_recordSupply

/-! ### 4a. `②` at the composed key

The guard inside `orbKeyG` calls `guardSupply` once per level, so its bill is parametric in
`guardSupply`'s own `supplyCost` (`Deepen.keyCost_orbKeyG_le`) — which is why that supply needs a
bound of its own. Three of its four members are already bounded in `RecordCost`; the fourth is
`matchSupply`, bounded in `SupplyCost`. -/

def guardSupplyBound (n : Nat) : Nat :=
  n * n * (n * n * n * n * n)
    + (n * n * (n * n * n * n * n)
      + (n * n * (1 + n * n) * (n * n * n * n * n) + SupplyCost.matchSupplyBound n))

theorem supplyCost_guardSupply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Deepen.guardSupply (n := n)) adj χ ≤ guardSupplyBound n := by
  simp only [Deepen.guardSupply, RecordCost.supplyCost_appendSupply, guardSupplyBound]
  exact Nat.add_le_add (RecordCost.supplyCost_foldSupplyFast_le adj χ)
    (Nat.add_le_add (RecordCost.supplyCost_deckSupply_le adj χ)
      (Nat.add_le_add (RecordCost.supplyCost_deck2Supply_le adj χ)
        (SupplyCost.supplyCost_matchSupply_le adj χ)))

/-- The composed key's per-evaluation bill: the holonomy sweep plus the guarded read *and its guard*. -/
def recordKeyBound (n : Nat) : Nat :=
  n * n * n * n * n + (n * n * n * n + n * (n * n * n * n + guardSupplyBound n))

theorem keyCost_recordKey_le (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (recordKey (n := n)) adj χ v ≤ recordKeyBound n :=
  keyCost_pairKey_le (fun v => RecordCost.keyCost_holKeyFast_le adj χ v)
    (fun v => Deepen.keyCost_orbKeyG_le (fun χ' => supplyCost_guardSupply_le adj χ') χ v) v

/-- **★★★ `②` END-TO-END AT THE COMPOSED KEY** — the same explicit-polynomial shape as
`RecordCost.descentCostS_selNode_record_le`, with the key bound now carrying the guard's own work. -/
theorem descentCostS_selNode_recordKey_le (adj : AdjMatrix n) :
    Select.descentCostS (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (recordKey (n := n))
          (RecordCost.recordSupplyFast (n := n))) adj
      ≤ n * n * n + (n + 1)
          * (1 + (Select.selProbeBound n (RecordCost.recordSupplyBound n)
              (RecordCost.recordGensBound n) (recordKeyBound n) + n * n * n)) := by
  refine Select.descentCostS_le_of_le_one
    (fun χ _ => Select.selNode_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine Select.selNode_cost_le (Select.selProbeCost_le (RecordCost.supplyCost_record_le adj χ)
    (RecordCost.gens_record_length_le adj χ) (fun v => keyCost_recordKey_le adj χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-- **The upgraded record capstone: `①` + `②` at the composed key.** This is the object
`Publication.canonForm?` should name; the remaining step there is reshaping the `②` bound into the
`costConst * n ^ costDeg` monomial its statement pins. -/
theorem recordKey_canonizer_with_cost :
    CanonSpec.IsCanonicalFormOpt
        (Select.canonFormS? (Refine.encodeFreeFast (n := n))
          (Select.selNode (Refine.encodeFreeFast (n := n)) (recordKey (n := n))
            (RecordCost.recordSupplyFast (n := n))))
    ∧ ∀ adj : AdjMatrix n,
        Select.descentCostS (Refine.encodeFreeFast (n := n))
            (Select.selNode (Refine.encodeFreeFast (n := n)) (recordKey (n := n))
              (RecordCost.recordSupplyFast (n := n))) adj
          ≤ n * n * n + (n + 1)
              * (1 + (Select.selProbeBound n (RecordCost.recordSupplyBound n)
                  (RecordCost.recordGensBound n) (recordKeyBound n) + n * n * n)) :=
  ⟨recordKey_canonizer, descentCostS_selNode_recordKey_le⟩

end RecordKey
end ChainDescent
