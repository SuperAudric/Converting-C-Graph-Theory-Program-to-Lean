import ChainDescent.Cost

/-!
# The **mutual-stall flag** — and the descent becomes UNCONDITIONALLY polynomial

(`docs/chain-descent-ir-blindspot-solver.md` §11.11; `docs/chain-descent-mixed-composition.md` Stage 4.)

## The correction this file implements

`Cost.lean` proved `descentCost ≤ poly` **given `ResolvedAll`** (every cell narrowed to ≤ 1). That left the
impression that the remaining ② work was to *widen* the bound to graphs with bounded, non-stacking fan-out — i.e.
to let the descent **defer** a decision, branch on it, and stay polynomial.

**That is not the algorithm.** Deferral is not a cheap mode of a healthy run; **it is the failure mode.** In the
interleaved engine every node either

* **consumes** (the supply connects the cell — the choice is a symmetry, no branching), or
* **forces** (the key separates the cell — the choice is a real decision, taken structurally),

and a node that can do **neither** has reached the **mutual stall**: that node *is* the unhandled residue. There is
no deferred-then-retried decision anywhere in the design, and therefore **no exhaustive fallback to be polynomial
*about***. A descent either runs as a single path or it stops.

So the flag is not a budget and the cost is not conditional:

> **`descentCost_guard_le` — the guarded descent is polynomial with NO hypothesis at all.**
> `ResolvedAll (guard R)` holds **by construction** (`resolvedAll_guard`), because the guard *makes* it hold: any
> node the resolvers leave with ≥ 2 branches flags instead of branching. Poly-**and**-flag, not poly-**or**-flag.

`Cost.ResolvedAll` therefore stops being a hypothesis about the graph and becomes a property of the object. What
used to be "which graphs are cheap?" is now exactly "which graphs **answer**?" — and that is `③`.

## ★ No `descend` signature change was needed

`aggregate [] = none` (`aggregate_nil`). So a resolver **already has a flag channel**: returning the *empty*
narrowing makes the node emit `none`, and `none` propagates to the root (a flagged branch flags the aggregate).
`guard R` uses exactly that. Nothing about `descend`, `①a`, `①b`, `①c` or the resolver contract changes.

## ⚠ THE NEW OBLIGATION THE FLAG CREATES: the supply must be EQUIVARIANT

This is a genuine finding, and it is not in any doc. `consume`'s selling point is that the supply is **untrusted**:
`consume_canonizer` holds for *every* supply, however wrong, because a covering resolver is *value*-invisible — a
bad supply costs branches, not correctness.

**A flag is not value-invisible.** `stalled` is defined from `(narrow R adj χ).length`, and for the composite that
length depends on how many orbits the supply's generators actually prove. A supply that returns good generators for
`G` and junk for `σ·G` makes `G` answer and `σ·G` flag — so **the flag would not be iso-invariant and `①c` would be
false.**

Hence: **soundness still needs nothing from the supply; the FLAG needs the supply to be equivariant**
(`StallEquivariant`, below — carried explicitly, and *free* for the force-only route, where the narrowing is
equivariant by construction). This is the honest price of having a flag at all, and it is a `①c` obligation, not a
soundness one.
-/

namespace ChainDescent
namespace Stall

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV KeyEquivariant)
open ChainDescent.Consume (Supply)

variable {n : Nat}

/-! ## 1. The flag channel — already present in the object -/

/-- **A resolver can already flag.** The empty narrowing aggregates to `none`, and `none` propagates: a flagged
branch flags its parent. So the mutual-stall flag needs **no change to `descend`**. -/
@[simp] theorem aggregate_nil : aggregate ([] : List (Option (Labelled n))) = none := rfl

/-! ## 2. The guard — flag instead of branch -/

/-- **The node has stalled**: the resolvers left ≥ 2 branches, i.e. some pair of branch vertices was **neither**
connected by the supply **nor** separated by the key (`Composite.forceThenConsume_stall`). That is the mutual
stall, and it is a **local, structural predicate of the node** — never of the traversal, which is what `①c`
requires. -/
def stalled (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  1 < (narrow R adj χ).length

instance (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) : Decidable (stalled R adj χ) :=
  inferInstanceAs (Decidable (1 < _))

/-- **★ THE STALL GUARD.** Run the resolver; if it leaves ≥ 2 branches, **flag** (return the empty narrowing)
instead of branching. The descent then never fans out — it is a single path or it stops. -/
def guard (R : Resolver n) : Resolver n := fun adj χ B =>
  let r := R adj χ B
  if 1 < (r.1.getD B).length then (some [], r.2) else (r.1, r.2)

theorem narrow_guard (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (guard R) adj χ = if stalled R adj χ then [] else narrow R adj χ := by
  simp only [narrow, guard, stalled]
  split_ifs with h
  · rfl
  · rfl

/-- The guarded resolver's cost is the underlying one's (the guard itself is free — it reads a length). -/
theorem guard_cost (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    (guard R adj χ B).2 = (R adj χ B).2 := by
  simp only [guard]
  split_ifs with h
  · rfl
  · rfl

/-! ## 3. ★★★ UNCONDITIONAL POLYNOMIALITY

`ResolvedAll` is no longer a hypothesis about the graph — the guard *makes* it true. -/

/-- The guarded narrowing never has more than one branch: **by construction**. -/
theorem narrow_guard_length_le_one (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) :
    (narrow (guard R) adj χ).length ≤ 1 := by
  rw [narrow_guard]
  by_cases h : stalled R adj χ
  · rw [if_pos h]; simp
  · rw [if_neg h]
    unfold stalled at h
    omega

/-- **★★ `ResolvedAll` HOLDS BY CONSTRUCTION** — no hypothesis on the graph, the supply or the key. -/
theorem resolvedAll_guard (R : Resolver n) (adj : AdjMatrix n) :
    Cost.ResolvedAll (guard R) adj :=
  fun χ _ => narrow_guard_length_le_one R adj χ

/-- **★★★ THE GUARDED DESCENT IS UNCONDITIONALLY POLYNOMIAL.**

No hypothesis on the graph, the oracle supply, or the key: whatever they do, the descent is a **single path** of
depth ≤ `n`, because a node the resolvers cannot resolve **flags** rather than branching. This is what "the
algorithm is polynomial, or it reports an unhandled residue" actually means — the polynomiality is *not*
conditional on the residue being small; it is `poly` **and** `flag`, never `poly` **or** `exponential`. -/
theorem descentCost_guard_le {rf : Refiner n} {R : Resolver n} {adj : AdjMatrix n} {c₁ c₂ : Nat}
    (hrf : ∀ χ : Colouring n, (rf adj χ).2 ≤ c₁)
    (hR : ∀ (χ : Colouring n) (B : List (Fin n)), (R adj χ B).2 ≤ c₂) :
    descentCost rf (guard R) adj ≤ c₁ + (n + 1) * (1 + c₁ + c₂) :=
  Cost.descentCost_le_of_resolved (resolvedAll_guard R adj) hrf
    (fun χ B => by rw [guard_cost]; exact hR χ B)

/-- Instantiated at the built refiner: `c₁ = n³`, so the whole bound is polynomial as soon as the resolver is. -/
theorem descentCost_guard_le_encodeFree {R : Resolver n} {adj : AdjMatrix n} {c₂ : Nat}
    (hR : ∀ (χ : Colouring n) (B : List (Fin n)), (R adj χ B).2 ≤ c₂) :
    descentCost (Refine.encodeFreeFast (n := n)) (guard R) adj
      ≤ n * n * n + (n + 1) * (1 + n * n * n + c₂) :=
  descentCost_guard_le (fun χ => le_of_eq (Cost.refiner_cost adj χ)) hR

/-! ## 4. `①` survives the flag — but the flag needs equivariance

`①a` is untouched (`soundOpt_canonForm?` holds for *every* resolver: `none` is sound). `①b`/`①c` need the guard to
transport, and that needs the **stall predicate** to transport — which is the new obligation. -/

/-- **The stall predicate is iso-invariant.** ⚠ *This is the price of having a flag.* It is **free** for an
equivariant narrowing (below), and for the composite it demands that the **oracle supply be equivariant** — a
supply returning good generators for `G` and junk for `σ·G` would make `G` answer and `σ·G` flag, and `①c` would be
false. Soundness still needs nothing from the supply; the flag does. -/
def StallEquivariant (R : Resolver n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    (narrow R (relabelAdj σ adj) (transportColouring σ χ)).length = (narrow R adj χ).length

/-- An **equivariant** narrowing gives stall-equivariance for free — the two narrowings are permutations of one
another, so they have the same length. (This is why the **force-only** route pays nothing for its flag.) -/
theorem stallEquivariant_of_narrowEquivariant {R : Resolver n} (hne : NarrowEquivariant R) :
    StallEquivariant R := by
  intro σ adj χ
  have h := (hne σ adj χ).length_eq
  rwa [List.length_map] at h

/-- The guard preserves `NarrowEquivariant`: both sides stall together (same length), and otherwise the narrowing
is unchanged. -/
theorem narrowEquivariant_guard {R : Resolver n} (hne : NarrowEquivariant R) :
    NarrowEquivariant (guard R) := by
  intro σ adj χ
  have hlen : (narrow R (relabelAdj σ adj) (transportColouring σ χ)).length
      = (narrow R adj χ).length := stallEquivariant_of_narrowEquivariant hne σ adj χ
  rw [narrow_guard, narrow_guard]
  unfold stalled
  by_cases h : 1 < (narrow R adj χ).length
  · rw [if_pos (by rw [hlen]; exact h), if_pos h]; simp
  · rw [if_neg (by rw [hlen]; exact h), if_neg h]
    exact hne σ adj χ

/-! ## 5. ★ THE GUARDED FORCE CANONIZER — sound, iso-invariant, and unconditionally polynomial -/

/-- **★★★ THE FORCE ROUTE, GUARDED: a canonical form that is UNCONDITIONALLY POLYNOMIAL and flags exactly at the
mutual stall.**

`①a`/`①b`/`①c` hold modulo nothing but `KeyEquivariant`, *and* the descent is a single path on **every** input. It
no longer "always answers" (`canonForm?_ne_none` needed `NarrowProper`, which the guard deliberately breaks) — and
that is the point: **it answers or it flags, and it is polynomial either way.** -/
theorem guarded_force_canonizer {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (guard (Force.forceBy key)))
    ∧ ∀ (adj : AdjMatrix n) (c₂ : Nat),
        (∀ (χ : Colouring n) (B : List (Fin n)), (Force.forceBy key adj χ B).2 ≤ c₂) →
        descentCost (Refine.encodeFreeFast (n := n)) (guard (Force.forceBy key)) adj
          ≤ n * n * n + (n + 1) * (1 + n * n * n + c₂) :=
  ⟨Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFreeFast
      (Descend.narrowTransport_of_narrowEquivariant Refine.refineEquivariant_encodeFreeFast
        (narrowEquivariant_guard (Force.narrowEquivariant_forceBy hk))),
   fun _ _ hR => descentCost_guard_le_encodeFree hR⟩

/-! ## 6. What the flag MEANS — the `③` hook

The guarded descent flags at a node iff the resolvers left ≥ 2 branches there. For the **mixed** resolver
`Composite.forceThenConsume_stall` already reads that off as an *attribution*: some pair of branch vertices was
**neither** connected by the supply **nor** separated by the key. That is the mutual stall, and characterizing the
graphs on which it occurs is `③` (`stalled ⟹ residueHiddenJohnson ∨ residueRigidObstruction`).

Note the direction of the remaining work has changed. Under the old framing `②` asked *"which graphs are cheap?"*.
Now every graph is cheap, and the whole question is *"which graphs **answer**?"* — one question, not two. -/

/-- The guarded descent flags at a node **exactly** when that node stalled. -/
theorem narrow_guard_eq_nil_iff (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n)
    (hne : ¬ Discrete χ) (hproper : narrow R adj χ ≠ []) :
    narrow (guard R) adj χ = [] ↔ stalled R adj χ := by
  rw [narrow_guard]
  by_cases h : stalled R adj χ
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc hproper, fun hc => absurd hc h⟩

end Stall
end ChainDescent
