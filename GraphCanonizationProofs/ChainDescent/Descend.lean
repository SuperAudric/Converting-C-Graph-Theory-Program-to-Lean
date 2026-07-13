import ChainDescent.Spine
import ChainDescent.CanonicalForm
import ChainDescent.CostModel

/-!
# Stage 0b — `descend`: the branching, resolver-parameterized descent (the OBJECT)

(`docs/chain-descent-mixed-composition.md` §1.2–§1.4, Stage 0b.)

Stage 0a fixed the spec: a canonizer is **`SoundOpt ∧ IsoInvariantOpt`** and nothing else (completeness and
flag-invariance are then free, `CanonicalForm.lean`). This file builds the **object** those two facts will be
proved about (Stage 2).

**The object.** One descent, defined once:

  `descend refine R adj fuel χ : CostM (Option (Labelled n))`

At a node with colouring `χ`: if `χ` is discrete, emit the leaf matrix; otherwise select the target cell
(equivariantly, by least colour), form the branch set `B` over its vertices, let the **resolver** `R` narrow
`B` to a nonempty `B' ⊆ B` (or *defer*, `B' = B`), recurse on each branch, and **aggregate**. The run flags
(`none`) when it runs out of fuel.

**Three design commitments, all from the doc's "bake-in" list — honoured here so later work is not foreclosed:**

1. **Index-free individualization** (`indivOne`). A branch marks its vertex with a *parity bit* on the existing
   colour — `χ' v = 2·χ v + 1`, `χ' u = 2·χ u` — and **never** mentions `v.val`. This is the "X3 index-free cut":
   an individualization that used `v.val` (as `IndivStep.default` does) would leak the vertex's *index* into the
   leaf colouring, and the descent could not be iso-invariant. Only the *level* structure survives, which is what
   transports.
2. **Refinement is a PARAMETER** (`refine : AdjMatrix n → Colouring n → Colouring n`), not hardcoded. The
   descent therefore does **not** bake in the `Encodable.encode` `refineStep`, whose colour blow-up is the known
   `#eval` staller (cost-model D7 fork; `chain-descent-executable-track.md`). The encode-free/renumbering round
   drops in as the instance. Its **equivariance** is the hypothesis Stage 2 will carry.
3. **Computable.** `rankPerm` is `noncomputable` (`Equiv.ofBijective`), so the leaf emit goes through `rankInv`
   (rank → vertex, by search) and is proved *equal* to `labelledAdj (rankPerm …)`. Nothing here uses
   `Classical.choice` in the definitions.

**Resolvers are STUBBED at this stage.** `Resolver` is the narrowing type; `deferAll` (never narrows) is the
baseline instance, which makes `descend deferAll` the honest exhaustive-branching object. The *contract*
(equivariance + **branch covering**: every discarded branch's output is already reachable through a kept one)
is Stage 1, and the consume/force instances are Stage 3. Crucially the descent is written against the resolver
**type**, so Stages 0–2 do not wait on either instance.
-/

namespace ChainDescent
namespace Descend

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)

variable {n : Nat}

/-- `Discrete` (colour-injectivity) is decidable — needed to branch on "is this a leaf?" *computably*. -/
instance decidableDiscrete (χ : Colouring n) : Decidable (Discrete χ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, χ i = χ j → i = j))

/-! ## 1. The computable leaf emit

`Colouring.rankPerm` is `noncomputable`, so we cannot emit a leaf through it. `rankInv` computes its inverse
(given a rank, search for the vertex carrying it) and `leafMatrix` relabels by rank. The soundness lemma —
`leafMatrix = labelledAdj (rankPerm …)` — is what makes the emitted leaf a *genuine relabelling*, i.e. `①a`
at the leaf. -/

/-- **Rank → vertex** (computable inverse of `Colouring.vertexRank`). On a discrete colouring the search always
succeeds (`rankInv_spec`); the `getD` default is never used there. -/
def rankInv (χ : Colouring n) (i : Fin n) : Fin n :=
  ((List.finRange n).find? (fun v => Colouring.vertexRank χ v = i)).getD i

/-- On a discrete colouring `vertexRank` is surjective (it is the underlying map of the bijection `rankPerm`). -/
theorem vertexRank_surj (χ : Colouring n) (h : Discrete χ) :
    Function.Surjective (Colouring.vertexRank χ) := by
  intro i
  obtain ⟨v, hv⟩ := (Colouring.rankPerm χ h).surjective i
  exact ⟨v, by rw [← Colouring.rankPerm_apply χ h v]; exact hv⟩

/-- **`rankInv` really inverts `vertexRank`** on a discrete colouring. -/
theorem rankInv_spec (χ : Colouring n) (h : Discrete χ) (i : Fin n) :
    Colouring.vertexRank χ (rankInv χ i) = i := by
  unfold rankInv
  cases hf : (List.finRange n).find? (fun v => Colouring.vertexRank χ v = i) with
  | none =>
      exfalso
      obtain ⟨v, hv⟩ := vertexRank_surj χ h i
      have hnone := List.find?_eq_none.mp hf v (List.mem_finRange v)
      simp [hv] at hnone
  | some w =>
      have hw := List.find?_some hf
      simpa using hw

/-- `rankInv` is the inverse permutation `rankPerm.symm`. -/
theorem rankInv_eq_symm (χ : Colouring n) (h : Discrete χ) (i : Fin n) :
    rankInv χ i = (Colouring.rankPerm χ h).symm i := by
  apply (Colouring.rankPerm χ h).injective
  rw [Equiv.apply_symm_apply, Colouring.rankPerm_apply]
  exact rankInv_spec χ h i

/-- **The leaf matrix** — relabel `adj` by colour-rank. Computable. -/
def leafMatrix (adj : AdjMatrix n) (χ : Colouring n) : Labelled n :=
  fun i j => adj.adj (rankInv χ i) (rankInv χ j)

/-- **The leaf emit is a genuine relabelling** — `leafMatrix = labelledAdj (rankPerm …)`. -/
theorem leafMatrix_eq_labelledAdj (adj : AdjMatrix n) (χ : Colouring n) (h : Discrete χ) :
    leafMatrix adj χ = labelledAdj (Colouring.rankPerm χ h) adj := by
  funext i j
  show adj.adj (rankInv χ i) (rankInv χ j)
      = adj.adj ((Colouring.rankPerm χ h).symm i) ((Colouring.rankPerm χ h).symm j)
  rw [rankInv_eq_symm χ h i, rankInv_eq_symm χ h j]

/-- **`①a` at the leaf** — the emitted matrix is a relabelling of the input. This is the base case of
`SoundOpt descend`. -/
theorem leafMatrix_sound (adj : AdjMatrix n) (χ : Colouring n) (h : Discrete χ) :
    ∃ π : Equiv.Perm (Fin n), leafMatrix adj χ = labelledAdj π adj :=
  ⟨Colouring.rankPerm χ h, leafMatrix_eq_labelledAdj adj χ h⟩

/-! ## 2. Index-free individualization (the X3 cut)

A branch commits **one** vertex. The fresh colour must not mention the vertex's *index*: `IndivStep.default`
encodes `χ v * n + v.val`, which is fine for a single fixed path but leaks the labelling into the leaf, and no
such descent can be iso-invariant. `indivOne` instead marks the chosen vertex with a **parity bit** over the
existing colour — pure structure, no index. -/

/-- **Individualize one vertex, index-free.** The chosen `v` gets an odd colour, everyone else an even one;
the old colouring is preserved (doubled). No `v.val` anywhere. -/
def indivOne (χ : Colouring n) (v : Fin n) : Colouring n :=
  fun u => if u = v then 2 * χ u + 1 else 2 * χ u

/-- The individualized vertex becomes a **singleton** (parity separates it from everyone else). -/
theorem indivOne_singleton (χ : Colouring n) (v : Fin n) :
    ∀ u, u ≠ v → indivOne χ v u ≠ indivOne χ v v := by
  intro u hu
  unfold indivOne
  rw [if_pos rfl, if_neg hu]
  omega

/-- Off the individualized vertex, `indivOne` **refines nothing away**: it induces the same partition as `χ`. -/
theorem indivOne_refines_off (χ : Colouring n) (v : Fin n) :
    ∀ x y, x ≠ v → y ≠ v → (indivOne χ v x = indivOne χ v y ↔ χ x = χ y) := by
  intro x y hx hy
  unfold indivOne
  rw [if_neg hx, if_neg hy]
  omega

/-! ## 3. The equivariant target-cell selector

The target cell is chosen by a rule that is a function of the **colouring alone** — the non-singleton cell
carrying the *least colour value*. Colour values are refinement-derived, so under a relabelling the colour
classes transport and the least non-singleton colour is the **same natural number**; that is what makes the
branch set transport (the new part of Stage 2's iso-invariance). Nothing here looks at a vertex index. -/

/-- The cell (colour class) of colour `c`. -/
def cellOf (χ : Colouring n) (c : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun v => χ v = c)

/-- The colours whose cell is not a singleton (the branchable colours). -/
def nonSingletonColours (χ : Colouring n) : Finset Nat :=
  (Finset.univ.image χ).filter (fun c => 1 < (cellOf χ c).card)

/-- **The target colour** — least non-singleton colour, or `none` when the colouring is discrete. -/
def targetColour (χ : Colouring n) : Option Nat :=
  (nonSingletonColours χ).min

/-- **The branch list** — the vertices of the target cell (empty exactly when discrete).

A `List`, not a `Finset`: `Finset.toList` is **noncomputable**, and the definition must compute (bake-in 1).
The list is built in `Fin n` index order, so its *order* is labelling-dependent — which is harmless, because
the only thing done with it is a **minimum** (`aggregate`), and a minimum under a total order depends only on
the multiset. That order-invariance is the Stage-2 lemma noted at `aggregate`. -/
def branches (χ : Colouring n) : List (Fin n) :=
  match targetColour χ with
  | none => []
  | some c => (List.finRange n).filter (fun v => χ v = c)

/-! ## 4. The `Resolver` (STUBBED)

A resolver **narrows** the branch set: given the node's colouring and the full branch set `B`, it may return a
sub-set `B'` it can justify, or `none` (= defer, keep all of `B`). Stage 1 adds the two `Prop` fields that make
it sound — **equivariance** and **branch covering** (`∃ cov : B \ B' → B', descend (cov b) = descend b`, i.e.
discarded branches are *redundant*, not *losing*) — and Stage 3 supplies the consume/force instances. `descend`
is written against this **type**, so it does not wait on either. -/

/-- A branch-narrowing resolver (the computable half of the contract). -/
abbrev Resolver (n : Nat) := Colouring n → List (Fin n) → Option (List (Fin n))

/-- The baseline resolver: never narrows (always defers). `descend deferAll` is the honest
exhaustive-branching object — sound and iso-invariant, but with no consumption or forcing. -/
def deferAll : Resolver n := fun _ _ => none

/-! ## 5. The aggregate

Branch results are combined by a **deterministic** rule: flag if any branch flagged, else take the row-major
lex-least matrix. Determinism is all `IsoInvariantOpt` needs — the spec never asks *which* leaf is chosen (§1.1),
only that isomorphic inputs get the same one.

The comparison is written directly (row-major flatten + list-lex) rather than through Mathlib's `Pi.Lex`, to
keep the definition **computable**.

**Stage-2 obligation (recorded here, where it arises):** `aggregate` is applied to `(branches χ).toList`, whose
*order* is labelling-dependent. The aggregate must therefore be **permutation-invariant** — which it is, being a
minimum under a total order, so it depends only on the multiset of results. That lemma is part of proving
`IsoInvariantOpt`. -/

/-- Row-major flattening of a labelled matrix. -/
def flatten (M : Labelled n) : List Nat :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => M i j))

/-- Lexicographic `≤` on `Nat` lists (computable, total). -/
def lexLeList : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLeList as bs

/-- Row-major lexicographic `≤` on labelled matrices. -/
def lexLe (M N : Labelled n) : Bool := lexLeList (flatten M) (flatten N)

/-- The lex-least matrix of a list (`none` on the empty list). -/
def lexMin? : List (Labelled n) → Option (Labelled n)
  | [] => none
  | M :: Ms =>
      match lexMin? Ms with
      | none => some M
      | some N => some (if lexLe M N then M else N)

/-- **Aggregate branch results.** Flag if any branch flagged; otherwise the lex-least leaf. -/
def aggregate (rs : List (Option (Labelled n))) : Option (Labelled n) :=
  if rs.any Option.isNone then none else lexMin? (rs.filterMap id)

/-! ## 6. `descend` — the object

Fuel bounds the depth. Each branch individualizes one vertex, so a leaf is reached within `n` levels; `fuel = n`
is the intended call (`descendTop`). Running out of fuel is the placeholder for the **stall flag** — Stage 4
replaces it with the real mutual-stall/budget test, at which point `none` acquires its `UnhandledResidue`
meaning.

Cost is carried *with* the value (`CostM`), so `②` is a theorem about this same definition's `cost` and the
executable is the definition itself — no second object, no bridge (§1.4). -/

/-- **The descent.** `refine` is the (parameterized) refinement round; `R` the branch-narrowing resolver. -/
def descend (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n)
    (adj : AdjMatrix n) : Nat → Colouring n → CostM (Option (Labelled n))
  | 0, _ => (none, 1)
  | fuel + 1, χ =>
      if _h : Discrete χ then
        (some (leafMatrix adj χ), 1)
      else
        let B := branches χ
        let B' := (R χ B).getD B
        let results : List (CostM (Option (Labelled n))) :=
          B'.map (fun v => descend refine R adj fuel (refine adj (indivOne χ v)))
        (aggregate (results.map Prod.fst), 1 + (results.map Prod.snd).sum)

/-- **The top-level canonizer object.** Depth budget `n` (each level commits one vertex). This is the function
`SoundOpt` / `IsoInvariantOpt` will be proved of (Stage 2), the function `②` will cost (Stage 4), and the
function that runs (the executable). -/
def canonForm? (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n)
    (adj : AdjMatrix n) : Option (Labelled n) :=
  (descend refine R adj n (refine adj (fun _ => 0))).1

/-- The descent's cost — the `cost` projection of the *same* definition. -/
def descentCost (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n)
    (adj : AdjMatrix n) : Nat :=
  (descend refine R adj n (refine adj (fun _ => 0))).2

end Descend
end ChainDescent
