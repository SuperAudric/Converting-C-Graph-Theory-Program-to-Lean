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

/-- **The descent.** `refine` is the (parameterized) refinement round; `R` the branch-narrowing resolver.

**FUEL IS PER-LAYER, NOT A THREADED BUDGET (design commitment).** Every branch at a level receives the *same*
`fuel`, and the accumulated `cost` is summed but **never fed back into `fuel`**. There is therefore no shared
budget that an earlier (expensive) resolver could drain, causing a later *polynomial* resolver to flag through
no fault of its own. Consequence: **"resolver `R` never returns `none` on class `X`" is a LOCAL statement about
`R`** — each resolver is poly-or-flag on its own, independently of what ran above it. Do not "optimize" this
into a threaded global budget; it would couple the resolvers' flag behaviour and destroy that locality. -/
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

/-! ## 7. Stage 2a — `SoundOpt descend`

Soundness by induction on `fuel`. The leaf case is `leafMatrix_sound`; the branch case needs only that the
aggregate returns *one of its inputs* (`aggregate_mem`), so the emitted matrix is some branch's matrix, which
by the IH is a relabelling. Note the resolver is entirely unconstrained here: narrowing can only *remove*
branches, and every surviving branch is still a relabelling — **soundness holds for ANY resolver**, which is
why a mis-narrowing resolver costs a branch and never correctness. -/

/-- The lex-min of a list is a member of it. -/
theorem lexMin?_mem : ∀ (l : List (Labelled n)) {c : Labelled n}, lexMin? l = some c → c ∈ l
  | [], c, h => by simp [lexMin?] at h
  | M :: Ms, c, h => by
      unfold lexMin? at h
      cases hM : lexMin? Ms with
      | none =>
          rw [hM] at h
          have hMc : M = c := Option.some.inj h
          exact hMc ▸ List.mem_cons_self
      | some N =>
          rw [hM] at h
          have hc : (if lexLe M N then M else N) = c := Option.some.inj h
          by_cases hle : lexLe M N = true
          · rw [if_pos hle] at hc
            exact hc ▸ List.mem_cons_self
          · rw [if_neg hle] at hc
            exact List.mem_cons_of_mem _ (hc ▸ lexMin?_mem Ms hM)

/-- **The aggregate returns one of its inputs.** (It flags iff some input flagged; otherwise it is the lex-min
of the answers, hence one of them.) -/
theorem aggregate_mem {rs : List (Option (Labelled n))} {c : Labelled n}
    (h : aggregate rs = some c) : some c ∈ rs := by
  unfold aggregate at h
  by_cases hany : rs.any Option.isNone = true
  · rw [if_pos hany] at h; exact absurd h (by simp)
  · rw [if_neg hany] at h
    have hmem := lexMin?_mem _ h
    obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hmem
    exact hfa ▸ ha

/-- **`①a` for the descent** — whenever it answers, the answer is a relabelling of the input. Holds for **any**
`refine` and **any** resolver `R`. -/
theorem descend_sound (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n)
    (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n) (c : Labelled n),
      (descend refine R adj fuel χ).1 = some c → ∃ π : Equiv.Perm (Fin n), c = labelledAdj π adj := by
  intro fuel
  induction fuel with
  | zero => intro χ c h; simp [descend] at h
  | succ fuel ih =>
      intro χ c h
      rw [descend] at h
      by_cases hd : Discrete χ
      · rw [dif_pos hd] at h
        have hc : leafMatrix adj χ = c := Option.some.inj h
        exact hc ▸ leafMatrix_sound adj χ hd
      · rw [dif_neg hd] at h
        simp only at h
        have hmem := aggregate_mem h
        obtain ⟨x, hx, hx1⟩ := List.mem_map.mp hmem
        obtain ⟨v, _, hv⟩ := List.mem_map.mp hx
        exact ih (refine adj (indivOne χ v)) c (by rw [← hv] at hx1; exact hx1)

/-- **`SoundOpt` for the top-level object** — the `Publication.canon_sound` obligation, discharged. -/
theorem soundOpt_canonForm? (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n) :
    CanonSpec.SoundOpt (canonForm? (n := n) refine R) := by
  intro adj c h
  exact descend_sound refine R adj n _ c h

/-! ## 8. Stage 2b — the transport lemmas (the road to `IsoInvariantOpt`)

The plan (`docs/chain-descent-mixed-composition.md` Stage 2). Write `G' = relabelAdj σ G` and transport a
colouring `χ` on `G` to `χ ∘ σ⁻¹` on `G'` (vertex `σ v` of `G'` plays the role of `v` of `G`). Then **every
piece of the descent transports**, and the payoff is that the emitted matrices are *literally equal*:

  `leafMatrix G' (χ ∘ σ⁻¹) = leafMatrix G χ`

The `σ` cancels because the output is indexed by **ranks**, not by vertices. That single fact is the heart of
`①b`. -/

/-- Transported colouring: `χ` on `G` becomes `χ ∘ σ⁻¹` on `relabelAdj σ G`. -/
def transportColouring (σ : Equiv.Perm (Fin n)) (χ : Colouring n) : Colouring n :=
  fun u => χ (σ.symm u)

/-- **Discreteness transports.** -/
theorem discrete_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    Discrete (transportColouring σ χ) ↔ Discrete χ := by
  constructor
  · intro h i j hij
    have := h (σ i) (σ j) (by simp [transportColouring, hij])
    exact σ.injective this
  · intro h i j hij
    unfold transportColouring at hij
    have := h _ _ hij
    exact σ.symm.injective this

/-- **Vertex rank transports**: the rank of `σ v` under `χ ∘ σ⁻¹` is the rank of `v` under `χ`. -/
theorem vertexRank_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    Colouring.vertexRank (transportColouring σ χ) (σ v) = Colouring.vertexRank χ v := by
  have h : transportColouring σ χ = fun u => χ (σ.symm u) := rfl
  rw [h]
  have := vertexRank_comp χ σ.symm (σ v)
  simpa using this

/-- **`indivOne` transports**: individualizing `σ v` in the transported colouring is the transport of
individualizing `v`. (This is where the *index-free* choice pays: an index-dependent individualization would
NOT satisfy this.) -/
theorem indivOne_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    indivOne (transportColouring σ χ) (σ v) = transportColouring σ (indivOne χ v) := by
  funext u
  show (if u = σ v then 2 * χ (σ.symm u) + 1 else 2 * χ (σ.symm u))
      = (if σ.symm u = v then 2 * χ (σ.symm u) + 1 else 2 * χ (σ.symm u))
  by_cases h : u = σ v
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun hc => h (by rw [← hc]; simp))]

/-- **Cells transport** (as cardinalities): the class of colour `c` in the transported colouring is the
`σ`-image of the class in `χ`, so it has the same size. -/
theorem cellOf_card_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (c : Nat) :
    (cellOf (transportColouring σ χ) c).card = (cellOf χ c).card := by
  unfold cellOf transportColouring
  apply Finset.card_bij (fun v _ => σ.symm v)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact σ.symm.injective hab
  · intro b hb
    refine ⟨σ b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa using hb

/-- **The colour value-set transports.** -/
theorem image_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    Finset.univ.image (transportColouring σ χ) = Finset.univ.image χ := by
  unfold transportColouring
  apply Finset.ext
  intro c
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨σ.symm u, hu⟩
  · rintro ⟨v, hv⟩; exact ⟨σ v, by simpa using hv⟩

/-- **The target colour transports** — it is the same natural number on both sides. (Hence the branch *set*
transports, which is what makes the aggregate comparable.) -/
theorem targetColour_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    targetColour (transportColouring σ χ) = targetColour χ := by
  unfold targetColour nonSingletonColours
  rw [image_transport σ χ]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [cellOf_card_transport σ χ c]

/-- **The leaf matrix is LITERALLY EQUAL under transport** — the heart of `①b`. The `σ` cancels because the
output matrix is indexed by colour-*ranks*, not by vertices. -/
theorem leafMatrix_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (h : Discrete χ) :
    leafMatrix (relabelAdj σ adj) (transportColouring σ χ) = leafMatrix adj χ := by
  have hd' : Discrete (transportColouring σ χ) := (discrete_transport σ χ).mpr h
  -- `rankInv` of the transported colouring is the σ-image of `rankInv`.
  have hrank : ∀ i, rankInv (transportColouring σ χ) i = σ (rankInv χ i) := by
    intro i
    have hσ : Colouring.vertexRank (transportColouring σ χ) (σ (rankInv χ i)) = i := by
      rw [vertexRank_transport σ χ (rankInv χ i)]
      exact rankInv_spec χ h i
    have hinj : Function.Injective (Colouring.vertexRank (transportColouring σ χ)) := by
      intro a b hab
      exact (Colouring.rankPerm (transportColouring σ χ) hd').injective hab
    exact hinj (by rw [rankInv_spec (transportColouring σ χ) hd' i, hσ])
  funext i j
  show (relabelAdj σ adj).adj (rankInv (transportColouring σ χ) i)
        (rankInv (transportColouring σ χ) j) = adj.adj (rankInv χ i) (rankInv χ j)
  rw [hrank i, hrank j]
  show adj.adj (σ.symm (σ (rankInv χ i))) (σ.symm (σ (rankInv χ j))) = _
  simp

/-! ## 9. Stage 2c — the two carried hypotheses, and what remains for `IsoInvariantOpt`

`IsoInvariantOpt descend` needs exactly two hypotheses plus one combinatorial lemma.

**★ A structural discovery worth recording: resolver EQUIVARIANCE is NOT needed.** One might expect to have to
assume the resolver narrows "the same way" on `G` and `σ·G`. It does not: **covering** says
`aggregate (narrowed) = aggregate (full)` on *each* side, so both sides can be rewritten to their **full**-branch
aggregates — and the full branch list is a function of the colouring alone, hence transports. The resolver is
therefore free to narrow *differently* on `G` and `σ·G` with no loss. This is what licenses **consume**'s
"pick any orbit representative", whose choice is genuinely *not* equivariant (all orbit members look alike to
refinement) — only its *result* is, exactly because the discarded branches are covered. -/

/-- **Hypothesis on the refinement parameter: equivariance.** The refinement round must commute with
relabelling. (The encode-free round satisfies this; the obligation is carried here because `refine` is a
parameter — see §1.4 bake-in 2.) -/
def RefineEquivariant (refine : AdjMatrix n → Colouring n → Colouring n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    refine (relabelAdj σ adj) (transportColouring σ χ)
      = transportColouring σ (refine adj χ)

/-- **Hypothesis on the resolver: BRANCH COVERING** (`docs/chain-descent-mixed-composition.md` §1.3).
Narrowing the branch list does not change the aggregate — because every discarded branch's output is *already
reachable* through a kept one. Stated exactly where it is used, so it references the descent's own values and
needs **no knowledge of the final answer**. `deferAll` satisfies it trivially (it never narrows). -/
def Covering (refine : AdjMatrix n → Colouring n → Colouring n) (R : Resolver n) : Prop :=
  ∀ (adj : AdjMatrix n) (fuel : Nat) (χ : Colouring n),
    aggregate (((R χ (branches χ)).getD (branches χ)).map
        (fun v => (descend refine R adj fuel (refine adj (indivOne χ v))).1))
      = aggregate ((branches χ).map
        (fun v => (descend refine R adj fuel (refine adj (indivOne χ v))).1))

/-- The baseline resolver never narrows, so it is trivially **covering**. Hence `descend deferAll` — the honest
exhaustive-branching object — carries no resolver obligation at all. -/
theorem covering_deferAll (refine : AdjMatrix n → Colouring n → Colouring n) :
    Covering (n := n) refine deferAll := by
  intro adj fuel χ
  rfl

end Descend
end ChainDescent
