import ChainDescent.Spine
import ChainDescent.CanonicalForm
import ChainDescent.CostModel

/-!
# `descend` — the branching, resolver-parameterized descent (THE OBJECT)

(`docs/chain-descent-mixed-composition.md` §1.2–§1.4.)

Stage 0a fixed the spec: a canonizer is **`SoundOpt ∧ IsoInvariantOpt`** and nothing else (completeness and
flag-invariance are then free, `CanonicalForm.lean`). This file builds the **object** those two facts are proved
about, and states the **resolver contract** the two intended instances (consume / force) must meet.

## The object

  `descend rf R adj fuel χ : CostM (Option (Labelled n))`

At a node with colouring `χ`: if `χ` is discrete, emit the leaf matrix; otherwise select the target cell
(equivariantly, by least colour), form the branch list `B` over its vertices, let the **resolver** `R` narrow `B`
to `B'` (or *defer*, `B' = B`), recurse on each branch, and **aggregate**. Both the refiner and the resolver are
written in `CostM`, so `②` is a theorem about this same definition's `cost` — the executable, the correctness
proof and the cost proof are three views of ONE definition (§1.4, cost-model D1).

## ★ THE CONTRACT (hardened 2026-07-13) — TWO soundness routes, not one

The earlier contract asked every resolver for **branch covering** (`aggregate (narrowed) = aggregate (full)`).
That was **too strong, and provably so**: covering forces `descend R` to compute the *same value* as the
exhaustive `descend deferAll` (`canonForm?_eq_deferAll_of_covering` below), i.e. it pins the object to the
exhaustive branch-min — the `canonMin` anchor §1 explicitly retired. A **force** resolver in a *rigid* medium
narrows to a branch whose leaf differs from the discarded branches' leaves, so it can satisfy covering only if
the rigid solver already computes the global lex-min, i.e. only if it **knows the answer**. Covering did not
dodge the known-answer problem; it *encoded* it.

What the induction actually needs is weaker: **the narrowed-branch aggregate transports** (`NarrowTransport`).
Two independent sufficient conditions feed it, with complementary firing domains:

| route | narrowing is | discards are | aggregate | instance |
|---|---|---|---|---|
| **`Covering`** | *non*-equivariant (pick any orbit rep) | **redundant** (an automorphism maps them to a kept branch) | preserved | **consume** |
| **`NarrowEquivariant`** | **equivariant** (a structural function of `(adj, χ)`) | genuinely different | *changes, consistently* | **force** |

The force route yields a **different but equally valid** canonical form — which is exactly why deferral was
legitimate in the first place. No global lex-min, no known answer.

**Why this does not collapse into GI ∈ P** (`narrow_eq_branches_of_orbit`): equivariant narrowing is *impossible*
on a cell that is a single orbit. If `α` is a colouring-preserving automorphism then `α·adj = adj`, `α·χ = χ`,
so equivariance gives `narrow = α · narrow` — the narrowed set is invariant under the whole colouring-preserving
automorphism group, and a nonempty invariant subset of a single orbit is the whole orbit. So **force provably
cannot fire on a symmetric cell, and consume fires exactly there**: the two routes have complementary,
non-overlapping firing domains. Graphs where *neither* fires are the residue. That is the architecture.

The contract is also *checkable*: a narrowing is equivariant iff it is a pure function of `(adj, χ)` that never
breaks ties by vertex index — the same discipline that makes `indivOne` index-free.

## Three design commitments (bake-ins), honoured here

1. **Index-free individualization** (`indivOne`): a branch marks its vertex with a *parity bit* on the existing
   colour and **never** mentions `v.val`. An index-dependent individualization (as `IndivStep.default` uses)
   would leak the labelling into the leaf and no descent over it could be iso-invariant.
2. **Refinement is a PARAMETER**, so the `Encodable.encode` colour blow-up (the known `#eval` staller) is not
   baked in; the encode-free round drops in as the instance.
3. **Computable.** `rankPerm` is `noncomputable` (`Equiv.ofBijective`), so the leaf emit goes through `rankInv`
   and is *proved equal* to `labelledAdj (rankPerm …)`. No `Classical.choice` in any definition.
-/

namespace ChainDescent
namespace Descend

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)

variable {n : Nat}

/-- `Discrete` (colour-injectivity) is decidable — needed to branch on "is this a leaf?" *computably*. -/
instance decidableDiscrete (χ : Colouring n) : Decidable (Discrete χ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, χ i = χ j → i = j))

/-! ## 1. The computable leaf emit -/

/-- **Rank → vertex** (computable inverse of `Colouring.vertexRank`). -/
def rankInv (χ : Colouring n) (i : Fin n) : Fin n :=
  ((List.finRange n).find? (fun v => Colouring.vertexRank χ v = i)).getD i

theorem vertexRank_surj (χ : Colouring n) (h : Discrete χ) :
    Function.Surjective (Colouring.vertexRank χ) := by
  intro i
  obtain ⟨v, hv⟩ := (Colouring.rankPerm χ h).surjective i
  exact ⟨v, by rw [← Colouring.rankPerm_apply χ h v]; exact hv⟩

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

theorem rankInv_eq_symm (χ : Colouring n) (h : Discrete χ) (i : Fin n) :
    rankInv χ i = (Colouring.rankPerm χ h).symm i := by
  apply (Colouring.rankPerm χ h).injective
  rw [Equiv.apply_symm_apply, Colouring.rankPerm_apply]
  exact rankInv_spec χ h i

/-- **The leaf matrix** — relabel `adj` by colour-rank. Computable. -/
def leafMatrix (adj : AdjMatrix n) (χ : Colouring n) : Labelled n :=
  fun i j => adj.adj (rankInv χ i) (rankInv χ j)

theorem leafMatrix_eq_labelledAdj (adj : AdjMatrix n) (χ : Colouring n) (h : Discrete χ) :
    leafMatrix adj χ = labelledAdj (Colouring.rankPerm χ h) adj := by
  funext i j
  show adj.adj (rankInv χ i) (rankInv χ j)
      = adj.adj ((Colouring.rankPerm χ h).symm i) ((Colouring.rankPerm χ h).symm j)
  rw [rankInv_eq_symm χ h i, rankInv_eq_symm χ h j]

/-- **`①a` at the leaf** — the emitted matrix is a relabelling of the input. -/
theorem leafMatrix_sound (adj : AdjMatrix n) (χ : Colouring n) (h : Discrete χ) :
    ∃ π : Equiv.Perm (Fin n), leafMatrix adj χ = labelledAdj π adj :=
  ⟨Colouring.rankPerm χ h, leafMatrix_eq_labelledAdj adj χ h⟩

/-! ## 2. Index-free individualization (the X3 cut) -/

/-- **Individualize one vertex, index-free.** The chosen `v` gets an odd colour, everyone else an even one.
No `v.val` anywhere. -/
def indivOne (χ : Colouring n) (v : Fin n) : Colouring n :=
  fun u => if u = v then 2 * χ u + 1 else 2 * χ u

theorem indivOne_singleton (χ : Colouring n) (v : Fin n) :
    ∀ u, u ≠ v → indivOne χ v u ≠ indivOne χ v v := by
  intro u hu
  unfold indivOne
  rw [if_pos rfl, if_neg hu]
  omega

theorem indivOne_refines_off (χ : Colouring n) (v : Fin n) :
    ∀ x y, x ≠ v → y ≠ v → (indivOne χ v x = indivOne χ v y ↔ χ x = χ y) := by
  intro x y hx hy
  unfold indivOne
  rw [if_neg hx, if_neg hy]
  omega

/-! ## 3. The equivariant target-cell selector -/

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

A `List`, not a `Finset` (`Finset.toList` is **noncomputable**). The list is built in `Fin n` index order, so its
*order* is labelling-dependent — harmless, because the only thing done with it is a minimum (`aggregate`), which
depends only on the multiset (`aggregate_perm`). -/
def branches (χ : Colouring n) : List (Fin n) :=
  match targetColour χ with
  | none => []
  | some c => (List.finRange n).filter (fun v => χ v = c)

theorem mem_branches_iff {χ : Colouring n} {c : Nat} (h : targetColour χ = some c) (v : Fin n) :
    v ∈ branches χ ↔ χ v = c := by
  unfold branches
  rw [h]
  simp

/-- A non-discrete colouring has a nonempty branch list. (Used for the totality theorem: the descent really
does reach a leaf, so the flag is never a fuel artefact.) -/
theorem branches_ne_nil {χ : Colouring n} (h : ¬ Discrete χ) : branches χ ≠ [] := by
  -- ¬Discrete gives two vertices sharing a colour, so that colour's cell is non-singleton.
  have hex : ∃ i j : Fin n, χ i = χ j ∧ i ≠ j := by
    by_contra hc
    push_neg at hc
    exact h (fun i j hij => hc i j hij)
  obtain ⟨i, j, hij, hne⟩ := hex
  have hmem : χ i ∈ nonSingletonColours χ := by
    unfold nonSingletonColours
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    refine Finset.one_lt_card.mpr ⟨i, ?_, j, ?_, hne⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij.symm⟩
  obtain ⟨c, hc⟩ := Finset.min_of_nonempty ⟨χ i, hmem⟩
  have hcmem : c ∈ nonSingletonColours χ := Finset.mem_of_min hc
  have hcard : 1 < (cellOf χ c).card := (Finset.mem_filter.mp hcmem).2
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (cellOf χ c).card)
  have hχv : χ v = c := (Finset.mem_filter.mp hv).2
  have : v ∈ branches χ := (mem_branches_iff (by unfold targetColour; exact hc) v).mpr hχv
  exact fun hnil => by rw [hnil] at this; exact absurd this (List.not_mem_nil)

/-- Every branch vertex sits in a **non-singleton** cell: it has a same-coloured partner. (The engine of the
totality theorem — individualizing it strictly increases the colour count.) -/
theorem exists_partner_of_mem_branches {χ : Colouring n} {v : Fin n} (hv : v ∈ branches χ) :
    ∃ u, u ≠ v ∧ χ u = χ v := by
  unfold branches at hv
  cases hc : targetColour χ with
  | none => rw [hc] at hv; exact absurd hv (List.not_mem_nil)
  | some c =>
      rw [hc] at hv
      have hχv : χ v = c := by simpa using (List.mem_filter.mp hv).2
      have hcmem : c ∈ nonSingletonColours χ :=
        Finset.mem_of_min (by unfold targetColour at hc; exact hc)
      have hcard : 1 < (cellOf χ c).card := (Finset.mem_filter.mp hcmem).2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      have hχa : χ a = c := (Finset.mem_filter.mp ha).2
      have hχb : χ b = c := (Finset.mem_filter.mp hb).2
      by_cases hav : a = v
      · exact ⟨b, by rw [← hav]; exact fun hc' => hab hc'.symm, by rw [hχb, hχv]⟩
      · exact ⟨a, hav, by rw [hχa, hχv]⟩

/-- The branch list has **no duplicates** (it is a filter of `finRange`). Needed to turn "the narrowing has a
unique member" into "the narrowing has length 1" — i.e. to state a resolver's *firing* quantitatively. -/
theorem branches_nodup (χ : Colouring n) : (branches χ).Nodup := by
  unfold branches
  cases targetColour χ with
  | none => exact List.nodup_nil
  | some c => exact (List.nodup_finRange n).filter _

/-- A nodup list strictly inside another (some member of the bigger one is missing) is **strictly shorter**. The
currency of *partial* firing: "the resolver discarded at least one branch" ⟹ "the fan-out actually went down". -/
theorem length_lt_of_missing {L M : List (Fin n)} (hL : L.Nodup) (hM : M.Nodup)
    (hsub : ∀ x ∈ L, x ∈ M) {z : Fin n} (hz : z ∈ M) (hnz : z ∉ L) : L.length < M.length := by
  have hss : L.toFinset ⊂ M.toFinset := by
    refine ⟨fun x hx => List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx)), fun hc => ?_⟩
    exact hnz (List.mem_toFinset.mp (hc (List.mem_toFinset.mpr hz)))
  have h1 := List.toFinset_card_of_nodup hL
  have h2 := List.toFinset_card_of_nodup hM
  have := Finset.card_lt_card hss
  omega

/-! ## 4. The `Refiner` and the `Resolver`

Both are written in `CostM`, so the descent's `cost` projection can charge the refinement round and the
resolver's own work. (Without this, `descentCost` would count *nodes* only and `②` could not be a theorem about
this definition — §1.4.) The **resolver takes the adjacency**: both intended instances need the graph
(`matchOracle` verifies automorphisms; the rigid solver does linear algebra on it). -/

/-- A refinement round, with its cost. -/
abbrev Refiner (n : Nat) := AdjMatrix n → Colouring n → CostM (Colouring n)

/-- A branch-narrowing resolver, with its cost. `none` = defer (keep the full branch list). -/
abbrev Resolver (n : Nat) := AdjMatrix n → Colouring n → List (Fin n) → CostM (Option (List (Fin n)))

/-- The refiner's **value** projection. -/
def refineV (rf : Refiner n) (adj : AdjMatrix n) (χ : Colouring n) : Colouring n := (rf adj χ).1

/-- The **narrowed branch list** — the resolver's value projection, defaulting to the full branch list when it
defers. This is the object the whole contract is stated about. -/
def narrow (R : Resolver n) (adj : AdjMatrix n) (χ : Colouring n) : List (Fin n) :=
  ((R adj χ (branches χ)).1).getD (branches χ)

/-- The baseline resolver: never narrows (always defers). `descend deferAll` is the honest exhaustive-branching
object — sound and iso-invariant, but with no consumption or forcing. -/
def deferAll : Resolver n := fun _ _ _ => (none, 0)

@[simp] theorem narrow_deferAll (adj : AdjMatrix n) (χ : Colouring n) :
    narrow deferAll adj χ = branches χ := rfl

/-! ## 5. The aggregate -/

/-- All index pairs, in row-major order. -/
def allPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))

theorem mem_allPairs (p : Fin n × Fin n) : p ∈ allPairs n := by
  refine List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _, ?_⟩
  exact List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩

/-- Row-major flattening. Defined over `allPairs` so that injectivity is immediate. -/
def flatten (M : Labelled n) : List Nat :=
  (allPairs n).map (fun p => M p.1 p.2)

theorem flatten_injective {M N : Labelled n} (h : flatten M = flatten N) : M = N := by
  funext i j
  exact List.map_inj_left.mp h (i, j) (mem_allPairs (i, j))

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

**FUEL IS PER-LAYER, NOT A THREADED BUDGET (design commitment).** Every branch at a level receives the *same*
`fuel`, and the accumulated `cost` is summed but **never fed back into `fuel`**. There is therefore no shared
budget that an earlier (expensive) resolver could drain, causing a later *polynomial* resolver to flag through no
fault of its own. Consequence: **"resolver `R` never flags on class `X`" is a LOCAL statement about `R`**. Do not
"optimize" this into a threaded global budget — it would couple the resolvers' flag behaviour and destroy that
locality.

The discreteness test comes **before** the fuel test, so a leaf is emitted even at `fuel = 0` (this is what makes
`n = 0` behave, and what makes the totality theorem tight). Fuel exhaustion is a **placeholder** for the real
mutual-stall flag (Stage 4); `canonForm?_isSome` below proves it never actually fires for a genuine refiner. -/
def descend (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) :
    Nat → Colouring n → CostM (Option (Labelled n))
  | 0, χ => if _h : Discrete χ then (some (leafMatrix adj χ), 1) else (none, 1)
  | fuel + 1, χ =>
      if _h : Discrete χ then
        (some (leafMatrix adj χ), 1)
      else
        let rr := R adj χ (branches χ)
        let B' := rr.1.getD (branches χ)
        let results := B'.map (fun v =>
          let rfc := rf adj (indivOne χ v)
          let sub := descend rf R adj fuel rfc.1
          (sub.1, rfc.2 + sub.2))
        (aggregate (results.map Prod.fst), 1 + rr.2 + (results.map Prod.snd).sum)

/-- **The top-level canonizer object.** Depth budget `n` (each level commits one vertex). -/
def canonForm? (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) : Option (Labelled n) :=
  (descend rf R adj n (refineV rf adj (fun _ => 0))).1

/-- The descent's cost — the `cost` projection of the *same* definition. Now genuinely charges the refiner and
the resolver, not just the node count. -/
def descentCost (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) : Nat :=
  (rf adj (fun _ => 0)).2 + (descend rf R adj n (refineV rf adj (fun _ => 0))).2

/-! ### The value equations (the descent's `value` projection, isolated once and for all) -/

theorem descend_val_leaf (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : Discrete χ) : ∀ fuel, (descend rf R adj fuel χ).1 = some (leafMatrix adj χ)
  | 0 => by rw [descend, dif_pos h]
  | _ + 1 => by rw [descend, dif_pos h]

theorem descend_val_zero (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) : (descend rf R adj 0 χ).1 = none := by
  rw [descend, dif_neg h]

theorem descend_val_succ (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) (fuel : Nat) :
    (descend rf R adj (fuel + 1) χ).1
      = aggregate ((narrow R adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1)) := by
  rw [descend, dif_neg h]
  simp [narrow, refineV, List.map_map, Function.comp_def]

/-! ## 7. `SoundOpt descend` (`①a`)

Holds for **any** refiner and **any** resolver: narrowing only *removes* branches, and every surviving branch is
still a relabelling. This is why a mis-narrowing resolver costs a branch and never correctness. -/

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

theorem aggregate_mem {rs : List (Option (Labelled n))} {c : Labelled n}
    (h : aggregate rs = some c) : some c ∈ rs := by
  unfold aggregate at h
  by_cases hany : rs.any Option.isNone = true
  · rw [if_pos hany] at h; exact absurd h (by simp)
  · rw [if_neg hany] at h
    have hmem := lexMin?_mem _ h
    obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hmem
    exact hfa ▸ ha

theorem descend_sound (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n) (c : Labelled n),
      (descend rf R adj fuel χ).1 = some c → ∃ π : Equiv.Perm (Fin n), c = labelledAdj π adj := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ c h
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R adj hd 0] at h
        exact (Option.some.inj h) ▸ leafMatrix_sound adj χ hd
      · rw [descend_val_zero rf R adj hd] at h; exact absurd h (by simp)
  | succ fuel ih =>
      intro χ c h
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R adj hd (fuel + 1)] at h
        exact (Option.some.inj h) ▸ leafMatrix_sound adj χ hd
      · rw [descend_val_succ rf R adj hd fuel] at h
        obtain ⟨x, hx, hx1⟩ := List.mem_map.mp (aggregate_mem h)
        exact ih (refineV rf adj (indivOne χ x)) c hx1

/-- **`SoundOpt` for the top-level object** — the `Publication.canon_sound` obligation, discharged. -/
theorem soundOpt_canonForm? (rf : Refiner n) (R : Resolver n) :
    CanonSpec.SoundOpt (canonForm? (n := n) rf R) := by
  intro adj c h
  exact descend_sound rf R adj n _ c h

/-! ### `lexLe` is a total order ⟹ `aggregate` is a genuine minimum ⟹ PERMUTATION-INVARIANT

The obligation created by `branches` being an index-ordered `List`: under a relabelling the branch list is only a
**permutation** of the transported list, so the aggregate must depend on the *multiset* alone. -/

theorem lexLeList_refl : ∀ a : List Nat, lexLeList a a = true
  | [] => rfl
  | a :: as => by
      show (if a < a then true else if a < a then false else lexLeList as as) = true
      simp [lexLeList_refl as]

theorem lexLeList_total : ∀ a b : List Nat, lexLeList a b = true ∨ lexLeList b a = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
      show (if a < b then true else if b < a then false else lexLeList as bs) = true ∨
           (if b < a then true else if a < b then false else lexLeList bs as) = true
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (by simp [h])
      · subst h
        rcases lexLeList_total as bs with hh | hh
        · exact Or.inl (by simp [hh])
        · exact Or.inr (by simp [hh])
      · exact Or.inr (by simp [h, Nat.not_lt_of_gt h])

theorem lexLeList_trans : ∀ a b c : List Nat,
    lexLeList a b = true → lexLeList b c = true → lexLeList a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, hab, _ => by simp [lexLeList] at hab
  | _ :: _, _ :: _, [], _, hbc => by simp [lexLeList] at hbc
  | a :: as, b :: bs, c :: cs, hab, hbc => by
      show (if a < c then true else if c < a then false else lexLeList as cs) = true
      have hab' : (if a < b then true else if b < a then false else lexLeList as bs) = true := hab
      have hbc' : (if b < c then true else if c < b then false else lexLeList bs cs) = true := hbc
      rcases lt_trichotomy a b with h1 | h1 | h1
      · rcases lt_trichotomy b c with h2 | h2 | h2
        · exact by simp [lt_trans h1 h2]
        · subst h2; exact by simp [h1]
        · rcases lt_trichotomy a c with h3 | h3 | h3
          · exact by simp [h3]
          · subst h3; simp [h2, Nat.not_lt_of_gt h2] at hbc'
          · simp [h2, Nat.not_lt_of_gt h2] at hbc'
      · subst h1
        simp [lt_irrefl] at hab'
        rcases lt_trichotomy a c with h3 | h3 | h3
        · exact by simp [h3]
        · subst h3
          simp [lt_irrefl] at hbc' ⊢
          exact lexLeList_trans as bs cs hab' hbc'
        · simp [h3, Nat.not_lt_of_gt h3] at hbc'
      · simp [h1, Nat.not_lt_of_gt h1] at hab'

theorem lexLeList_antisymm : ∀ a b : List Nat,
    lexLeList a b = true → lexLeList b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, hba => by simp [lexLeList] at hba
  | _ :: _, [], hab, _ => by simp [lexLeList] at hab
  | a :: as, b :: bs, hab, hba => by
      have hab' : (if a < b then true else if b < a then false else lexLeList as bs) = true := hab
      have hba' : (if b < a then true else if a < b then false else lexLeList bs as) = true := hba
      rcases lt_trichotomy a b with h | h | h
      · simp [h, Nat.not_lt_of_gt h] at hba'
      · subst h
        simp [lt_irrefl] at hab' hba'
        rw [lexLeList_antisymm as bs hab' hba']
      · simp [h, Nat.not_lt_of_gt h] at hab'

theorem lexLe_refl (M : Labelled n) : lexLe M M = true := lexLeList_refl _
theorem lexLe_total (M N : Labelled n) : lexLe M N = true ∨ lexLe N M = true := lexLeList_total _ _
theorem lexLe_trans {M N P : Labelled n} (h1 : lexLe M N = true) (h2 : lexLe N P = true) :
    lexLe M P = true := lexLeList_trans _ _ _ h1 h2
theorem lexLe_antisymm {M N : Labelled n} (h1 : lexLe M N = true) (h2 : lexLe N M = true) :
    M = N := flatten_injective (lexLeList_antisymm _ _ h1 h2)

theorem lexMin?_eq_none_iff (l : List (Labelled n)) : lexMin? l = none ↔ l = [] := by
  cases l with
  | nil => simp [lexMin?]
  | cons M Ms =>
      constructor
      · intro h
        unfold lexMin? at h
        cases hM : lexMin? Ms with
        | none => rw [hM] at h; exact absurd h (by simp)
        | some N => rw [hM] at h; exact absurd h (by simp)
      · intro h; exact absurd h (by simp)

theorem lexMin?_le : ∀ (l : List (Labelled n)) (m : Labelled n), lexMin? l = some m →
    ∀ x ∈ l, lexLe m x = true := by
  intro l
  induction l with
  | nil => intro m h; exact absurd h (by simp [lexMin?])
  | cons M Ms ih =>
      intro m h x hx
      unfold lexMin? at h
      cases hM : lexMin? Ms with
      | none =>
          rw [hM] at h
          have hm : M = m := Option.some.inj h
          have hMs : Ms = [] := (lexMin?_eq_none_iff Ms).mp hM
          subst hMs
          have hxM : x = M := by simpa using hx
          subst hxM
          exact hm ▸ lexLe_refl _
      | some N =>
          rw [hM] at h
          have hm : (if lexLe M N then M else N) = m := Option.some.inj h
          have hNle : ∀ y ∈ Ms, lexLe N y = true := ih N hM
          rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]
            by_cases hle : lexLe M N = true
            · rw [if_pos hle] at hm; rw [← hm]; exact lexLe_refl M
            · rw [if_neg hle] at hm
              rw [← hm]
              rcases lexLe_total M N with h1 | h1
              · exact absurd h1 hle
              · exact h1
          · by_cases hle : lexLe M N = true
            · rw [if_pos hle] at hm; rw [← hm]; exact lexLe_trans hle (hNle x hx)
            · rw [if_neg hle] at hm; rw [← hm]; exact hNle x hx

theorem lexMin?_perm {l l' : List (Labelled n)} (h : l.Perm l') : lexMin? l = lexMin? l' := by
  cases hl : lexMin? l with
  | none =>
      have hlnil : l = [] := (lexMin?_eq_none_iff l).mp hl
      have hl'nil : l' = [] := by rw [hlnil] at h; exact h.nil_eq.symm
      rw [hl'nil]
      rfl
  | some m =>
      cases hl' : lexMin? l' with
      | none =>
          exfalso
          have hl'nil : l' = [] := (lexMin?_eq_none_iff l').mp hl'
          have hlnil : l = [] := by rw [hl'nil] at h; exact h.eq_nil
          rw [hlnil] at hl
          exact absurd hl (by simp [lexMin?])
      | some m' =>
          have h1 : lexLe m m' = true := lexMin?_le l m hl m' (h.mem_iff.mpr (lexMin?_mem l' hl'))
          have h2 : lexLe m' m = true := lexMin?_le l' m' hl' m (h.mem_iff.mp (lexMin?_mem l hl))
          rw [lexLe_antisymm h1 h2]

/-- **THE AGGREGATE IS PERMUTATION-INVARIANT** — the labelling-dependent branch *order* never leaks out. -/
theorem aggregate_perm {rs rs' : List (Option (Labelled n))} (h : rs.Perm rs') :
    aggregate rs = aggregate rs' := by
  have hany : rs.any Option.isNone = rs'.any Option.isNone := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hp⟩; exact ⟨x, h.mem_iff.mp hx, hp⟩
    · rintro ⟨x, hx, hp⟩; exact ⟨x, h.mem_iff.mpr hx, hp⟩
  unfold aggregate
  by_cases hcase : rs'.any Option.isNone = true
  · rw [if_pos hcase, if_pos (hany.trans hcase)]
  · rw [if_neg hcase, if_neg (by rw [hany]; exact hcase)]
    exact lexMin?_perm (h.filterMap id)

/-- **`lexMin?` depends only on the SET of candidates** — a minimum under a total order does. Strictly more
general than `lexMin?_perm`: multiplicities may differ too. -/
theorem lexMin?_congr_mem {l l' : List (Labelled n)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    lexMin? l = lexMin? l' := by
  cases hl : lexMin? l with
  | none =>
      have hlnil : l = [] := (lexMin?_eq_none_iff l).mp hl
      have hl'nil : l' = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have hxl := (h x).mpr hx
        rw [hlnil] at hxl
        exact absurd hxl (List.not_mem_nil)
      rw [hl'nil]; rfl
  | some m =>
      cases hl' : lexMin? l' with
      | none =>
          exfalso
          have hl'nil : l' = [] := (lexMin?_eq_none_iff l').mp hl'
          have hml' := (h m).mp (lexMin?_mem l hl)
          rw [hl'nil] at hml'
          exact absurd hml' (List.not_mem_nil)
      | some m' =>
          have h1 : lexLe m m' = true := lexMin?_le l m hl m' ((h m').mpr (lexMin?_mem l' hl'))
          have h2 : lexLe m' m = true := lexMin?_le l' m' hl' m ((h m).mp (lexMin?_mem l hl))
          rw [lexLe_antisymm h1 h2]

/-- **★ THE AGGREGATE DEPENDS ONLY ON THE SET OF BRANCH RESULTS.** Stronger than `aggregate_perm`, and it is what
the **consume** resolver needs: consume *drops* branches (it keeps one representative per orbit), so the branch
multiset genuinely shrinks — but the *value set* is unchanged, and that is all the aggregate sees. -/
theorem aggregate_congr_mem {rs rs' : List (Option (Labelled n))}
    (h : ∀ x, x ∈ rs ↔ x ∈ rs') : aggregate rs = aggregate rs' := by
  have hany : rs.any Option.isNone = rs'.any Option.isNone := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hp⟩; exact ⟨x, (h x).mp hx, hp⟩
    · rintro ⟨x, hx, hp⟩; exact ⟨x, (h x).mpr hx, hp⟩
  unfold aggregate
  by_cases hcase : rs'.any Option.isNone = true
  · rw [if_pos hcase, if_pos (hany.trans hcase)]
  · rw [if_neg hcase, if_neg (by rw [hany]; exact hcase)]
    refine lexMin?_congr_mem ?_
    intro x
    simp only [List.mem_filterMap, id_eq]
    constructor
    · rintro ⟨a, ha, hax⟩; exact ⟨a, (h a).mp ha, hax⟩
    · rintro ⟨a, ha, hax⟩; exact ⟨a, (h a).mpr ha, hax⟩

/-- The aggregate answers whenever the branch list is nonempty and no branch flagged. -/
theorem aggregate_ne_none {rs : List (Option (Labelled n))} (hne : rs ≠ [])
    (h : ∀ x ∈ rs, x ≠ none) : aggregate rs ≠ none := by
  have hany : ¬ (rs.any Option.isNone = true) := by
    intro hc
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp hc
    exact h x hx (Option.isNone_iff_eq_none.mp hp)
  unfold aggregate
  rw [if_neg hany]
  intro hc
  have hnil : rs.filterMap id = [] := (lexMin?_eq_none_iff _).mp hc
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  cases hxv : x with
  | none => exact h x hx hxv
  | some c =>
      have hmem : c ∈ rs.filterMap id := List.mem_filterMap.mpr ⟨x, hx, hxv⟩
      rw [hnil] at hmem
      exact absurd hmem (List.not_mem_nil)

/-! ## 8. The transport layer

Write `G' = relabelAdj σ G` and transport a colouring `χ` on `G` to `χ ∘ σ⁻¹` on `G'`. Every piece of the descent
transports, and the payoff is that the emitted matrices are **literally equal** — the `σ` cancels because the
output is indexed by colour-**ranks**, not by vertices. That single fact is the heart of `①b`. -/

/-- Transported colouring: `χ` on `G` becomes `χ ∘ σ⁻¹` on `relabelAdj σ G`. -/
def transportColouring (σ : Equiv.Perm (Fin n)) (χ : Colouring n) : Colouring n :=
  fun u => χ (σ.symm u)

theorem discrete_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    Discrete (transportColouring σ χ) ↔ Discrete χ := by
  constructor
  · intro h i j hij
    have := h (σ i) (σ j) (by simp [transportColouring, hij])
    exact σ.injective this
  · intro h i j hij
    unfold transportColouring at hij
    exact σ.symm.injective (h _ _ hij)

theorem vertexRank_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    Colouring.vertexRank (transportColouring σ χ) (σ v) = Colouring.vertexRank χ v := by
  have h : transportColouring σ χ = fun u => χ (σ.symm u) := rfl
  rw [h]
  simpa using vertexRank_comp χ σ.symm (σ v)

/-- **`indivOne` transports** — this is where the *index-free* choice pays: an index-dependent individualization
would NOT satisfy this. -/
theorem indivOne_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (v : Fin n) :
    indivOne (transportColouring σ χ) (σ v) = transportColouring σ (indivOne χ v) := by
  funext u
  show (if u = σ v then 2 * χ (σ.symm u) + 1 else 2 * χ (σ.symm u))
      = (if σ.symm u = v then 2 * χ (σ.symm u) + 1 else 2 * χ (σ.symm u))
  by_cases h : u = σ v
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun hc => h (by rw [← hc]; simp))]

theorem cellOf_card_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (c : Nat) :
    (cellOf (transportColouring σ χ) c).card = (cellOf χ c).card := by
  unfold cellOf transportColouring
  apply Finset.card_bij (fun v _ => σ.symm v)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a _ b _ hab
    exact σ.symm.injective hab
  · intro b hb
    refine ⟨σ b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa using hb

theorem image_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    Finset.univ.image (transportColouring σ χ) = Finset.univ.image χ := by
  unfold transportColouring
  apply Finset.ext
  intro c
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨σ.symm u, hu⟩
  · rintro ⟨v, hv⟩; exact ⟨σ v, by simpa using hv⟩

theorem targetColour_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    targetColour (transportColouring σ χ) = targetColour χ := by
  unfold targetColour nonSingletonColours
  rw [image_transport σ χ]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [cellOf_card_transport σ χ c]

/-- **The leaf matrix is LITERALLY EQUAL under transport** — the heart of `①b`. -/
theorem leafMatrix_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (h : Discrete χ) :
    leafMatrix (relabelAdj σ adj) (transportColouring σ χ) = leafMatrix adj χ := by
  have hd' : Discrete (transportColouring σ χ) := (discrete_transport σ χ).mpr h
  have hrank : ∀ i, rankInv (transportColouring σ χ) i = σ (rankInv χ i) := by
    intro i
    have hσ : Colouring.vertexRank (transportColouring σ χ) (σ (rankInv χ i)) = i := by
      rw [vertexRank_transport σ χ (rankInv χ i)]
      exact rankInv_spec χ h i
    have hinj : Function.Injective (Colouring.vertexRank (transportColouring σ χ)) := fun a b hab =>
      (Colouring.rankPerm (transportColouring σ χ) hd').injective hab
    exact hinj (by rw [rankInv_spec (transportColouring σ χ) hd' i, hσ])
  funext i j
  show (relabelAdj σ adj).adj (rankInv (transportColouring σ χ) i)
        (rankInv (transportColouring σ χ) j) = adj.adj (rankInv χ i) (rankInv χ j)
  rw [hrank i, hrank j]
  show adj.adj (σ.symm (σ (rankInv χ i))) (σ.symm (σ (rankInv χ j))) = _
  simp

/-- **The branch list transports UP TO PERMUTATION** (it is built in index order). -/
theorem branches_transport_perm (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    (branches (transportColouring σ χ)).Perm ((branches χ).map σ) := by
  unfold branches
  rw [targetColour_transport σ χ]
  cases hc : targetColour χ with
  | none => simp
  | some c =>
      refine List.perm_of_nodup_nodup_toFinset_eq
        ((List.nodup_finRange n).filter _) (((List.nodup_finRange n).filter _).map σ.injective) ?_
      ext u
      simp only [List.mem_toFinset, List.mem_filter, List.mem_map, List.mem_finRange,
        transportColouring, true_and, decide_eq_true_eq]
      constructor
      · intro hu; exact ⟨σ.symm u, hu, by simp⟩
      · rintro ⟨v, hv, rfl⟩; simpa using hv

/-! ## 9. ★ THE CONTRACT

`RefineEquivariant` is the refiner's obligation. `NarrowTransport` is the resolver's — stated as *exactly* what
the induction's branch case needs, and **fuel-graded**: it receives the induction hypothesis as an explicit
argument. That grading is what makes the **consume** instance possible without circularity — consume's covering
witness is an automorphism `α`, so its proof *is* `descend_transport` at `σ = α`, one fuel level down. -/

/-- **Hypothesis on the refiner: equivariance.** -/
def RefineEquivariant (rf : Refiner n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    refineV rf (relabelAdj σ adj) (transportColouring σ χ) = transportColouring σ (refineV rf adj χ)

/-- The descent's iso-invariance **at a given fuel** (the graded induction statement). -/
def TransportAt (rf : Refiner n) (R : Resolver n) (fuel : Nat) : Prop :=
  ∀ (adj : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (χ : Colouring n),
    (descend rf R (relabelAdj σ adj) fuel (transportColouring σ χ)).1
      = (descend rf R adj fuel χ).1

/-- **★ THE RESOLVER CONTRACT — the narrowed-branch aggregate transports.**

This is *precisely* the branch case of `descend_transport`, and nothing more. It is **weaker than covering**: it
does not demand that narrowing preserve the aggregate, only that whatever aggregate the narrowing produces is the
*same* on `G` and on `σ·G`. That is what lets **force** change the canonical form (to a different, equally valid
one) instead of being required to reproduce the exhaustive branch-min — i.e. instead of having to know the
answer.

The `TransportAt rf R fuel` argument is the **induction hypothesis, threaded in explicitly**, so an instance may
use the descent's own iso-invariance one fuel level down (which `consume` must). -/
def NarrowTransport (rf : Refiner n) (R : Resolver n) : Prop :=
  ∀ (fuel : Nat), TransportAt rf R fuel →
    ∀ (adj : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (χ : Colouring n), ¬ Discrete χ →
      aggregate ((narrow R (relabelAdj σ adj) (transportColouring σ χ)).map
          (fun v => (descend rf R (relabelAdj σ adj) fuel
              (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) v))).1))
        = aggregate ((narrow R adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

/-- The per-branch values agree under transport (`indivOne` equivariance + the refiner's equivariance + the IH).
Shared by both sufficient conditions below. -/
theorem branchVal_transport {rf : Refiner n} {R : Resolver n} (hre : RefineEquivariant rf)
    {fuel : Nat} (ih : TransportAt rf R fuel) (adj : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (χ : Colouring n) (v : Fin n) :
    (descend rf R (relabelAdj σ adj) fuel
        (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) (σ v)))).1
      = (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 := by
  rw [indivOne_transport σ χ v, hre σ adj (indivOne χ v)]
  exact ih adj σ (refineV rf adj (indivOne χ v))

/-! ### Sufficient condition 1 — **`Covering`** (the CONSUME route)

Narrowing does not change the aggregate, because every discarded branch's output is *already reachable* through a
kept one (an automorphism maps it there). The choice of representative is genuinely **non**-equivariant — orbit
members are indistinguishable to refinement — and that is fine: only the *result* transports. -/
def Covering (rf : Refiner n) (R : Resolver n) : Prop :=
  ∀ (adj : AdjMatrix n) (fuel : Nat) (χ : Colouring n),
    aggregate ((narrow R adj χ).map
        (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))
      = aggregate ((branches χ).map
        (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

/-- **★ THE FUEL-GRADED COVERING — the form `consume` actually satisfies.**

`Covering` (above) is *unconditional*: it asserts the narrowed aggregate equals the full one outright. But the
**consume** resolver cannot prove that from nothing — its covering witness is a colouring-preserving automorphism
`α`, and "the discarded branch and the kept one have the same `descend` value" **is** `descend_transport` at
`σ = α`. That is not circular (it descends on fuel), but it means the hypothesis must be able to *use the
induction hypothesis*. `CoveringAt` is `Covering` with `TransportAt rf R fuel` — the IH — threaded in, exactly as
`NarrowTransport` threads it.

**This is the graded form every real resolver instance should target.** `Covering ⟹ CoveringAt` trivially. -/
def CoveringAt (rf : Refiner n) (R : Resolver n) : Prop :=
  ∀ (fuel : Nat), TransportAt rf R fuel →
    ∀ (adj : AdjMatrix n) (χ : Colouring n),
      aggregate ((narrow R adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))
        = aggregate ((branches χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

theorem coveringAt_of_covering {rf : Refiner n} {R : Resolver n} (h : Covering rf R) :
    CoveringAt rf R := fun fuel _ adj χ => h adj fuel χ

theorem narrowTransport_of_coveringAt {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hcov : CoveringAt rf R) : NarrowTransport rf R := by
  intro fuel ih adj σ χ _
  rw [hcov fuel ih (relabelAdj σ adj) (transportColouring σ χ), hcov fuel ih adj χ]
  refine aggregate_perm (((branches_transport_perm σ χ).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq
    (List.map_congr_left (fun v _ => branchVal_transport hre ih adj σ χ v))

theorem narrowTransport_of_covering {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hcov : Covering rf R) : NarrowTransport rf R :=
  narrowTransport_of_coveringAt hre (coveringAt_of_covering hcov)

/-! ### Sufficient condition 2 — **`NarrowEquivariant`** (the FORCE route)

The narrowing is a structural function of `(adj, χ)`: it transports under `σ` (up to the same index-ordering
permutation `branches` already has). The discarded branches are genuinely *different* — the aggregate **changes**
— but it changes *consistently* on `G` and `σ·G`, which is all iso-invariance ever needed. This is the route the
rigid solver takes, and it needs no knowledge of the final answer. -/
def NarrowEquivariant (R : Resolver n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    (narrow R (relabelAdj σ adj) (transportColouring σ χ)).Perm ((narrow R adj χ).map σ)

theorem narrowTransport_of_narrowEquivariant {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hne : NarrowEquivariant R) : NarrowTransport rf R := by
  intro fuel ih adj σ χ _
  refine aggregate_perm (((hne σ adj χ).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq
    (List.map_congr_left (fun v _ => branchVal_transport hre ih adj σ χ v))

/-- `deferAll` takes **both** routes (it never narrows). -/
theorem covering_deferAll (rf : Refiner n) : Covering (n := n) rf deferAll := by
  intro adj fuel χ; rfl

theorem narrowEquivariant_deferAll : NarrowEquivariant (n := n) deferAll := by
  intro σ adj χ
  simpa using branches_transport_perm σ χ

theorem narrowTransport_deferAll {rf : Refiner n} (hre : RefineEquivariant rf) :
    NarrowTransport (n := n) rf deferAll :=
  narrowTransport_of_covering hre (covering_deferAll rf)

/-! ### Sufficient condition 3 — **`CoveringOfAt`** (the HYBRID route: force **then** consume)

The two routes above are not composable as stated, and the engine (IR §11.11) is **interleaved** — almost every
real residue needs *both* moves at the *same* cell (consume the symmetry that is there, force the rest). A
composite resolver is neither `Covering` (force changes the aggregate) nor `NarrowEquivariant` (consume's choice
of orbit representative is not equivariant), so it satisfies **neither** sufficient condition, and the mixed
object — the one this whole track is named for — could not be built.

The fix is to see that both routes are the **same** condition against different *reference lists*. Covering says
"the narrowed aggregate equals the aggregate over `branches`"; equivariance says "the narrowed aggregate equals
the aggregate over `narrow` itself, which transports". Generalize the reference to an arbitrary **equivariant
intermediate narrowing `N`**:

> **`R` covers an equivariant `N`** — the aggregate over `narrow R` equals the aggregate over `N`, and `N`
> transports.

`Covering` is the case `N = branches`; `NarrowEquivariant` is the case `N = narrow R`. And the composite is the
case `N = the FORCED set`: force narrows equivariantly to `N`, then consume covers `N` (its discards are
redundant *within* `N`, because the force key is constant on automorphism orbits, so the forced set is a **union
of orbits** and an orbit representative never escapes it). One contract, three instances. -/

/-- An **intermediate narrowing** — the reference list a resolver's aggregate is compared against. -/
abbrev NarrowFn (n : Nat) := AdjMatrix n → Colouring n → List (Fin n)

/-- The intermediate narrowing transports (same shape as `NarrowEquivariant`, for a bare function). -/
def NarrowFnEquivariant (N : NarrowFn n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n),
    (N (relabelAdj σ adj) (transportColouring σ χ)).Perm ((N adj χ).map σ)

/-- **`R`'s narrowing covers `N`** — fuel-graded, exactly as `CoveringAt` is (the consume half of a composite
still needs the induction hypothesis to know its discards are value-equal). -/
def CoveringOfAt (rf : Refiner n) (R : Resolver n) (N : NarrowFn n) : Prop :=
  ∀ (fuel : Nat), TransportAt rf R fuel →
    ∀ (adj : AdjMatrix n) (χ : Colouring n),
      aggregate ((narrow R adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))
        = aggregate ((N adj χ).map
          (fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1))

/-- **★★ THE GENERAL RESOLVER CONTRACT — covering an equivariant intermediate.** Sandwich: the narrowed aggregate
equals `N`'s on each side, and `N`'s transports. Subsumes both earlier routes and admits the composite. -/
theorem narrowTransport_of_coveringOfAt {rf : Refiner n} {R : Resolver n} {N : NarrowFn n}
    (hre : RefineEquivariant rf) (hNe : NarrowFnEquivariant N) (hcov : CoveringOfAt rf R N) :
    NarrowTransport rf R := by
  intro fuel ih adj σ χ _
  rw [hcov fuel ih (relabelAdj σ adj) (transportColouring σ χ), hcov fuel ih adj χ]
  refine aggregate_perm (((hNe σ adj χ).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq
    (List.map_congr_left (fun v _ => branchVal_transport hre ih adj σ χ v))

/-- `Covering` is the hybrid route at `N = branches`. -/
theorem narrowFnEquivariant_branches : NarrowFnEquivariant (n := n) (fun _ χ => branches χ) :=
  fun σ _ χ => branches_transport_perm σ χ

/-! ## 10. `IsoInvariantOpt descend` (the capstone) -/

/-- **`①b`/`①c` — the descent is ISO-INVARIANT.** The branch case is *exactly* the resolver contract — note it
needs **no** refiner hypothesis: `RefineEquivariant` is used only to *establish* `NarrowTransport` (in the two
sufficient conditions) and to transport the root colouring. `NarrowTransport` is the whole per-node obligation. -/
theorem descend_transport {rf : Refiner n} {R : Resolver n} (hnt : NarrowTransport rf R) :
    ∀ fuel, TransportAt rf R fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro adj σ χ
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R _ ((discrete_transport σ χ).mpr hd) 0,
            descend_val_leaf rf R adj hd 0, leafMatrix_transport σ adj χ hd]
      · rw [descend_val_zero rf R _ (fun hc => hd ((discrete_transport σ χ).mp hc)),
            descend_val_zero rf R adj hd]
  | succ fuel ih =>
      intro adj σ χ
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R _ ((discrete_transport σ χ).mpr hd) (fuel + 1),
            descend_val_leaf rf R adj hd (fuel + 1), leafMatrix_transport σ adj χ hd]
      · rw [descend_val_succ rf R _ (fun hc => hd ((discrete_transport σ χ).mp hc)) fuel,
            descend_val_succ rf R adj hd fuel]
        exact hnt fuel ih adj σ χ hd

theorem isoInvariantOpt_canonForm? {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransport rf R) :
    CanonSpec.IsoInvariantOpt (canonForm? (n := n) rf R) := by
  intro σ adj
  show (descend rf R (relabelAdj σ adj) n (refineV rf (relabelAdj σ adj) (fun _ => 0))).1
      = (descend rf R adj n (refineV rf adj (fun _ => 0))).1
  have h0 : refineV rf (relabelAdj σ adj) (fun _ => 0)
      = transportColouring σ (refineV rf adj (fun _ => 0)) := by
    simpa [transportColouring] using hre σ adj (fun _ => 0)
  rw [h0]
  exact descend_transport hnt n adj σ (refineV rf adj (fun _ => 0))

/-- **★ THE CAPSTONE — `descend` IS A CANONICAL FORM.** Sound ∧ iso-invariant, hence (Stage 0a) a *complete*
isomorphism invariant with an iso-invariant flag: `①a`, `①b`, `①c` all discharged for the real object, modulo
exactly two carried hypotheses — the refiner's equivariance and the resolver's `NarrowTransport` contract. -/
theorem isCanonicalFormOpt_canonForm? {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransport rf R) :
    CanonSpec.IsCanonicalFormOpt (canonForm? (n := n) rf R) :=
  ⟨soundOpt_canonForm? rf R, isoInvariantOpt_canonForm? hre hnt⟩

/-- **Completeness, free.** The `Publication.canon_complete` obligation. -/
theorem canonForm?_complete {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransport rf R)
    (G H : AdjMatrix n) (cG cH : Labelled n)
    (hG : canonForm? rf R G = some cG) (hH : canonForm? rf R H = some cH) :
    CanonSpec.GraphIso G H ↔ cG = cH :=
  CanonSpec.complete_of_isCanonicalFormOpt (isCanonicalFormOpt_canonForm? hre hnt) G H cG cH hG hH

/-- **The flag is iso-invariant, free.** The `Publication.flag_iso_invariant` obligation. -/
theorem canonForm?_flag_iso_invariant {rf : Refiner n} {R : Resolver n}
    (hre : RefineEquivariant rf) (hnt : NarrowTransport rf R)
    {G H : AdjMatrix n} (h : CanonSpec.GraphIso G H) :
    canonForm? rf R G = none ↔ canonForm? rf R H = none :=
  CanonSpec.flag_iso_invariant_of_isoInvariantOpt (isoInvariantOpt_canonForm? hre hnt) h

/-! ## 11. ★★ WHY COVERING WAS TOO STRONG, AND WHY THE DESIGN DOES NOT COLLAPSE

Two theorems that together justify the two-route contract. -/

/-- **★ Covering makes a resolver VALUE-INVISIBLE.** A covering resolver computes *exactly* the exhaustive
branch-min — it can change the **cost**, never the **answer**. So demanding `Covering` of every resolver pins the
object to `canonMin` (the global-lex-min anchor the design retired), and a **force** resolver could satisfy it
only by already computing that min — i.e. only by knowing the answer. This is the theorem that retired the
one-contract design. -/
theorem canonForm?_eq_deferAll_of_covering {rf : Refiner n} {R : Resolver n}
    (hcov : Covering rf R) (adj : AdjMatrix n) :
    canonForm? rf R adj = canonForm? rf deferAll adj := by
  have key : ∀ (fuel : Nat) (χ : Colouring n),
      (descend rf R adj fuel χ).1 = (descend rf deferAll adj fuel χ).1 := by
    intro fuel
    induction fuel with
    | zero =>
        intro χ
        by_cases hd : Discrete χ
        · rw [descend_val_leaf rf R adj hd 0, descend_val_leaf rf deferAll adj hd 0]
        · rw [descend_val_zero rf R adj hd, descend_val_zero rf deferAll adj hd]
    | succ fuel ih =>
        intro χ
        by_cases hd : Discrete χ
        · rw [descend_val_leaf rf R adj hd (fuel + 1), descend_val_leaf rf deferAll adj hd (fuel + 1)]
        · rw [descend_val_succ rf R adj hd fuel, descend_val_succ rf deferAll adj hd fuel,
              hcov adj fuel χ, narrow_deferAll]
          exact congrArg aggregate (List.map_congr_left (fun v _ => ih (refineV rf adj (indivOne χ v))))
  exact key n _

/-- An **equivariant** narrowing is invariant under every colouring-preserving automorphism. (`α·adj = adj` and
`α·χ = χ` turn `NarrowEquivariant` into `narrow = α · narrow`.) -/
theorem narrow_aut_invariant {R : Resolver n} (hne : NarrowEquivariant R)
    (adj : AdjMatrix n) (χ : Colouring n) (α : Equiv.Perm (Fin n))
    (hadj : relabelAdj α adj = adj) (hχ : transportColouring α χ = χ) (v : Fin n) :
    α v ∈ narrow R adj χ ↔ v ∈ narrow R adj χ := by
  have hp : (narrow R adj χ).Perm ((narrow R adj χ).map α) := by
    have h := hne α adj χ
    rwa [hadj, hχ] at h
  constructor
  · intro h
    obtain ⟨u, hu, hsu⟩ := List.mem_map.mp (hp.mem_iff.mp h)
    rwa [α.injective hsu] at hu
  · intro h
    exact hp.mem_iff.mpr (List.mem_map.mpr ⟨v, h, rfl⟩)

/-- **★★ THE NON-COLLAPSE THEOREM — an equivariant narrowing CANNOT FIRE on an orbit cell.**

If the target cell is a single orbit of the colouring-preserving automorphism group, then any nonempty
equivariant narrowing of it is the **whole cell**. So `force` (the equivariant route) provably cannot fire on a
*symmetric* cell — which is exactly where `consume` (the covering route) fires, and consume is licensed there
*precisely because* its choice is non-equivariant.

The two routes therefore have **complementary, non-overlapping firing domains**, and the design does not collapse
into "narrow to one branch everywhere" (which would be GI ∈ P). Equivariant narrowing is available only where the
cell is genuinely *not* an orbit **and** the resolver can structurally see the distinction (the linear/ring
structure the rigid solver reads). Graphs where neither route fires are **the residue** — which is the whole
point of the architecture. -/
theorem narrow_eq_branches_of_orbit {R : Resolver n} (hne : NarrowEquivariant R)
    (adj : AdjMatrix n) (χ : Colouring n)
    (hsub : ∀ v ∈ narrow R adj χ, v ∈ branches χ)
    (hnil : narrow R adj χ ≠ [])
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ α : Equiv.Perm (Fin n),
        relabelAdj α adj = adj ∧ transportColouring α χ = χ ∧ α u = w) :
    ∀ w ∈ branches χ, w ∈ narrow R adj χ := by
  intro w hw
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hnil
  obtain ⟨α, hadj, hχ, hαu⟩ := horb u (hsub u hu) w hw
  have := (narrow_aut_invariant hne adj χ α hadj hχ u).mpr hu
  rwa [hαu] at this

/-! ## 12. Totality — the flag is NOT a fuel artefact

The capstone holds for *any* `RefineEquivariant` refiner — including the degenerate constant one, which satisfies
it by `rfl` and flags on **every** graph. A theorem that is true only of a canonizer that never answers is
worthless, so we earn non-vacuity here: a refiner that genuinely **refines** (never merges two colour classes)
reaches a leaf within `n` levels, so `canonForm?` never flags. Fuel exhaustion is then a pure depth bound, and
`none` is free to acquire its real (Stage 4) mutual-stall meaning. -/

/-- The number of colour classes. -/
def ncol (χ : Colouring n) : Nat := (Finset.univ.image χ).card

theorem ncol_le (χ : Colouring n) : ncol χ ≤ n := by
  unfold ncol
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := χ)

theorem discrete_of_ncol_eq {χ : Colouring n} (h : ncol χ = n) : Discrete χ := by
  intro i j hij
  have hcard : (Finset.univ.image χ).card = (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; exact h
  exact Finset.injOn_of_card_image_eq hcard (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- **Individualizing a branch vertex strictly increases the colour count.** (It splits a non-singleton cell:
the old colour survives on the partner, and the new odd colour is fresh by parity.) -/
theorem ncol_lt_indivOne {χ : Colouring n} {v : Fin n} (hv : v ∈ branches χ) :
    ncol χ < ncol (indivOne χ v) := by
  obtain ⟨u, huv, hχu⟩ := exists_partner_of_mem_branches hv
  -- The doubled old colours, plus the fresh odd colour, all occur in `indivOne χ v`.
  have hsub : insert (2 * χ v + 1) ((Finset.univ.image χ).image (fun c => 2 * c))
      ⊆ Finset.univ.image (indivOne χ v) := by
    intro d hd
    rcases Finset.mem_insert.mp hd with hd | hd
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by simp [indivOne, hd]⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
      -- pick a representative of colour `χ x` that is not `v` (the partner `u` when `χ x = χ v`)
      by_cases hxv : x = v
      · refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
        simp [indivOne, huv, hχu, hxv]
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by simp [indivOne, hxv]⟩
  have hnotmem : (2 * χ v + 1) ∉ (Finset.univ.image χ).image (fun c => 2 * c) := by
    intro hc
    obtain ⟨c, _, hcc⟩ := Finset.mem_image.mp hc
    omega
  have hdouble : ((Finset.univ.image χ).image (fun c => 2 * c)).card = ncol χ :=
    Finset.card_image_of_injective _ (fun a b hab => by omega)
  calc ncol χ = ((Finset.univ.image χ).image (fun c => 2 * c)).card := hdouble.symm
    _ < (insert (2 * χ v + 1) ((Finset.univ.image χ).image (fun c => 2 * c))).card := by
        rw [Finset.card_insert_of_notMem hnotmem]; omega
    _ ≤ ncol (indivOne χ v) := Finset.card_le_card hsub

/-- **The refiner genuinely refines**: it never merges two colour classes. (Colour refinement satisfies this by
construction; the degenerate constant refiner does not — which is exactly what this rules out.) -/
def RefineSplits (rf : Refiner n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n) (x y : Fin n),
    refineV rf adj χ x = refineV rf adj χ y → χ x = χ y

theorem ncol_le_refine {rf : Refiner n} (hs : RefineSplits rf) (adj : AdjMatrix n) (χ : Colouring n) :
    ncol χ ≤ ncol (refineV rf adj χ) := by
  classical
  -- Send each old colour to the new colour of one of its representatives. `RefineSplits` says the new
  -- colouring separates only *within* old classes, so this map is injective on the old palette.
  set f : Nat → Nat := fun c =>
    if h : ∃ x : Fin n, χ x = c then refineV rf adj χ (Classical.choose h) else 0 with hf
  have hrep : ∀ c ∈ Finset.univ.image χ, ∃ x : Fin n, χ x = c := by
    intro c hc
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
    exact ⟨x, hx⟩
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro c hc
    have h := hrep c hc
    refine Finset.mem_image.mpr ⟨Classical.choose h, Finset.mem_univ _, ?_⟩
    rw [hf]
    simp only [dif_pos h]
  · intro c1 hc1 c2 hc2 heq
    have h1 := hrep c1 (by simpa using hc1)
    have h2 := hrep c2 (by simpa using hc2)
    rw [hf] at heq
    simp only [dif_pos h1, dif_pos h2] at heq
    have := hs adj χ (Classical.choose h1) (Classical.choose h2) heq
    rw [Classical.choose_spec h1, Classical.choose_spec h2] at this
    exact this

/-- A resolver whose narrowing stays inside the branch list and never empties it. Both intended instances satisfy
this (consume keeps an orbit representative; force keeps the determined branch). -/
def NarrowProper (R : Resolver n) : Prop :=
  (∀ (adj : AdjMatrix n) (χ : Colouring n), ¬ Discrete χ → narrow R adj χ ≠ []) ∧
  (∀ (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n), v ∈ narrow R adj χ → v ∈ branches χ)

theorem narrowProper_deferAll : NarrowProper (n := n) deferAll :=
  ⟨fun _ χ h => by simpa using branches_ne_nil h, fun _ _ _ h => by simpa using h⟩

/-- **Properness at ONE graph.** `descend_ne_none` never uses the resolver's properness at any graph other than the
one it is descending on, so the totality theorem is really a *per-graph* statement. That matters for `③`: whether a
graph is handled is a property of **that graph**, so a residue predicate must not be forced to quantify over all
graphs (`Residue.lean`). -/
def NarrowProperAt (R : Resolver n) (adj : AdjMatrix n) : Prop :=
  (∀ χ : Colouring n, ¬ Discrete χ → narrow R adj χ ≠ []) ∧
  (∀ (χ : Colouring n) (v : Fin n), v ∈ narrow R adj χ → v ∈ branches χ)

theorem narrowProperAt_of_narrowProper {R : Resolver n} (hp : NarrowProper R) (adj : AdjMatrix n) :
    NarrowProperAt R adj :=
  ⟨fun χ h => hp.1 adj χ h, fun χ v h => hp.2 adj χ v h⟩

theorem descend_ne_none_at {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    {adj : AdjMatrix n} (hp : NarrowProperAt R adj) :
    ∀ (fuel : Nat) (χ : Colouring n), n ≤ ncol χ + fuel → (descend rf R adj fuel χ).1 ≠ none := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ hb
      have hd : Discrete χ := discrete_of_ncol_eq (le_antisymm (ncol_le χ) (by omega))
      rw [descend_val_leaf rf R adj hd 0]
      exact fun hc => by simp at hc
  | succ fuel ih =>
      intro χ hb
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R adj hd (fuel + 1)]
        exact fun hc => by simp at hc
      · rw [descend_val_succ rf R adj hd fuel]
        refine aggregate_ne_none ?_ ?_
        · exact fun hc => (hp.1 χ hd) (List.map_eq_nil_iff.mp hc)
        · intro x hx
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
          refine ih (refineV rf adj (indivOne χ v)) ?_
          have h1 : ncol χ < ncol (indivOne χ v) := ncol_lt_indivOne (hp.2 χ v hv)
          have h2 : ncol (indivOne χ v) ≤ ncol (refineV rf adj (indivOne χ v)) :=
            ncol_le_refine hs adj (indivOne χ v)
          omega

/-- **`③`-facing totality: the descent answers on a graph whose resolver is proper THERE.** -/
theorem canonForm?_ne_none_at {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    {adj : AdjMatrix n} (hp : NarrowProperAt R adj) : canonForm? rf R adj ≠ none :=
  descend_ne_none_at hs hp n _
    (by have := Nat.zero_le (ncol (refineV rf adj (fun _ => 0))); omega)

/-! ### Reachability — the node colourings the descent can actually visit

`NarrowProperAt` still quantifies over **all** colourings, but the descent only ever sees colourings built by its
own root/branch steps. `Reaches` names that set — as an **over-approximation** (any branch vertex, not just the
resolver-kept ones), so it is *resolver-independent*: strengthening a resolver only shrinks the true visit set,
and everything proved `∀ χ, Reaches rf adj χ → …` stays valid with no re-proof. This is what lets a capability
predicate (`Residue.Handled`) be discharged from **structural** hypotheses (the seal speaks only about committed
individualization paths, never about arbitrary colourings — `CellsAreOrbits` genuinely *fails* at colourings the
descent never visits, so a `∀ χ` predicate was undischargeable in principle). -/

/-- **The descent's reachable node colourings** (over-approximated): the refined root, closed under
"individualize a branch vertex of a non-discrete node, then refine". Every colouring `descend rf R` actually
visits satisfies this for *any* resolver whose narrowing stays inside `branches` (`NarrowProperAt`'s second
half), because the branch step here allows **every** branch vertex. -/
inductive Reaches (rf : Refiner n) (adj : AdjMatrix n) : Colouring n → Prop
  | root : Reaches rf adj (refineV rf adj (fun _ => 0))
  | step {χ : Colouring n} {v : Fin n} :
      Reaches rf adj χ → ¬ Discrete χ → v ∈ branches χ →
      Reaches rf adj (refineV rf adj (indivOne χ v))

/-- **Totality from properness on the REACHED set only.** The `∀ χ` of `descend_ne_none_at` was never needed:
the induction only ever applies the properness hypothesis at colourings the descent visits, all of which are
`Reaches`-reachable (the subset half `hsub` is what re-establishes reachability for each child). -/
theorem descend_ne_none_reaches {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    {adj : AdjMatrix n}
    (hne : ∀ χ : Colouring n, Reaches rf adj χ → ¬ Discrete χ → narrow R adj χ ≠ [])
    (hsub : ∀ (χ : Colouring n) (v : Fin n), v ∈ narrow R adj χ → v ∈ branches χ) :
    ∀ (fuel : Nat) (χ : Colouring n), Reaches rf adj χ → n ≤ ncol χ + fuel →
      (descend rf R adj fuel χ).1 ≠ none := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ _ hb
      have hd : Discrete χ := discrete_of_ncol_eq (le_antisymm (ncol_le χ) (by omega))
      rw [descend_val_leaf rf R adj hd 0]
      exact fun hc => by simp at hc
  | succ fuel ih =>
      intro χ hr hb
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R adj hd (fuel + 1)]
        exact fun hc => by simp at hc
      · rw [descend_val_succ rf R adj hd fuel]
        refine aggregate_ne_none ?_ ?_
        · exact fun hc => (hne χ hr hd) (List.map_eq_nil_iff.mp hc)
        · intro x hx
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
          refine ih (refineV rf adj (indivOne χ v)) (hr.step hd (hsub χ v hv)) ?_
          have h1 : ncol χ < ncol (indivOne χ v) := ncol_lt_indivOne (hsub χ v hv)
          have h2 : ncol (indivOne χ v) ≤ ncol (refineV rf adj (indivOne χ v)) :=
            ncol_le_refine hs adj (indivOne χ v)
          omega

/-- **`③`-facing totality, reached-set form: the descent answers on a graph whose resolver is proper at every
REACHED node.** Strictly more applicable than `canonForm?_ne_none_at` (whose `NarrowProperAt` quantifies over all
colourings): the root is reachable by construction, so this needs properness only where the descent can go. -/
theorem canonForm?_ne_none_reaches {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    {adj : AdjMatrix n}
    (hne : ∀ χ : Colouring n, Reaches rf adj χ → ¬ Discrete χ → narrow R adj χ ≠ [])
    (hsub : ∀ (χ : Colouring n) (v : Fin n), v ∈ narrow R adj χ → v ∈ branches χ) :
    canonForm? rf R adj ≠ none :=
  descend_ne_none_reaches hs hne hsub n _ Reaches.root
    (by have := Nat.zero_le (ncol (refineV rf adj (fun _ => 0))); omega)

/-- **★ TOTALITY — the descent always reaches a leaf.** With a genuinely-refining refiner and a proper resolver,
`fuel` suffices whenever `n ≤ ncol χ + fuel`. -/
theorem descend_ne_none {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    (hp : NarrowProper R) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n), n ≤ ncol χ + fuel → (descend rf R adj fuel χ).1 ≠ none := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ hb
      have hd : Discrete χ := discrete_of_ncol_eq (le_antisymm (ncol_le χ) (by omega))
      rw [descend_val_leaf rf R adj hd 0]
      exact fun hc => by simp at hc
  | succ fuel ih =>
      intro χ hb
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R adj hd (fuel + 1)]
        exact fun hc => by simp at hc
      · rw [descend_val_succ rf R adj hd fuel]
        refine aggregate_ne_none ?_ ?_
        · exact fun hc => (hp.1 adj χ hd) (List.map_eq_nil_iff.mp hc)
        · intro x hx
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
          refine ih (refineV rf adj (indivOne χ v)) ?_
          have h1 : ncol χ < ncol (indivOne χ v) := ncol_lt_indivOne (hp.2 adj χ v hv)
          have h2 : ncol (indivOne χ v) ≤ ncol (refineV rf adj (indivOne χ v)) :=
            ncol_le_refine hs adj (indivOne χ v)
          omega

/-- **★ THE CANONIZER ANSWERS.** `canonForm?` never flags for a genuinely-refining refiner and a proper
resolver — so the capstone is about a canonizer that *computes*, not one that flags on everything, and the
`none` branch is free for its real (Stage 4) mutual-stall meaning. -/
theorem canonForm?_ne_none {rf : Refiner n} {R : Resolver n} (hs : RefineSplits rf)
    (hp : NarrowProper R) (adj : AdjMatrix n) : canonForm? rf R adj ≠ none :=
  descend_ne_none hs hp adj n _ (by have := Nat.zero_le (ncol (refineV rf adj (fun _ => 0))); omega)

end Descend
end ChainDescent
