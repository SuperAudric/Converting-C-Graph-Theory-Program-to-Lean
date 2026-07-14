import ChainDescent.Descend
import ChainDescent.Refine

/-!
# `force` — the RIGID resolver route (the `NarrowEquivariant` route)

(`docs/chain-descent-mixed-composition.md` §1.3 + Stage 3; `chain-descent-ir-blindspot-solver.md` §11.12.)

The second of the two resolver instances. Where **consume** discards branches because they are *redundant* (an
automorphism maps them onto a kept one), **force** discards branches that are genuinely **different** — it keeps
the branch the structure *determines*. That is sound not because the discards lose, but because the choice is
**structural**: it is a pure function of `(adj, χ)`, so it transports under relabelling, so the descent stays
iso-invariant. The canonical form it produces is a *different but equally valid* one — legitimate for exactly the
reason deferral always was.

## ★ THE WHOLE ① OBLIGATION OF A FORCE RESOLVER IS `KeyEquivariant`

This file provides the **combinator**, not one hard-wired solver:

  `forceBy key : Resolver n`  — keep the branches whose **key is least**.

A `Key` is any vertex invariant `AdjMatrix n → Colouring n → Fin n → List Nat`. Its *only* soundness obligation is

  **`KeyEquivariant key`** — `key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = key adj χ v`

i.e. *the key never breaks ties by vertex index*, the same discipline that makes `indivOne` index-free. Given that,
`narrowEquivariant_forceBy` discharges the resolver contract and `force_canonizer` gives `①a`/`①b`/`①c` **plus
totality**, unconditionally.

**The rigid solver (Algorithm R) drops in here as a stronger `key`** — its solve-derived invariant — and owes
**nothing but `KeyEquivariant`**. This is the re-basing of the rigid seal's §11.12 onto the resolver contract:

* **P1** (minimal forcing-circuits generate the row-space) and **P3** (solve / canonical-form correctness) are
  **not** ① obligations under this contract. If extraction under-generates, or the solve is weak, the key simply
  separates fewer vertices — the resolver narrows less and the descent branches more. *Sound.*
* ⚠ **But relocation is not elimination.** Narrowing less ⟹ more branching ⟹ budget exhaustion ⟹ flag ⟹ the input
  lands in `UnhandledResidue`. **A key that never separates is a canonizer that flags everything: correct, and
  worthless.** So P1/P3 keep their *full* content — they are exactly what determines **how much** the key sees, and
  they now live on the **②/firing** side of the ledger, which is where the "polynomial-**or-flag**" headline lives.

## ★★ Why this does not collapse into GI ∈ P

`forceBy` **provably cannot fire on a symmetric cell** (`narrow_eq_branches_of_orbit`, specialized here as
`forceBy_no_narrowing_on_orbit`): a colouring-preserving automorphism `α` forces `narrow = α · narrow`, and a
nonempty invariant subset of a *single orbit* is the whole orbit. So force is available **only** where the cell is
genuinely not an orbit and the key can structurally see the distinction — which is exactly where **consume** cannot
fire. The two routes have **complementary, non-overlapping firing domains**; graphs where *neither* fires are the
residue.

## A concrete key that provably fires — `lookaheadKey`

Individualize `v`, refine, and rank `v` by **the leaf that step reaches** (falling back to a cell-size histogram
when it does not discretize). It is *not* the rigid solver — it is a real instance proving the combinator works,
and the *shape* the solver's key will have: a structural invariant, ranked.

**Measured, and both halves matter:**

* On a **rigid** 3-regular graph (`F12`, one 1-WL cell of size 12) it collapses the root fan-out **12 → 1** and the
  descent becomes a single path: `descentCost` **22477 → 5186**.
* On the **symmetric** `C₇` it **cannot fire at all** — every cell is an orbit — so it only pays for the key:
  `descentCost` **7568 → 10312**. That is not a defect; it is `forceBy_no_narrowing_on_orbit` *observed*, and it is
  why `consume` exists.

**The histogram alone is NOT enough** (a false start worth recording): on a rigid cubic graph, individualizing
*any* vertex discretizes, so every vertex's cell-size histogram is all-ones and the key separates **nothing**
(measured: it narrowed 12 branches to 12). The leaf matrix is what separates them — and it may be used precisely
because `leafMatrix_transport` proves the emitted matrix is *literally equal* under relabelling.
-/

namespace ChainDescent
namespace Force

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend

variable {n : Nat}

/-! ## 1. Minimum of a list of keys (under the proved total order `lexLeList`) -/

/-- The lex-least key of a list (`none` on the empty list). -/
def kmin? : List (List Nat) → Option (List Nat)
  | [] => none
  | a :: as =>
      match kmin? as with
      | none => some a
      | some b => some (if lexLeList a b then a else b)

/-- `kmin?` flags exactly on the empty list. -/
theorem kmin?_eq_none_iff (l : List (List Nat)) : kmin? l = none ↔ l = [] := by
  cases l with
  | nil => simp [kmin?]
  | cons a as =>
      constructor
      · intro h
        unfold kmin? at h
        cases hk : kmin? as with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some b => rw [hk] at h; exact absurd h (by simp)
      · intro h; exact absurd h (by simp)

/-- The minimum is one of the candidates. -/
theorem kmin?_mem : ∀ (l : List (List Nat)) {m : List Nat}, kmin? l = some m → m ∈ l
  | [], m, h => by simp [kmin?] at h
  | a :: as, m, h => by
      unfold kmin? at h
      cases hk : kmin? as with
      | none =>
          rw [hk] at h
          exact (Option.some.inj h) ▸ List.mem_cons_self
      | some b =>
          rw [hk] at h
          have hm : (if lexLeList a b then a else b) = m := Option.some.inj h
          by_cases hle : lexLeList a b = true
          · rw [if_pos hle] at hm
            exact hm ▸ List.mem_cons_self
          · rw [if_neg hle] at hm
            exact List.mem_cons_of_mem _ (hm ▸ kmin?_mem as hk)

/-- The minimum really is `≤` every candidate. -/
theorem kmin?_le : ∀ (l : List (List Nat)) (m : List Nat), kmin? l = some m →
    ∀ x ∈ l, lexLeList m x = true := by
  intro l
  induction l with
  | nil => intro m h; exact absurd h (by simp [kmin?])
  | cons a as ih =>
      intro m h x hx
      unfold kmin? at h
      cases hk : kmin? as with
      | none =>
          rw [hk] at h
          have hm : a = m := Option.some.inj h
          have hnil : as = [] := (kmin?_eq_none_iff as).mp hk
          subst hnil
          have : x = a := by simpa using hx
          subst this
          exact hm ▸ lexLeList_refl x
      | some b =>
          rw [hk] at h
          have hm : (if lexLeList a b then a else b) = m := Option.some.inj h
          have hble : ∀ y ∈ as, lexLeList b y = true := ih b hk
          rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]
            by_cases hle : lexLeList a b = true
            · rw [if_pos hle] at hm; rw [← hm]; exact lexLeList_refl a
            · rw [if_neg hle] at hm
              rw [← hm]
              rcases lexLeList_total a b with h1 | h1
              · exact absurd h1 hle
              · exact h1
          · by_cases hle : lexLeList a b = true
            · rw [if_pos hle] at hm
              rw [← hm]
              exact lexLeList_trans a b x hle (hble x hx)
            · rw [if_neg hle] at hm
              rw [← hm]
              exact hble x hx

/-- **`kmin?` depends only on the SET of candidates** — a minimum under a total order does. This is what makes the
narrowing survive the fact that the branch list is built in *index* order. -/
theorem kmin?_congr_mem {l l' : List (List Nat)} (h : ∀ x, x ∈ l ↔ x ∈ l') : kmin? l = kmin? l' := by
  cases hl : kmin? l with
  | none =>
      have hlnil : l = [] := (kmin?_eq_none_iff l).mp hl
      have hl'nil : l' = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have := (h x).mpr hx
        rw [hlnil] at this
        exact absurd this (List.not_mem_nil)
      rw [hl'nil]; rfl
  | some m =>
      cases hl' : kmin? l' with
      | none =>
          exfalso
          have hl'nil : l' = [] := (kmin?_eq_none_iff l').mp hl'
          have := (h m).mp (kmin?_mem l hl)
          rw [hl'nil] at this
          exact absurd this (List.not_mem_nil)
      | some m' =>
          have h1 : lexLeList m m' = true := kmin?_le l m hl m' ((h m').mpr (kmin?_mem l' hl'))
          have h2 : lexLeList m' m = true := kmin?_le l' m' hl' m ((h m).mp (kmin?_mem l hl))
          rw [lexLeList_antisymm m m' h1 h2]

/-! ## 2. The `Key` contract and the `forceBy` combinator -/

/-- A **structural vertex key** — any invariant the forcing rule ranks branches by. (`List Nat` so it can be
compared with the already-proved total order `lexLeList`.) -/
abbrev Key (n : Nat) := AdjMatrix n → Colouring n → Fin n → List Nat

/-- **★ THE ONLY ① OBLIGATION OF A FORCE RESOLVER.** The key is a pure function of the *structure*: it commutes
with relabelling, i.e. it never breaks ties by vertex index. -/
def KeyEquivariant (key : Key n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = key adj χ v

/-- Keep exactly the branches attaining the least key. (Factored out so the `match` can be discharged by the two
rewrite lemmas below rather than reduced in every proof.) -/
def keepMin (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) : List (Fin n) :=
  match kmin? (B.map (key adj χ)) with
  | none => B
  | some m => B.filter (fun v => decide (key adj χ v = m))

/-- No branches (a discrete node): nothing to narrow. -/
theorem keepMin_none {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    (h : kmin? (B.map (key adj χ)) = none) : keepMin key adj χ B = B := by
  unfold keepMin; rw [h]

/-- The narrowing is the fibre of the least key. -/
theorem keepMin_some {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    {m : List Nat} (h : kmin? (B.map (key adj χ)) = some m) :
    keepMin key adj χ B = B.filter (fun v => decide (key adj χ v = m)) := by
  unfold keepMin; rw [h]

/-- **★ THE FORCE RESOLVER.** Keep exactly the branches of least key; discard the rest. The discards are genuinely
*different* subproblems — the aggregate **changes** — but it changes *consistently* on `G` and `σ·G`, which is all
iso-invariance ever needed. **No global lex-min, no knowledge of the answer.** -/
def forceBy (key : Key n) : Resolver n := fun adj χ B =>
  (some (keepMin key adj χ B), n * n * n)

theorem narrow_forceBy (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceBy key) adj χ = keepMin key adj χ (branches χ) := rfl

/-! ## 3. Soundness — `NarrowEquivariant`, from `KeyEquivariant` alone -/

/-- Mapping then filtering is filtering-by-the-composite then mapping. -/
theorem filter_map_comm {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).filter p = (l.filter (fun a => p (f a))).map f
  | [] => rfl
  | a :: as => by
      by_cases h : p (f a) = true
      · simp [List.filter_cons, h, filter_map_comm f p as]
      · simp only [Bool.not_eq_true] at h
        simp [List.filter_cons, h, filter_map_comm f p as]

/-- **★★ THE FORCE ROUTE, DISCHARGED.** An equivariant key gives an equivariant narrowing — hence (Stage 2) the
whole resolver contract. This is the *entire* ① content of the rigid solver. -/
theorem narrowEquivariant_forceBy {key : Key n} (hk : KeyEquivariant key) :
    NarrowEquivariant (forceBy key) := by
  intro σ adj χ
  -- The two branch lists are permutation-related, and the key transports pointwise.
  have hbr : (branches (transportColouring σ χ)).Perm ((branches χ).map σ) :=
    branches_transport_perm σ χ
  have hkeys : ∀ v : Fin n,
      key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = key adj χ v := hk σ adj χ
  -- Step 1: the minimum key is the SAME natural-number list on both sides.
  have hmap : ((branches (transportColouring σ χ)).map
        (key (relabelAdj σ adj) (transportColouring σ χ))).Perm
      ((branches χ).map (key adj χ)) := by
    refine (hbr.map _).trans ?_
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left (fun v _ => hkeys v))
  have hmin : kmin? ((branches (transportColouring σ χ)).map
        (key (relabelAdj σ adj) (transportColouring σ χ)))
      = kmin? ((branches χ).map (key adj χ)) :=
    kmin?_congr_mem (fun x => hmap.mem_iff)
  rw [narrow_forceBy, narrow_forceBy]
  -- Step 2: split on whether the cell is empty (discrete) or not.
  cases hk0 : kmin? ((branches χ).map (key adj χ)) with
  | none =>
      rw [keepMin_none (hmin.trans hk0), keepMin_none hk0]
      exact hbr
  | some m =>
      rw [keepMin_some (hmin.trans hk0), keepMin_some hk0]
      -- Filter both sides by "key = m"; the σ-side filter pulls back through the perm.
      refine (hbr.filter _).trans ?_
      rw [filter_map_comm]
      refine List.Perm.of_eq (congrArg (List.map σ) ?_)
      apply List.filter_congr
      intro v _
      simp only [hkeys v]

/-! ## 4. Properness (totality) -/

/-- The forced narrowing stays inside the branch cell and never empties it. -/
theorem narrowProper_forceBy (key : Key n) : NarrowProper (forceBy key) := by
  constructor
  · intro adj χ hd
    have hbne : branches χ ≠ [] := branches_ne_nil hd
    rw [narrow_forceBy]
    cases hk : kmin? ((branches χ).map (key adj χ)) with
    | none => rw [keepMin_none hk]; exact hbne
    | some m =>
        rw [keepMin_some hk]
        -- the minimum is attained, so the filter keeps at least that branch
        obtain ⟨v, hv, hvm⟩ := List.mem_map.mp (kmin?_mem _ hk)
        intro hnil
        have hmem : v ∈ (branches χ).filter (fun v => decide (key adj χ v = m)) :=
          List.mem_filter.mpr ⟨hv, by simp [hvm]⟩
        rw [hnil] at hmem
        exact absurd hmem (List.not_mem_nil)
  · intro adj χ v hv
    rw [narrow_forceBy] at hv
    cases hk : kmin? ((branches χ).map (key adj χ)) with
    | none => rw [keepMin_none hk] at hv; exact hv
    | some m =>
        rw [keepMin_some hk] at hv
        exact (List.mem_filter.mp hv).1

/-! ## 5. ★ THE CAPSTONE -/

/-- **★★★ THE FORCE-DRIVEN CANONIZER — a canonical form that answers, for EVERY equivariant key.**

`①a`, `①b`, `①c` all hold and the descent never flags, **modulo nothing but `KeyEquivariant key`**. Note the form
it computes is *not* the exhaustive branch-min (unlike `consume`, which is value-invisible) — it is a **different,
equally valid** canonical form, defined by the forcing rule. That is precisely what frees the rigid solver from
having to know the answer. -/
theorem force_canonizer {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFree (n := n)) (forceBy key))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFree (n := n)) (forceBy key) adj ≠ none :=
  ⟨Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFree
      (Descend.narrowTransport_of_narrowEquivariant Refine.refineEquivariant_encodeFree
        (narrowEquivariant_forceBy hk)),
   fun adj => Descend.canonForm?_ne_none Refine.refineSplits_encodeFree
      (narrowProper_forceBy key) adj⟩

/-- The runnable version. -/
theorem force_canonizer_fast {key : Key n} (hk : KeyEquivariant key) :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceBy key))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceBy key) adj ≠ none := by
  rw [Refine.encodeFreeFast_eq]
  exact force_canonizer hk

/-- **★★ NO GI ∈ P COLLAPSE — `forceBy` cannot fire on a symmetric cell.** If the branch cell is a single orbit of
the colouring-preserving automorphism group, the forced narrowing is the **whole cell**. Forcing is available only
where the cell is genuinely *not* an orbit — which is exactly where **consume** cannot fire. Complementary,
non-overlapping firing domains. -/
theorem forceBy_no_narrowing_on_orbit {key : Key n} (hk : KeyEquivariant key)
    (adj : AdjMatrix n) (χ : Colouring n)
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ α : Equiv.Perm (Fin n),
        relabelAdj α adj = adj ∧ transportColouring α χ = χ ∧ α u = w)
    (hnil : narrow (forceBy key) adj χ ≠ []) :
    ∀ w ∈ branches χ, w ∈ narrow (forceBy key) adj χ :=
  narrow_eq_branches_of_orbit (narrowEquivariant_forceBy hk) adj χ
    (fun v hv => (narrowProper_forceBy key).2 adj χ v hv) hnil horb

/-! ## 6. A concrete key that FIRES — the one-step look-ahead

Individualize `v`, refine, and take the **histogram** of the resulting colouring (the cell-size profile). It is
equivariant because cell *sizes* transport (`cellOf_card_transport`), and it separates two vertices of a 1-WL cell
exactly when individualizing them yields differently-shaped refinements — which on a rigid graph it typically does.

This is **not** the rigid solver: it is a real instance demonstrating the combinator fires, and it is the *shape*
the solver's key will have (a structural invariant, ranked). The solver replaces it with a strictly stronger key
(the linear/ring solve), and owes exactly the same one obligation. -/

/-- The refinement reached by individualizing `v`, as **materialised data**.

⚠ **It returns `ColData`, NOT `Colouring` — and that is load-bearing** (`Refine.lean` §4). `Colouring n` unfolds to
`Fin n → Nat`, so a definition of type `… → Colouring n` is compiled at *full arity* and re-runs its body on **every
colour lookup**. Defining this as a `Colouring` made the key ~10⁴× slower and the resolver stopped `#eval`-ing
(measured). Returning a non-function-typed value forces the refinement **once**. -/
def lookData (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Refine.ColData n :=
  Refine.warmRefineVec adj (indivOne χ v)

/-- The look-ahead colouring, as a lookup into already-forced data. Proved equal to `warmRefineR` — so the
equivariance proof is unaffected by the reification. -/
theorem lookData_col (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (lookData adj χ v).col = Refine.warmRefineR adj (indivOne χ v) :=
  Refine.warmRefineVec_col_eq adj (indivOne χ v)

/-- **The one-step look-ahead key.**

Individualize `v` and refine. If that **discretizes**, rank `v` by the *leaf matrix it would reach* — a genuine
structural invariant (`leafMatrix_transport`: the emitted matrix is *literally equal* under relabelling, because
it is indexed by colour-**ranks**, not vertices). Otherwise fall back to the cell-size histogram.

**The discrete branch is what makes this key actually FIRE.** The histogram alone does not: on a rigid cubic
graph, individualizing *any* vertex discretizes, so every vertex's histogram is all-ones and the key separates
nothing (measured — it narrowed 12 branches to 12 on `F12`). The leaf matrix separates them.

Both branches are equivariant, and *discreteness itself* transports (`discrete_transport`), so the `if` is taken
on the same side for `v` and `σ v`. -/
def lookaheadKey : Key n := fun adj χ v =>
  let ψ : Colouring n := (lookData adj χ v).col
  if Discrete ψ then 1 :: flatten (leafMatrix adj ψ)
  else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)

/-- The look-ahead colouring transports. -/
theorem lookData_col_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) :
    (lookData (relabelAdj σ adj) (transportColouring σ χ) (σ v)).col
      = transportColouring σ ((lookData adj χ v).col) := by
  rw [lookData_col, lookData_col, indivOne_transport σ χ v]
  exact Refine.refineEquivariant_encodeFree σ adj (indivOne χ v)

/-- **The look-ahead key is equivariant** — so `forceBy lookaheadKey` is a canonical form that answers. The
refinement transports, individualization transports, discreteness transports, and *both* ranking invariants
transport: the leaf matrix is literally equal (`leafMatrix_transport`) and cell sizes are invariant
(`cellOf_card_transport`). -/
theorem keyEquivariant_lookahead : KeyEquivariant (lookaheadKey (n := n)) := by
  intro σ adj χ v
  show (let ψ : Colouring n := (lookData (relabelAdj σ adj) (transportColouring σ χ) (σ v)).col
        if Discrete ψ then 1 :: flatten (leafMatrix (relabelAdj σ adj) ψ)
        else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card))
      = (let ψ : Colouring n := (lookData adj χ v).col
         if Discrete ψ then 1 :: flatten (leafMatrix adj ψ)
         else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card))
  simp only [lookData_col_transport σ adj χ v]
  by_cases hd : Discrete ((lookData adj χ v).col)
  · rw [if_pos ((discrete_transport σ _).mpr hd), if_pos hd,
        leafMatrix_transport σ adj ((lookData adj χ v).col) hd]
  · rw [if_neg (fun hc => hd ((discrete_transport σ _).mp hc)), if_neg hd]
    exact congrArg (0 :: ·) (List.map_congr_left (fun c _ =>
      cellOf_card_transport σ ((lookData adj χ v).col) c.val))

/-- **★ THE LOOK-AHEAD CANONIZER** — a fully concrete, hypothesis-free force-driven canonizer: sound,
iso-invariant, complete, and it always answers. -/
theorem lookahead_canonizer :
    CanonSpec.IsCanonicalFormOpt
        (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceBy lookaheadKey))
    ∧ ∀ adj : AdjMatrix n,
        Descend.canonForm? (Refine.encodeFreeFast (n := n)) (forceBy lookaheadKey) adj ≠ none :=
  force_canonizer_fast keyEquivariant_lookahead

end Force
end ChainDescent
