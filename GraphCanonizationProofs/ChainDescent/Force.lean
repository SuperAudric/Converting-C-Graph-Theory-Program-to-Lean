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

**Measured, and all three halves matter:**

* On a **rigid** 3-regular graph (`F12`, one 1-WL cell of size 12) it collapses the root fan-out **12 → 1** and the
  descent becomes a single path. It **fires** — `forceBy_singleton_of_separating`, observed.
* On the **symmetric** `C₇` it **cannot fire at all** — every cell is an orbit — so it only pays for the key. That
  is not a defect; it is `forceBy_no_narrowing_on_orbit` *observed*, and it is why `consume` exists.
* ⚠ **But under HONEST cost accounting it does not PAY.** `descentCost` on `F12`: exhaustive **22477**, forced
  **26066** — a *net loss*. The key runs a full warm refinement per branch, so the root alone costs
  `12 · (n³ + n²) = 22464`, which already exceeds the entire exhaustive descent. **Firing is not the same as
  paying**, and until `Key` carried a cost the cost model could not see the difference (a flat `n³` charge per node
  reported a fictitious 22477 → 5186).

  The waste is *structural, not incidental*: the refinement `lookaheadKey` computes for branch `v` is **exactly**
  the refinement the child node recomputes from scratch when the descent takes `v`. A resolver that handed its
  look-ahead forward — instead of discarding it — would pay for it once. That is a `descend`-signature question and
  belongs to `②`; it is recorded here because the honest cost model is what exposed it.

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

/-- A **structural vertex key** — any invariant the forcing rule ranks branches by, **with its own cost**.

⚠ **The `CostM` is load-bearing, not bookkeeping.** With a cost-free key the contract admits an *exponential*
resolver that no theorem objects to: take `key adj χ v := flatten (canonForm? … (indivOne χ v))` — the whole
subtree's canonical form. That is `KeyEquivariant` (it is built from equivariant pieces), it fires maximally, and
`force_canonizer` certifies it a canonizer — while doing exhaustive work at every node. "The resolver fires" is
only a meaningful claim against a key that is *charged for what it computes*, so a `Key` carries its cost and
`forceBy` bills every evaluation (`forceBy_cost`). (`List Nat` so keys compare under the proved total order
`lexLeList`.) -/
abbrev Key (n : Nat) := AdjMatrix n → Colouring n → Fin n → CostM (List Nat)

/-- The key's **value** projection — what the ranking actually compares. -/
def keyV (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : List Nat :=
  (key adj χ v).1

/-- The key's **cost** projection — what `forceBy` is billed for each evaluation. -/
def keyCost (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Nat :=
  (key adj χ v).2

/-- **★ THE ONLY ① OBLIGATION OF A FORCE RESOLVER.** The key's *value* is a pure function of the *structure*: it
commutes with relabelling, i.e. it never breaks ties by vertex index. (The key's **cost** carries no ① obligation
— an expensive key is sound, just slow. Its cost is a ② obligation, which is the point of charging it.) -/
def KeyEquivariant (key : Key n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    keyV key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = keyV key adj χ v

/-- Keep exactly the branches attaining the least key. (Factored out so the `match` can be discharged by the two
rewrite lemmas below rather than reduced in every proof.) -/
def keepMin (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) : List (Fin n) :=
  match kmin? (B.map (keyV key adj χ)) with
  | none => B
  | some m => B.filter (fun v => decide (keyV key adj χ v = m))

/-- No branches (a discrete node): nothing to narrow. -/
theorem keepMin_none {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    (h : kmin? (B.map (keyV key adj χ)) = none) : keepMin key adj χ B = B := by
  unfold keepMin; rw [h]

/-- The narrowing is the fibre of the least key. -/
theorem keepMin_some {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    {m : List Nat} (h : kmin? (B.map (keyV key adj χ)) = some m) :
    keepMin key adj χ B = B.filter (fun v => decide (keyV key adj χ v = m)) := by
  unfold keepMin; rw [h]

/-- **★ THE FORCE RESOLVER.** Keep exactly the branches of least key; discard the rest. The discards are genuinely
*different* subproblems — the aggregate **changes** — but it changes *consistently* on `G` and `σ·G`, which is all
iso-invariance ever needed. **No global lex-min, no knowledge of the answer.**

The cost is the **sum of the key's own costs over the branches it evaluates**, plus `n²` for the scan — so a key
that does exhaustive work is billed for exhaustive work, and `②` is a statement about what the resolver actually
does. -/
def forceBy (key : Key n) : Resolver n := fun adj χ B =>
  (some (keepMin key adj χ B), (B.map (keyCost key adj χ)).sum + n * n)

theorem narrow_forceBy (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceBy key) adj χ = keepMin key adj χ (branches χ) := rfl

/-- **The resolver is billed for every key evaluation it makes.** -/
theorem forceBy_cost (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    (forceBy key adj χ B).2 = (B.map (keyCost key adj χ)).sum + n * n := rfl

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
      keyV key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = keyV key adj χ v := hk σ adj χ
  -- Step 1: the minimum key is the SAME natural-number list on both sides.
  have hmap : ((branches (transportColouring σ χ)).map
        (keyV key (relabelAdj σ adj) (transportColouring σ χ))).Perm
      ((branches χ).map (keyV key adj χ)) := by
    refine (hbr.map _).trans ?_
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left (fun v _ => hkeys v))
  have hmin : kmin? ((branches (transportColouring σ χ)).map
        (keyV key (relabelAdj σ adj) (transportColouring σ χ)))
      = kmin? ((branches χ).map (keyV key adj χ)) :=
    kmin?_congr_mem (fun x => hmap.mem_iff)
  rw [narrow_forceBy, narrow_forceBy]
  -- Step 2: split on whether the cell is empty (discrete) or not.
  cases hk0 : kmin? ((branches χ).map (keyV key adj χ)) with
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

/-- **The forced set is exactly the argmin of the key over the cell.** Everything about force's *firing* is read
off this one characterization. -/
theorem mem_keepMin_iff {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    (v : Fin n) :
    v ∈ keepMin key adj χ B
      ↔ v ∈ B ∧ ∀ w ∈ B, lexLeList (keyV key adj χ v) (keyV key adj χ w) = true := by
  cases hk : kmin? (B.map (keyV key adj χ)) with
  | none =>
      have hnil : B = [] := by
        have h0 := (kmin?_eq_none_iff _).mp hk
        simpa using h0
      subst hnil
      rw [keepMin_none hk]
      simp
  | some m =>
      rw [keepMin_some hk]
      have hle : ∀ x ∈ B.map (keyV key adj χ), lexLeList m x = true := kmin?_le _ m hk
      constructor
      · intro hv
        obtain ⟨hvB, hvm⟩ := List.mem_filter.mp hv
        have hvm' : keyV key adj χ v = m := by simpa using hvm
        refine ⟨hvB, fun w hw => ?_⟩
        rw [hvm']
        exact hle _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
      · rintro ⟨hvB, hmin⟩
        -- `v`'s key is ≤ every key, and `m` is ≤ every key and is attained ⟹ they are equal.
        obtain ⟨w₀, hw₀, hw₀m⟩ := List.mem_map.mp (kmin?_mem _ hk)
        have h1 : lexLeList (keyV key adj χ v) m = true := by rw [← hw₀m]; exact hmin w₀ hw₀
        have h2 : lexLeList m (keyV key adj χ v) = true :=
          hle _ (List.mem_map.mpr ⟨v, hvB, rfl⟩)
        exact List.mem_filter.mpr ⟨hvB, by simp [lexLeList_antisymm _ _ h1 h2]⟩

/-! ## 4. Properness (totality) -/

/-- The forced narrowing stays inside the branch cell and never empties it. -/
theorem narrowProper_forceBy (key : Key n) : NarrowProper (forceBy key) := by
  constructor
  · intro adj χ hd
    have hbne : branches χ ≠ [] := branches_ne_nil hd
    rw [narrow_forceBy]
    cases hk : kmin? ((branches χ).map (keyV key adj χ)) with
    | none => rw [keepMin_none hk]; exact hbne
    | some m =>
        rw [keepMin_some hk]
        -- the minimum is attained, so the filter keeps at least that branch
        obtain ⟨v, hv, hvm⟩ := List.mem_map.mp (kmin?_mem _ hk)
        intro hnil
        have hmem : v ∈ (branches χ).filter (fun v => decide (keyV key adj χ v = m)) :=
          List.mem_filter.mpr ⟨hv, by simp [hvm]⟩
        rw [hnil] at hmem
        exact absurd hmem (List.not_mem_nil)
  · intro adj χ v hv
    rw [narrow_forceBy] at hv
    cases hk : kmin? ((branches χ).map (keyV key adj χ)) with
    | none => rw [keepMin_none hk] at hv; exact hv
    | some m =>
        rw [keepMin_some hk] at hv
        exact (List.mem_filter.mp hv).1

/-! ## 4b. ★ FIRING — what force actually narrows, and its floor and ceiling

`narrowProper` says the narrowing is nonempty and inside the cell. **A resolver that returns the whole cell
satisfies that** — so on its own it certifies nothing: sound, and silently useless. These are the theorems that
pin force's firing *exactly*.

**Ceiling** (`keyV_aut_invariant`): an equivariant key is **constant on colouring-preserving automorphism
orbits**, so the forced set is a **union of orbits** — force can never split one, and never narrows below orbit
granularity. That is `forceBy_no_narrowing_on_orbit` in sharper form, and it is what lets `consume` finish the job
(the composite, `Composite.lean`).

**Floor** (`forceBy_singleton_of_separating`): if the key **separates** the cell, the forced set is a
**singleton** — force removes *all* branching. This is the precise obligation the rigid solver's key inherits, and
it is what P1/P3 (§11.12) are really about. -/

/-- **★ THE CEILING — an equivariant key is CONSTANT ON ORBITS.** If `α` is a colouring-preserving automorphism of
`(adj, χ)`, it cannot change any vertex's key. So the key is blind to *exactly* the distinctions consume handles,
and force's narrowing can never cut inside an orbit. -/
theorem keyV_aut_invariant {key : Key n} (hk : KeyEquivariant key) {adj : AdjMatrix n}
    {χ : Colouring n} {α : Equiv.Perm (Fin n)} (hadj : relabelAdj α adj = adj)
    (hχ : transportColouring α χ = χ) (v : Fin n) :
    keyV key adj χ (α v) = keyV key adj χ v := by
  have h := hk α adj χ v
  rwa [hadj, hχ] at h

/-- **The forced set is a union of orbits** — a corollary of the ceiling, and the lemma the composite needs: an
orbit representative of a kept branch is itself kept, so consuming *inside* the forced set never escapes it. -/
theorem mem_keepMin_of_aut {key : Key n} (hk : KeyEquivariant key) {adj : AdjMatrix n}
    {χ : Colouring n} {α : Equiv.Perm (Fin n)} (hadj : relabelAdj α adj = adj)
    (hχ : transportColouring α χ = χ) {v : Fin n}
    (hv : v ∈ keepMin key adj χ (branches χ)) (hαv : α v ∈ branches χ) :
    α v ∈ keepMin key adj χ (branches χ) := by
  obtain ⟨_, hmin⟩ := mem_keepMin_iff (key := key) (adj := adj) (χ := χ) (B := branches χ) v |>.mp hv
  refine mem_keepMin_iff _ |>.mpr ⟨hαv, fun w hw => ?_⟩
  rw [keyV_aut_invariant hk hadj hχ v]
  exact hmin w hw

/-- **★★ THE FLOOR — a SEPARATING key removes ALL branching.** If the key distinguishes the cell's vertices
pairwise, `forceBy` narrows the cell to a **single** branch: the descent takes one path, not `|cell|`.

This is the theorem that makes the force route *useful* rather than merely sound, and it states exactly what the
rigid solver's key must deliver on the rigid residue. Note the hypothesis is *injectivity on the cell*, i.e. the
key sees every distinction the graph makes there — the same content as §11.12's P1/P3, now on the ②/firing side of
the ledger where it belongs. -/
theorem forceBy_singleton_of_separating {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    (hd : ¬ Discrete χ)
    (hsep : ∀ u ∈ branches χ, ∀ w ∈ branches χ, keyV key adj χ u = keyV key adj χ w → u = w) :
    (narrow (forceBy key) adj χ).length = 1 := by
  rw [narrow_forceBy]
  set L := keepMin key adj χ (branches χ) with hL
  -- nonempty (properness) …
  have hne : L ≠ [] := by
    have := (narrowProper_forceBy key).1 adj χ hd
    rwa [narrow_forceBy] at this
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
  -- … and any two members attain the same (minimal) key, hence are equal.
  have huniq : ∀ w ∈ L, w = v := by
    intro w hw
    obtain ⟨hwB, hwmin⟩ := (mem_keepMin_iff w).mp hw
    obtain ⟨hvB, hvmin⟩ := (mem_keepMin_iff v).mp hv
    exact hsep w hwB v hvB
      (lexLeList_antisymm _ _ (hwmin v hvB) (hvmin w hwB))
  -- nodup + a unique member ⟹ length 1
  have hnodup : L.Nodup := by
    rw [hL]
    cases hk : kmin? ((branches χ).map (keyV key adj χ)) with
    | none => rw [keepMin_none hk]; exact branches_nodup χ
    | some m => rw [keepMin_some hk]; exact (branches_nodup χ).filter _
  have hfin : L.toFinset = {v} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨List.mem_toFinset.mpr hv, fun w hw => huniq w (List.mem_toFinset.mp hw)⟩
  have := List.toFinset_card_of_nodup hnodup
  rw [hfin] at this
  simpa using this.symm

/-- **Force FIRES exactly when the key is non-constant on the cell** — it discards a branch iff two branches get
different keys. (The contrapositive is the ceiling: on an orbit cell the key is constant, so nothing is
discarded.) -/
theorem forceBy_discards_of_key_ne {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} (hu : u ∈ branches χ) (hw : w ∈ branches χ)
    (hne : keyV key adj χ u ≠ keyV key adj χ w) :
    ∃ z ∈ branches χ, z ∉ narrow (forceBy key) adj χ := by
  rw [narrow_forceBy]
  -- whichever of `u`, `w` has the strictly larger key cannot be in the argmin set
  rcases lexLeList_total (keyV key adj χ u) (keyV key adj χ w) with h | h
  · refine ⟨w, hw, fun hc => ?_⟩
    obtain ⟨_, hmin⟩ := (mem_keepMin_iff w).mp hc
    exact hne (lexLeList_antisymm _ _ h (hmin u hu))
  · refine ⟨u, hu, fun hc => ?_⟩
    obtain ⟨_, hmin⟩ := (mem_keepMin_iff u).mp hc
    exact hne (lexLeList_antisymm _ _ (hmin w hw) h)

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
on the same side for `v` and `σ v`.

**Its cost is charged honestly**: one warm refinement (`warmRefineCost n = n³`) plus `n²` to read off the ranking
invariant. `forceBy` bills this once per branch, so a node's force cost is `Θ(|cell| · n³)` — polynomial, and
*visibly* so. (Compare the exhaustive key warned about at `Key`: it would be billed its exhaustive cost, and `②`
would reject it. That is the whole reason `Key` carries a cost.) -/
def lookaheadKey : Key n := fun adj χ v =>
  let ψ : Colouring n := (lookData adj χ v).col
  ((if Discrete ψ then 1 :: flatten (leafMatrix adj ψ)
    else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)),
   CostModel.WarmRefine.warmRefineCost n + n * n)

@[simp] theorem keyV_lookaheadKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (lookaheadKey (n := n)) adj χ v =
      (let ψ : Colouring n := (lookData adj χ v).col
       if Discrete ψ then 1 :: flatten (leafMatrix adj ψ)
       else 0 :: (List.finRange n).map (fun c => (cellOf ψ c.val).card)) := rfl

/-- The look-ahead key costs one refinement per branch — **polynomial, and charged**. -/
theorem keyCost_lookaheadKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (lookaheadKey (n := n)) adj χ v = CostModel.WarmRefine.warmRefineCost n + n * n := rfl

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
