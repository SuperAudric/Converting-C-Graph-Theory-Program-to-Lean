import ChainDescent.DeepMatchSupply

/-!
# `F1` — `partialMatchSupply d` : the SUPPORT-LOCAL bounded-depth oracle

## The problem (the F_k fold-cover gap, 2026-07-16 audit)

Every built supply constructs its candidate with `matchCol`, which dif-gates on `Discrete` for **both**
colourings — the candidate exists only when the deepened colouring is **globally** discrete. On a `k`-fold cover
of a rigid core (the "F_k tower" family) the copies are 1-WL-twins, so discretizing means pinning `k − 1` copies:
`SeparatesAt` forces `d ≥ k − 2` and the supply costs `n^{Ω(k)}`. The whole fold family — including the parts the
C# testbed handles in polynomial time (`CopySwapAut`, fully-symmetric covers of any multiplicity) — fell out of
the Lean poly regime. Plan + staging: `docs/chain-descent-fold-tower-plan.md` (this file is its F1).

## The fix: match the SUPPORT, not the graph

Verification (`Consume.IsColAut`) never needed discreteness — only the *constructor* did. The automorphisms worth
catching on a fold are **fiber-wise copy transpositions**: identity outside two copies. Pinning ONE vertex
discretizes one copy (refinement-visible core), and then every moved vertex is a singleton **on one side**:

* **forward** — a `ψ₁`-singleton maps to the unique `ψ₂`-vertex of its colour;
* **backward** — a `ψ₂`-singleton maps to the unique `ψ₁`-vertex of its colour (correct for **involutions**);
* **identity** elsewhere (correct off the support);

then a two-sided inverse check assembles the `Equiv.Perm`, and `Consume.verified` re-checks it as always — the
supply stays untrusted, so `①` carries nothing new.

**Reconstruction** (`partialMatch_transport_of_catches`): the constructor returns **exactly `α`** whenever
`CatchesAt ψ α` — either every moved vertex is a `ψ`-singleton (subsumes the fully-discrete case, hence every
`deepMatchSupply` firing — `supportSeparatesAt_of_separatesAt`), or `α` is an **involution** whose every moved
vertex is a singleton on one side. A copy transposition of a `k`-fold cover is caught at the depth that
discretizes ONE copy — **`d` is independent of `k`** (measured at `d = 0` on a 4-fold cover, `Regression` §8,
where `deepMatchSupply 0` certifies nothing and `deepMatchSupply` needs `d ≥ k − 2 = 2`).

## What it does NOT reach, stated honestly

The support must be **refinement-visible** (a pin discretizes a copy). A WL-blind core (multipede fold) never
produces singletons, so no matching supply can fire there at any depth — that case is the plan's F2 (structural
fold supply, the C# B4 port) + F3 (ring key). Non-involutive deck symmetry (e.g. odd cyclic) with an invisible
gradient is likewise out of F1's scope, by the same boundary.

Cost is the `deepMatchSupply` table verbatim: `|table| = |cell| · n^{≤d}` deepenings + `|table|²` support-local
matches at `O(n²)` each, billed in `supplyCost` — poly for fixed `d`, and the fold family now needs only fixed
small `d`.
-/

namespace ChainDescent
namespace PartialMatch

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach CellIsOrbit)
open ChainDescent.DeepMatch (deepCol deepData deepData_col deepCol_transport allSeqs mem_allSeqs
  mem_allSeqs_map exists_preimage_seq deepTable mem_deepTable_iff deepTable_col SeparatesAt)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)
open ChainDescent.Composite (forceThenConsume)

variable {n : Nat}

/-! ## 1. Support-local vocabulary -/

/-- `u`'s colour class in `ψ` is a singleton. The pointwise form of `Discrete` (which is `∀ u, SingletonAt ψ u`)
— the constructor reads colours only where they already pin a vertex. -/
def SingletonAt (ψ : Colouring n) (u : Fin n) : Prop :=
  ∀ x : Fin n, ψ x = ψ u → x = u

instance (ψ : Colouring n) (u : Fin n) : Decidable (SingletonAt ψ u) :=
  inferInstanceAs (Decidable (∀ x : Fin n, ψ x = ψ u → x = u))

theorem singletonAt_of_discrete {ψ : Colouring n} (h : Discrete ψ) (u : Fin n) :
    SingletonAt ψ u :=
  fun x hx => h x u hx

/-- Singleton-ness transports: a class of the transported colouring is a singleton iff its `σ`-preimage is. -/
theorem singletonAt_transport (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) (u : Fin n) :
    SingletonAt (transportColouring σ ψ) u ↔ SingletonAt ψ (σ.symm u) := by
  constructor
  · intro h x hx
    have hσ : σ x = u := h (σ x) (by simpa [transportColouring] using hx)
    simp [← hσ]
  · intro h y hy
    have := h (σ.symm y) (by simpa [transportColouring] using hy)
    simpa using congrArg σ this

/-! ## 2. The unique colour lookup -/

instance (ψ : Colouring n) (c : Nat) : Decidable (∃! x : Fin n, ψ x = c) :=
  inferInstanceAs (Decidable (∃ x : Fin n, ψ x = c ∧ ∀ y : Fin n, ψ y = c → y = x))

private theorem existsUnique_univ {p : Fin n → Prop} (h : ∃! x, p x) :
    ∃! x, x ∈ (Finset.univ : Finset (Fin n)) ∧ p x := by
  obtain ⟨x, hx, hu⟩ := h
  exact ⟨x, ⟨Finset.mem_univ x, hx⟩, fun y hy => hu y hy.2⟩

/-- The unique vertex of colour `c`, if there is exactly one — the only lookup the constructor performs. It is a
*canonical* value (no representative is chosen), which is what keeps the supply equivariance-free of choices. -/
def uniqueAt (ψ : Colouring n) (c : Nat) : Option (Fin n) :=
  if h : ∃! x : Fin n, ψ x = c then
    some (Finset.choose (fun x => ψ x = c) Finset.univ (existsUnique_univ h))
  else none

theorem uniqueAt_self {ψ : Colouring n} {u : Fin n} (h : SingletonAt ψ u) :
    uniqueAt ψ (ψ u) = some u := by
  have hex : ∃! x : Fin n, ψ x = ψ u := ⟨u, rfl, fun y hy => h y hy⟩
  rw [uniqueAt, dif_pos hex]
  exact congrArg some
    (h _ (Finset.choose_spec (fun x => ψ x = ψ u) Finset.univ (existsUnique_univ hex)).2)

private theorem existsUnique_transport (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) (c : Nat) :
    (∃! y : Fin n, transportColouring σ ψ y = c) ↔ (∃! x : Fin n, ψ x = c) := by
  constructor
  · rintro ⟨y, hy, hu⟩
    refine ⟨σ.symm y, hy, fun x hx => ?_⟩
    have := hu (σ x) (by simpa [transportColouring] using hx)
    simp [← this]
  · rintro ⟨x, hx, hu⟩
    refine ⟨σ x, by simpa [transportColouring] using hx, fun y hy => ?_⟩
    have := hu (σ.symm y) (by simpa [transportColouring] using hy)
    simpa using congrArg σ this

/-- The lookup transports: `uniqueAt` on the transported colouring is the `σ`-image of the lookup. The engine of
both the reconstruction theorem and `GensEquivariant`. -/
theorem uniqueAt_transport (σ : Equiv.Perm (Fin n)) (ψ : Colouring n) (c : Nat) :
    uniqueAt (transportColouring σ ψ) c = (uniqueAt ψ c).map σ := by
  by_cases h : ∃! x : Fin n, ψ x = c
  · have h' : ∃! y : Fin n, transportColouring σ ψ y = c :=
      (existsUnique_transport σ ψ c).mpr h
    rw [uniqueAt, uniqueAt, dif_pos h, dif_pos h', Option.map_some]
    refine congrArg some (h'.unique ?_ ?_)
    · exact (Finset.choose_spec (fun y => transportColouring σ ψ y = c) Finset.univ
        (existsUnique_univ h')).2
    · show transportColouring σ ψ (σ _) = c
      simpa [transportColouring] using
        (Finset.choose_spec (fun x => ψ x = c) Finset.univ (existsUnique_univ h)).2
  · have h' : ¬ ∃! y : Fin n, transportColouring σ ψ y = c :=
      fun hc => h ((existsUnique_transport σ ψ c).mp hc)
    rw [uniqueAt, uniqueAt, dif_neg h, dif_neg h']
    rfl

/-! ## 3. The support-local constructor -/

/-- The raw support-local map: forward-match on `ψ₁`-singletons, backward-match on `ψ₂`-singletons, identity
elsewhere. Total by construction; the permutation check happens in `partialMatch`. -/
def pmFun (ψ₁ ψ₂ : Colouring n) (u : Fin n) : Fin n :=
  if SingletonAt ψ₁ u then (uniqueAt ψ₂ (ψ₁ u)).getD u
  else if SingletonAt ψ₂ u then (uniqueAt ψ₁ (ψ₂ u)).getD u
  else u

/-- **The support-local candidate constructor.** Assemble `pmFun ψ₁ ψ₂` and its mirror into an `Equiv.Perm` iff
they are two-sided inverses (decidable); else decline. Like `matchCol` it is untrusted — `Consume.verified`
re-checks every candidate — but unlike `matchCol` it never demands global discreteness. -/
def partialMatch (ψ₁ ψ₂ : Colouring n) : Option (Equiv.Perm (Fin n)) :=
  if h : (∀ u, pmFun ψ₂ ψ₁ (pmFun ψ₁ ψ₂ u) = u) ∧ (∀ u, pmFun ψ₁ ψ₂ (pmFun ψ₂ ψ₁ u) = u) then
    some ⟨pmFun ψ₁ ψ₂, pmFun ψ₂ ψ₁, h.1, h.2⟩
  else none

/-! ## 4. Reconstruction — what the constructor provably catches -/

/-- **The catch condition.** Either every moved vertex is a `ψ`-singleton (the fully-discretized-support case —
any `α`), or `α` is an **involution** and every moved vertex is a singleton on **one side** (`x` or `α x`). The
second disjunct is the fold case: a copy transposition with only one copy discretized. -/
def CatchesAt (ψ : Colouring n) (α : Equiv.Perm (Fin n)) : Prop :=
  (∀ x, α x ≠ x → SingletonAt ψ x) ∨
    (α * α = 1 ∧ ∀ x, α x ≠ x → (SingletonAt ψ x ∨ SingletonAt ψ (α x)))

private theorem invol_apply {α : Equiv.Perm (Fin n)} (h : α * α = 1) (x : Fin n) :
    α (α x) = x := by
  have := congrArg (fun e : Equiv.Perm (Fin n) => e x) h
  simpa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this

/-- Fixed points of `α⁻¹` and `α` coincide. -/
private theorem fixed_inv_iff {α : Equiv.Perm (Fin n)} (x : Fin n) : α⁻¹ x = x ↔ α x = x := by
  rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]

private theorem symm_eq_of_invol {α : Equiv.Perm (Fin n)} (h : α * α = 1) (x : Fin n) :
    α.symm x = α x :=
  α.injective (by rw [Equiv.apply_symm_apply, invol_apply h])

/-- **★ THE RECONSTRUCTION, pointwise.** On a catchable pair the raw map is **exactly `α`**: the forward branch
reads `α` off the singleton colours, the backward branch reads `α⁻¹ = α` (involution), and the identity branch is
`α` off the support. -/
theorem pmFun_transport_eq {ψ : Colouring n} {α : Equiv.Perm (Fin n)} (hc : CatchesAt ψ α) :
    ∀ u, pmFun ψ (transportColouring α ψ) u = α u := by
  intro u
  unfold pmFun
  by_cases h1 : SingletonAt ψ u
  · rw [if_pos h1, uniqueAt_transport, uniqueAt_self h1]
    rfl
  · rw [if_neg h1]
    by_cases h2 : SingletonAt (transportColouring α ψ) u
    · rw [if_pos h2]
      have h2' : SingletonAt ψ (α.symm u) := (singletonAt_transport α ψ u).mp h2
      have hval : transportColouring α ψ u = ψ (α.symm u) := rfl
      rw [hval, uniqueAt_self h2', Option.getD_some]
      rcases hc with hall | ⟨hinv, _⟩
      · have hu : α u = u := by
          by_contra hne
          exact h1 (hall u hne)
        have hsu : α.symm u = u := (congrArg α.symm hu).symm.trans (α.symm_apply_apply u)
        rw [hsu, hu]
      · exact symm_eq_of_invol hinv u
    · rw [if_neg h2]
      by_contra hne
      have hne' : α u ≠ u := fun h => hne h.symm
      rcases hc with hall | ⟨hinv, hsupp⟩
      · exact h1 (hall u hne')
      · rcases hsupp u hne' with hs | hs
        · exact h1 hs
        · refine h2 ((singletonAt_transport α ψ u).mpr ?_)
          rw [symm_eq_of_invol hinv u]
          exact hs

private theorem transport_transport (σ τ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    transportColouring σ (transportColouring τ χ) = transportColouring (σ * τ) χ :=
  rfl

private theorem transport_inv_cancel (α : Equiv.Perm (Fin n)) (χ : Colouring n) :
    transportColouring α⁻¹ (transportColouring α χ) = χ := by
  rw [transport_transport, inv_mul_cancel]
  rfl

/-- The catch condition holds symmetrically for the inverse against the transported colouring — which is what
makes the two-sided inverse check in `partialMatch` pass. -/
theorem catchesAt_symm {ψ : Colouring n} {α : Equiv.Perm (Fin n)} (hc : CatchesAt ψ α) :
    CatchesAt (transportColouring α ψ) α⁻¹ := by
  rcases hc with hall | ⟨hinv, hsupp⟩
  · left
    intro x hx
    have hαx : α x ≠ x := fun h => hx ((fixed_inv_iff x).mpr h)
    have hsx : α (α.symm x) ≠ α.symm x := by
      rw [Equiv.apply_symm_apply]
      exact fun h => hαx ((congrArg α h).trans (α.apply_symm_apply x))
    exact (singletonAt_transport α ψ x).mpr (hall (α.symm x) hsx)
  · have hα : α⁻¹ = α := inv_eq_of_mul_eq_one_right hinv
    rw [hα]
    right
    refine ⟨hinv, fun x hx => ?_⟩
    have hsy : ∀ y, α.symm y = α y := symm_eq_of_invol hinv
    rcases hsupp x hx with hs | hs
    · right
      refine (singletonAt_transport α ψ (α x)).mpr ?_
      rw [hsy (α x), invol_apply hinv]
      exact hs
    · left
      refine (singletonAt_transport α ψ x).mpr ?_
      rw [hsy x]
      exact hs

/-- **★★ THE RECONSTRUCTION.** On a catchable pair the constructor returns **exactly `α`** — the fold analogue of
`matchCol_self_transport`, with global discreteness replaced by a discretized (half-)support. -/
theorem partialMatch_transport_of_catches {ψ : Colouring n} {α : Equiv.Perm (Fin n)}
    (hc : CatchesAt ψ α) :
    partialMatch ψ (transportColouring α ψ) = some α := by
  have hf : ∀ u, pmFun ψ (transportColouring α ψ) u = α u := pmFun_transport_eq hc
  have hg : ∀ u, pmFun (transportColouring α ψ) ψ u = α⁻¹ u := by
    intro u
    have h := pmFun_transport_eq (catchesAt_symm hc) u
    rwa [transport_inv_cancel] at h
  rw [partialMatch, dif_pos ⟨fun u => by rw [hf, hg]; simp,
    fun u => by rw [hg, hf]; simp⟩]
  exact congrArg some (Equiv.ext hf)

/-! ## 5. Equivariance of the constructor — no choice is ever made -/

theorem pmFun_conj (σ : Equiv.Perm (Fin n)) (ψ₁ ψ₂ : Colouring n) (u : Fin n) :
    pmFun (transportColouring σ ψ₁) (transportColouring σ ψ₂) u
      = σ (pmFun ψ₁ ψ₂ (σ.symm u)) := by
  unfold pmFun
  by_cases h1 : SingletonAt ψ₁ (σ.symm u)
  · rw [if_pos ((singletonAt_transport σ ψ₁ u).mpr h1), if_pos h1]
    have hval : transportColouring σ ψ₁ u = ψ₁ (σ.symm u) := rfl
    rw [hval, uniqueAt_transport]
    cases uniqueAt ψ₂ (ψ₁ (σ.symm u)) with
    | none => simp
    | some x => simp
  · rw [if_neg (fun hc => h1 ((singletonAt_transport σ ψ₁ u).mp hc)), if_neg h1]
    by_cases h2 : SingletonAt ψ₂ (σ.symm u)
    · rw [if_pos ((singletonAt_transport σ ψ₂ u).mpr h2), if_pos h2]
      have hval : transportColouring σ ψ₂ u = ψ₂ (σ.symm u) := rfl
      rw [hval, uniqueAt_transport]
      cases uniqueAt ψ₁ (ψ₂ (σ.symm u)) with
      | none => simp
      | some x => simp
    · rw [if_neg (fun hc => h2 ((singletonAt_transport σ ψ₂ u).mp hc)), if_neg h2]
      simp

private theorem pm_check_conj (σ : Equiv.Perm (Fin n)) (ψ₁ ψ₂ : Colouring n) :
    (∀ u, pmFun (transportColouring σ ψ₂) (transportColouring σ ψ₁)
        (pmFun (transportColouring σ ψ₁) (transportColouring σ ψ₂) u) = u)
      ↔ (∀ u, pmFun ψ₂ ψ₁ (pmFun ψ₁ ψ₂ u) = u) := by
  constructor
  · intro h u
    have := h (σ u)
    rw [pmFun_conj, pmFun_conj] at this
    simp only [Equiv.symm_apply_apply] at this
    exact σ.injective this
  · intro h u
    rw [pmFun_conj, pmFun_conj]
    simp only [Equiv.symm_apply_apply]
    rw [h (σ.symm u)]
    exact σ.apply_symm_apply u

/-- The constructor transports (up to conjugation), **including its failure mode** — the exact analogue of
`matchCol_transport`, so the supply's equivariance proof is the `deepMatchSupply` one verbatim. -/
theorem partialMatch_conj (σ : Equiv.Perm (Fin n)) (ψ₁ ψ₂ : Colouring n) :
    partialMatch (transportColouring σ ψ₁) (transportColouring σ ψ₂)
      = (partialMatch ψ₁ ψ₂).map (fun t => σ * t * σ⁻¹) := by
  unfold partialMatch
  by_cases h : (∀ u, pmFun ψ₂ ψ₁ (pmFun ψ₁ ψ₂ u) = u) ∧ (∀ u, pmFun ψ₁ ψ₂ (pmFun ψ₂ ψ₁ u) = u)
  · rw [dif_pos h, dif_pos ⟨(pm_check_conj σ ψ₁ ψ₂).mpr h.1, (pm_check_conj σ ψ₂ ψ₁).mpr h.2⟩,
      Option.map_some]
    refine congrArg some (Equiv.ext fun u => ?_)
    show pmFun (transportColouring σ ψ₁) (transportColouring σ ψ₂) u = σ (pmFun ψ₁ ψ₂ (σ⁻¹ u))
    rw [pmFun_conj]
    rfl
  · rw [dif_neg h, dif_neg
      (fun hc => h ⟨(pm_check_conj σ ψ₁ ψ₂).mp hc.1, (pm_check_conj σ ψ₂ ψ₁).mp hc.2⟩)]
    rfl

/-! ## 6. The supply -/

/-- The deep candidate, support-locally: individualize-and-refine along both sequences, then `partialMatch`. -/
def pCandidate (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) (sv : List (Fin n))
    (w : Fin n) (sw : List (Fin n)) : Option (Equiv.Perm (Fin n)) :=
  partialMatch (deepCol adj χ (v :: sv)) (deepCol adj χ (w :: sw))

/-- **The oracle reconstructs a catchable automorphism exactly, at depth** — the fold analogue of
`deepCandidate_eq_of_isColAut`: `α·s` has the same length as `s`, so the partner is enumerated, and the pair
reconstructs `α` from a (half-)discretized support instead of a discrete graph. -/
theorem pCandidate_eq_of_isColAut {adj : AdjMatrix n} {χ : Colouring n} {α : Equiv.Perm (Fin n)}
    (hα : IsColAut adj χ α) (v : Fin n) (s : List (Fin n))
    (hcatch : CatchesAt (deepCol adj χ (v :: s)) α) :
    pCandidate adj χ v s (α v) (s.map α) = some α := by
  have ht : deepCol adj χ (α v :: s.map α) = transportColouring α (deepCol adj χ (v :: s)) := by
    have h := deepCol_transport α adj (v :: s) χ
    rw [hα.relabel, hα.transport] at h
    simpa using h
  unfold pCandidate
  rw [ht]
  exact partialMatch_transport_of_catches hcatch

/-- The candidate conjugates — the engine of `GensEquivariant`. -/
theorem pCandidate_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) (sv : List (Fin n)) (w : Fin n) (sw : List (Fin n)) :
    pCandidate (relabelAdj σ adj) (transportColouring σ χ) (σ v) (sv.map σ) (σ w) (sw.map σ)
      = (pCandidate adj χ v sv w sw).map (fun t => σ * t * σ⁻¹) := by
  have h1 : deepCol (relabelAdj σ adj) (transportColouring σ χ) (σ v :: sv.map σ)
      = transportColouring σ (deepCol adj χ (v :: sv)) := by
    simpa using deepCol_transport σ adj (v :: sv) χ
  have h2 : deepCol (relabelAdj σ adj) (transportColouring σ χ) (σ w :: sw.map σ)
      = transportColouring σ (deepCol adj χ (w :: sw)) := by
    simpa using deepCol_transport σ adj (w :: sw) χ
  unfold pCandidate
  rw [h1, h2, partialMatch_conj]

/-- **★ THE SUPPORT-LOCAL BOUNDED-DEPTH ORACLE.** The `deepTable` enumeration verbatim, with `matchCol` replaced
by `partialMatch`. Untrusted: `Consume.verified` re-checks each candidate, so `consume_canonizer` holds for it
with no obligation. -/
def partialMatchSupply (d : Nat) : Supply n := fun adj χ =>
  let table := deepTable adj χ d
  (table.flatMap (fun p => table.filterMap (fun q => partialMatch p.2.col q.2.col)),
   table.length * (d + 1) * CostModel.WarmRefine.warmRefineCost n
     + table.length * table.length * (n * n))

theorem mem_gens_partialMatchSupply_iff {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (partialMatchSupply (n := n) d) adj χ ↔
      ∃ v ∈ branches χ, ∃ sv ∈ allSeqs n d, ∃ w ∈ branches χ, ∃ sw ∈ allSeqs n d,
        pCandidate adj χ v sv w sw = some g := by
  constructor
  · intro hg
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨q, hq2, hmc⟩ := List.mem_filterMap.mp hq
    rw [deepTable_col hp, deepTable_col hq2] at hmc
    obtain ⟨v, hv, sv, hsv, rfl⟩ := mem_deepTable_iff.mp hp
    obtain ⟨w, hw, sw, hsw, rfl⟩ := mem_deepTable_iff.mp hq2
    exact ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
  · rintro ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
    refine List.mem_flatMap.mpr ⟨_, mem_deepTable_iff.mpr ⟨v, hv, sv, hsv, rfl⟩, ?_⟩
    refine List.mem_filterMap.mpr ⟨_, mem_deepTable_iff.mpr ⟨w, hw, sw, hsw, rfl⟩, ?_⟩
    show partialMatch (deepData adj (Refine.warmRefineVec adj (indivOne χ v)) sv).col
        (deepData adj (Refine.warmRefineVec adj (indivOne χ w)) sw).col = some g
    rw [deepData_col, deepData_col, Refine.warmRefineVec_col_eq, Refine.warmRefineVec_col_eq]
    exact hmc

/-! ## 7. `①c` — the supply is equivariant -/

/-- **★★ THE SUPPORT-LOCAL ORACLE IS EQUIVARIANT** — same argument as `deepMatchSupply`: the search space is
characterized purely by length, and the constructor conjugates (`partialMatch_conj`). `pmFun`'s branches are all
canonical (`uniqueAt` — *the* unique vertex; the identity), so no representative is ever chosen (standing trap
#7). -/
theorem gensEquivariant_partialMatchSupply (d : Nat) :
    GensEquivariant (partialMatchSupply (n := n) d) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_partialMatchSupply_iff]
  constructor
  · rintro ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
    obtain ⟨v₀, hv₀, rfl⟩ := (hbr v).mp hv
    obtain ⟨w₀, hw₀, rfl⟩ := (hbr w).mp hw
    obtain ⟨sv₀, hsv₀, rfl⟩ := exists_preimage_seq σ d hsv
    obtain ⟨sw₀, hsw₀, rfl⟩ := exists_preimage_seq σ d hsw
    rw [pCandidate_conj] at hmc
    rcases hcase : pCandidate adj χ v₀ sv₀ w₀ sw₀ with _ | t
    · rw [hcase] at hmc; simp at hmc
    · rw [hcase] at hmc
      simp only [Option.map_some, Option.some.injEq] at hmc
      exact ⟨t, ⟨v₀, hv₀, sv₀, hsv₀, w₀, hw₀, sw₀, hsw₀, hcase⟩, hmc.symm⟩
  · rintro ⟨h, ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩, rfl⟩
    refine ⟨σ v, (hbr _).mpr ⟨v, hv, rfl⟩, sv.map σ, (mem_allSeqs_map σ d sv).mpr hsv,
            σ w, (hbr _).mpr ⟨w, hw, rfl⟩, sw.map σ, (mem_allSeqs_map σ d sw).mpr hsw, ?_⟩
    rw [pCandidate_conj, hmc]
    rfl

theorem supplyEquivariant_partialMatchSupply (d : Nat) :
    SupplyEquivariant (partialMatchSupply (n := n) d) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant (gensEquivariant_partialMatchSupply d)

/-! ## 8. ★★★ FIRING — depth independent of the fold multiplicity -/

/-- **The support-local depth witness.** Every branch pair is connected by an automorphism whose support is
(half-)discretized after **some** `≤ d` further individualizations. On a `k`-fold cover this holds at the `d`
that discretizes ONE copy — independent of `k` — where `SeparatesAt` needs `d ≥ k − 2`. -/
def SupportSeparatesAt (adj : AdjMatrix n) (χ : Colouring n) (d : Nat) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ α : Equiv.Perm (Fin n),
    IsColAut adj χ α ∧ α u = w ∧
      ∃ s : List (Fin n), s.length ≤ d ∧ CatchesAt (deepCol adj χ (u :: s)) α

/-- **The strict-generalization half:** every `deepMatchSupply` firing configuration is a `partialMatchSupply`
one — a discrete deep colouring makes every vertex a singleton, so any localising `α` is caught. -/
theorem supportSeparatesAt_of_separatesAt {adj : AdjMatrix n} {χ : Colouring n} {d : Nat}
    (hsep : SeparatesAt adj χ d)
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ,
      ∃ α : Equiv.Perm (Fin n), IsColAut adj χ α ∧ α u = w) :
    SupportSeparatesAt adj χ d := by
  intro u hu w hw
  obtain ⟨α, hα, hαu⟩ := horb u hu w hw
  obtain ⟨s, hs, hdisc⟩ := hsep u hu
  exact ⟨α, hα, hαu, s, hs, Or.inl (fun x _ => singletonAt_of_discrete hdisc x)⟩

/-- **Graded firing, per pair:** one catchable automorphism puts its pair into the verified `WordReach` — each
verified copy transposition merges its two copies, whatever happens elsewhere in the cell. -/
theorem wordReach_partialMatch_of_catches {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {u w : Fin n} {α : Equiv.Perm (Fin n)}
    (hu : u ∈ branches χ) (hw : w ∈ branches χ) (hα : IsColAut adj χ α) (hαu : α u = w)
    {s : List (Fin n)} (hs : s.length ≤ d) (hcatch : CatchesAt (deepCol adj χ (u :: s)) α) :
    WordReach (verified (partialMatchSupply (n := n) d) adj χ) u w := by
  have hmem : α ∈ verified (partialMatchSupply (n := n) d) adj χ := by
    refine List.mem_filter.mpr ⟨?_, by simpa using hα⟩
    refine mem_gens_partialMatchSupply_iff.mpr
      ⟨u, hu, s, (mem_allSeqs d s).mpr hs, α u, by rw [hαu]; exact hw,
       s.map α, (mem_allSeqs d _).mpr (by simpa using hs), ?_⟩
    exact pCandidate_eq_of_isColAut hα u s hcatch
  have hstep := (Consume.WordReach.refl
    (G := verified (partialMatchSupply (n := n) d) adj χ) u).step hmem
  rwa [hαu] at hstep

/-- **★★★ THE ORACLE FIRES.** Under the support-local depth witness the branch cell is certified as one orbit and
`consume` collapses it to a single branch — on a fold cover, at the depth that discretizes one copy. -/
theorem cellIsOrbit_partialMatchSupply {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    (h : SupportSeparatesAt adj χ d) :
    CellIsOrbit (partialMatchSupply (n := n) d) adj χ := by
  intro u hu w hw
  obtain ⟨α, hα, hαu, s, hs, hcatch⟩ := h u hu w hw
  exact wordReach_partialMatch_of_catches hu hw hα hαu hs hcatch

/-! ## 9. ★★★ THE CAPSTONE -/

/-- **★★★ THE SUPPORT-LOCAL MIXED CANONIZER.** Sound, complete, iso-invariant (answer **and** flag), single
guarded path — for **every** depth `d`, with **no carried hypothesis**. Raising `d` (or catching more, at the
same `d`, than `deepMatchSupply` — the whole point) only shrinks `Residue.Handled`'s complement. -/
theorem partialMatchSupply_guarded_canonizer (d : Nat) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n))
          (partialMatchSupply (n := n) d)))) :=
  SupplyTransport.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (supplyEquivariant_partialMatchSupply d)

end PartialMatch
end ChainDescent
