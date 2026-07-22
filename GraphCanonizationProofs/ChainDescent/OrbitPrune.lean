import ChainDescent.DeepMatchSupply

/-!
# `P3` foundation — the pruning license, and why it costs NOTHING in `①`

## The problem P3 has to dodge

`deepMatchSupply d` fires but does not pay: `n^{O(d)}`, measured as a 125× net loss on `C₇`. The fix
(`chain-descent-handoff-2026-07-14.md` §6.2b) is **orbit pruning** — enumerate one deepening sequence per orbit of
the group found so far. But a pruned enumeration **picks a representative sequence**, and a pick is exactly what
`SupplyTransport.GensEquivariant` forbids: the pruned generator *list* is **not** pointwise `σ`-conjugate to the
unpruned one, because `σ` sends the chosen representative to a *different* representative of the conjugate orbit.

Re-deriving `①c` from scratch for a fixpoint construction would be brutal. So we do not.

## §1 — The reduction: everything downstream reads the supply ONLY through its ORBITS

`narrow`, `descend`, `canonForm?`, `Stall.stalled`, `Consume.CellIsOrbit`, `Residue.Handled` all touch the supply
through exactly one channel: `Consume.rep (verified S adj χ)`, and `rep` is the least element of an **orbit**
(`Consume.mem_orbit_iff_wordReach`). So two supplies that prove the **same orbit relation** induce **literally the
same resolver** — same `narrow`, same `descend`, same answer, same flag.

> **`SameOrbits S₁ S₂` ⟹ the two guarded canonizers are the SAME FUNCTION.**

Hence `①a`/`①b`/`①c` transfer wholesale (`guarded_mixed_canonizer_of_sameOrbits`), and a pruned supply's *only*
obligation is the group-theoretic one: **it proves the same orbits**. Zero `①` exposure. This reduction is
reusable by **any** future supply optimization, not just this one.

## §2 — The pruning license: the candidate changes by a KNOWN group element

The identities that make orbit pruning sound:

> **`deepCandidate v sv (g w) (g·sw) = g · deepCandidate v sv w sw`** (left / `w`-side)
> **`deepCandidate (g v) (g·sv) w sw = deepCandidate v sv w sw · g⁻¹`** (right / `v`-side)

for any `g` already known to be a colouring-preserving automorphism. So dropping a `(w, sw)` whose orbit-mate is
kept loses only `g · c` — and `g` and `c` are both in the generated group, so **the group is unchanged**. Since
`Consume.CellIsOrbit` is stated via **`WordReach`** — *a word in the generators*, not a single generator — the
pruned-away element survives as a product, and `§1` then hands back the whole of `①`.

That is the entire mechanism, and under localisation it collapses the `n^d` enumeration to a **single path per
branch** — a sum, not a product.
-/

namespace ChainDescent
namespace OrbitPrune

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.Descend
open ChainDescent.Consume (Supply verified rep WordReach IsColAut CellIsOrbit matchCol rankSwap)
open ChainDescent.Force (Key KeyEquivariant)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.Stall (StallEquivariant)
open ChainDescent.SupplyTransport (SupplyEquivariant)
open ChainDescent.DeepMatch (deepCol deepCandidate)

variable {n : Nat}

/-! ## 1. `rep` depends only on the ORBIT RELATION -/

/-- The minimum of a seeded list depends only on which elements the list *contains*. -/
theorem minList_congr {l₁ l₂ : List (Fin n)} (b : Fin n) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    Consume.minList b l₁ = Consume.minList b l₂ := by
  have key : ∀ m₁ m₂ : List (Fin n), (∀ x, x ∈ m₁ ↔ x ∈ m₂) →
      Consume.minList b m₁ ≤ Consume.minList b m₂ := by
    intro m₁ m₂ h12
    rcases Consume.minList_mem m₂ b with hb | hm
    · rw [hb]; exact Consume.minList_le_seed m₁ b
    · exact Consume.minList_le m₁ b _ ((h12 _).mpr hm)
  exact le_antisymm (key l₁ l₂ h) (key l₂ l₁ (fun x => (h x).symm))

/-- **★ `rep` IS A FUNCTION OF THE ORBIT RELATION.** Two generator lists that word-reach the same pairs give the
*same* representative — even though `rep` is a least-index pick and neither list determines the other. -/
theorem rep_congr {G₁ G₂ : List (Equiv.Perm (Fin n))}
    (h : ∀ u w : Fin n, WordReach G₁ u w ↔ WordReach G₂ u w) (b : Fin n) :
    rep G₁ b = rep G₂ b :=
  minList_congr b (fun x => by
    rw [Consume.mem_orbit_iff_wordReach, Consume.mem_orbit_iff_wordReach]; exact h b x)

/-! ## 2. `SameOrbits` — and the resolvers coincide -/

/-- **Two supplies prove the SAME ORBITS.** The only thing about a supply that the object can see. -/
def SameOrbits (S₁ S₂ : Supply n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n),
    WordReach (verified S₁ adj χ) u w ↔ WordReach (verified S₂ adj χ) u w

theorem SameOrbits.symm {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂) : SameOrbits S₂ S₁ :=
  fun adj χ u w => (h adj χ u w).symm

/-- The mixed resolver's narrowing is unchanged. -/
theorem narrow_forceThenConsume_congr {key : Key n} {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂)
    (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceThenConsume key S₁) adj χ = narrow (forceThenConsume key S₂) adj χ := by
  rw [Composite.narrow_forceThenConsume, Composite.narrow_forceThenConsume]
  have hrep : rep (verified S₁ adj χ) = rep (verified S₂ adj χ) := funext (rep_congr (h adj χ))
  rw [hrep]

/-- The **guard** sees only the narrowing, so it is unchanged too. -/
theorem narrow_guard_congr {R₁ R₂ : Resolver n}
    (hn : ∀ adj χ, narrow R₁ adj χ = narrow R₂ adj χ) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (Stall.guard R₁) adj χ = narrow (Stall.guard R₂) adj χ := by
  rw [Stall.narrow_guard, Stall.narrow_guard]
  by_cases h1 : Stall.stalled R₁ adj χ
  · have h2 : Stall.stalled R₂ adj χ := by
      unfold Stall.stalled at h1 ⊢; rwa [← hn adj χ]
    rw [if_pos h1, if_pos h2]
  · have h2 : ¬ Stall.stalled R₂ adj χ := by
      unfold Stall.stalled at h1 ⊢; rwa [← hn adj χ]
    rw [if_neg h1, if_neg h2, hn adj χ]

/-- **Resolvers with the same narrowing compute the same VALUE** (the cost may differ — that is the point). -/
theorem descend_val_congr {rf : Refiner n} {R₁ R₂ : Resolver n}
    (hn : ∀ adj χ, narrow R₁ adj χ = narrow R₂ adj χ) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n),
      (descend rf R₁ adj fuel χ).1 = (descend rf R₂ adj fuel χ).1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R₁ adj hd 0, descend_val_leaf rf R₂ adj hd 0]
      · rw [descend_val_zero rf R₁ adj hd, descend_val_zero rf R₂ adj hd]
  | succ fuel ih =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descend_val_leaf rf R₁ adj hd (fuel + 1), descend_val_leaf rf R₂ adj hd (fuel + 1)]
      · rw [descend_val_succ rf R₁ adj hd fuel, descend_val_succ rf R₂ adj hd fuel, hn adj χ]
        exact congrArg aggregate (List.map_congr_left (fun v _ => ih _))

theorem canonForm?_congr {rf : Refiner n} {R₁ R₂ : Resolver n}
    (hn : ∀ adj χ, narrow R₁ adj χ = narrow R₂ adj χ) (adj : AdjMatrix n) :
    canonForm? rf R₁ adj = canonForm? rf R₂ adj :=
  descend_val_congr hn adj n _

/-! ## 2b. `SameOrbitsOnBranches` — the WEAKER hypothesis that already suffices

The narrowing (`Composite.narrow_forceThenConsume`) applies `rep` only to `forcedSet key adj χ ⊆ branches χ`
(`forcedSet_subset`), and `rep G b` for a branch `b` depends only on `b`'s orbit — which stays inside the
branch cell (`orbit_subset_branches`). So the reduction needs the two supplies to agree on orbits **only for
branch sources**, not over all of `Fin n`. This weaker hypothesis is what a greedy-pick supply can discharge
from its branch-cell coverage alone, WITHOUT the `K∖cell` group-recovery crux. -/

/-- `rep` at a single point depends only on that point's orbit relation (`rep_congr` needs `h` only at `b`). -/
theorem rep_congr_at {G₁ G₂ : List (Equiv.Perm (Fin n))} {b : Fin n}
    (h : ∀ w : Fin n, WordReach G₁ b w ↔ WordReach G₂ b w) : rep G₁ b = rep G₂ b :=
  minList_congr b (fun x => by
    rw [Consume.mem_orbit_iff_wordReach, Consume.mem_orbit_iff_wordReach]; exact h x)

/-- **Two supplies prove the same orbits FOR BRANCH SOURCES.** All the object can see of a supply is the
narrowing, which reps only `forcedSet ⊆ branches`; so this is exactly as strong as `SameOrbits` for the
reduction, while being far cheaper to prove (branch-cell coverage, no `K∖cell`). -/
def SameOrbitsOnBranches (S₁ S₂ : Supply n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n), ∀ u ∈ branches χ, ∀ w : Fin n,
    WordReach (verified S₁ adj χ) u w ↔ WordReach (verified S₂ adj χ) u w

/-- The mixed resolver's narrowing is unchanged under `SameOrbitsOnBranches` — the reps it uses live on
`forcedSet ⊆ branches`, where the two supplies agree. -/
theorem narrow_forceThenConsume_congr_branch {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbitsOnBranches S₁ S₂) (adj : AdjMatrix n) (χ : Colouring n) :
    narrow (forceThenConsume key S₁) adj χ = narrow (forceThenConsume key S₂) adj χ := by
  rw [Composite.narrow_forceThenConsume, Composite.narrow_forceThenConsume]
  have hmap : (Composite.forcedSet key adj χ).map (rep (verified S₁ adj χ))
      = (Composite.forcedSet key adj χ).map (rep (verified S₂ adj χ)) :=
    List.map_congr_left (fun b hb =>
      rep_congr_at (h adj χ b (Composite.forcedSet_subset key adj χ hb)))
  rw [hmap]

/-- The guarded mixed canonizers of two `SameOrbitsOnBranches` supplies are the **same function**. -/
theorem canonForm?_eq_of_sameOrbitsOnBranches {rf : Refiner n} {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbitsOnBranches S₁ S₂) :
    canonForm? rf (Stall.guard (forceThenConsume key S₁))
      = canonForm? rf (Stall.guard (forceThenConsume key S₂)) :=
  funext (canonForm?_congr
    (fun adj χ => narrow_guard_congr (narrow_forceThenConsume_congr_branch h) adj χ))

/-- **★★★ `①` TRANSFERS from branch-only orbit agreement.** The weaker-hypothesis analogue of
`guarded_mixed_canonizer_of_sameOrbits`: a supply that proves the same orbits **on branch sources** as an
already-certified equivariant one inherits `①a`/`①b`/`①c`. This is the version a greedy-pick supply uses —
its `K∖cell` action is invisible to the object, so it need not be recovered. -/
theorem guarded_mixed_canonizer_of_sameOrbitsOnBranches {key : Key n} (hk : KeyEquivariant key)
    {S₁ S₂ : Supply n} (h1 : SupplyEquivariant S₁) (h : SameOrbitsOnBranches S₁ S₂) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key S₂))) := by
  have hcert := SupplyTransport.guarded_mixed_canonizer hk h1
  rwa [canonForm?_eq_of_sameOrbitsOnBranches (rf := Refine.encodeFreeFast (n := n)) (key := key) h]
    at hcert

/-! ## 3. ★★★ THE REDUCTION — `①` transfers across `SameOrbits`, for free -/

/-- The guarded mixed canonizers of two `SameOrbits` supplies are the **same function**. -/
theorem canonForm?_eq_of_sameOrbits {rf : Refiner n} {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbits S₁ S₂) :
    canonForm? rf (Stall.guard (forceThenConsume key S₁))
      = canonForm? rf (Stall.guard (forceThenConsume key S₂)) :=
  funext (canonForm?_congr
    (fun adj χ => narrow_guard_congr (narrow_forceThenConsume_congr h) adj χ))

/-- **★★★ `①` TRANSFERS.** A supply that proves the same orbits as an *already-certified* one inherits `①a`, `①b`
and `①c` — with **no** equivariance obligation of its own. This is the license every pruned / optimized supply
runs on: it may make any choice it likes internally, provided the **group it generates** is unchanged. -/
theorem guarded_mixed_canonizer_of_sameOrbits {key : Key n} (hk : KeyEquivariant key)
    {S₁ S₂ : Supply n} (h1 : SupplyEquivariant S₁) (h : SameOrbits S₁ S₂) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume key S₂))) := by
  have hcert := SupplyTransport.guarded_mixed_canonizer hk h1
  rwa [canonForm?_eq_of_sameOrbits (rf := Refine.encodeFreeFast (n := n)) (key := key) h] at hcert

/-- The **flag** transfers too (it is read off the same narrowing). -/
theorem stallEquivariant_congr {R₁ R₂ : Resolver n}
    (hn : ∀ adj χ, narrow R₁ adj χ = narrow R₂ adj χ) (h : StallEquivariant R₁) :
    StallEquivariant R₂ := by
  intro σ adj χ
  rw [← hn, ← hn]
  exact h σ adj χ

/-- **FIRING transfers.** -/
theorem cellIsOrbit_congr {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂) {adj : AdjMatrix n}
    {χ : Colouring n} (h1 : CellIsOrbit S₁ adj χ) : CellIsOrbit S₂ adj χ :=
  fun u hu w hw => (h adj χ u w).mp (h1 u hu w hw)

/-- …and hence `②`'s per-cell resolution predicate, and `③`'s `Handled`. **The residue is unchanged.** -/
theorem cellResolved_congr {key : Key n} {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂)
    {adj : AdjMatrix n} {χ : Colouring n} (h1 : Cost.CellResolved key S₁ adj χ) :
    Cost.CellResolved key S₂ adj χ :=
  h1.imp (cellIsOrbit_congr h) id

theorem handled_congr {key : Key n} {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂)
    {adj : AdjMatrix n} (h1 : Residue.Handled key S₁ adj) : Residue.Handled key S₂ adj :=
  fun χ hr hd => cellResolved_congr h (h1 χ hr hd)

/-! ## 4. ★★ THE PRUNING LICENSE — the candidate changes by a KNOWN group element -/

/-- Left: replacing the `w`-side colouring by its `g`-transport **left-multiplies** the colour-match by `g`. -/
theorem rankSwap_left_mul (g : Equiv.Perm (Fin n)) {ψv ψw : Colouring n}
    (hv : Discrete ψv) (hw : Discrete ψw) (hw' : Discrete (transportColouring g ψw)) :
    rankSwap ψv (transportColouring g ψw) hv hw' = g * rankSwap ψv ψw hv hw := by
  refine Equiv.ext (fun u => ?_)
  show rankInv (transportColouring g ψw) (Colouring.vertexRank ψv u)
      = g (rankSwap ψv ψw hv hw u)
  rw [Consume.rankInv_transport g hw]
  rfl

/-- Right: replacing the `v`-side colouring by its `g`-transport **right-multiplies** by `g⁻¹`. -/
theorem rankSwap_right_mul (g : Equiv.Perm (Fin n)) {ψv ψw : Colouring n}
    (hv : Discrete ψv) (hw : Discrete ψw) (hv' : Discrete (transportColouring g ψv)) :
    rankSwap (transportColouring g ψv) ψw hv' hw = rankSwap ψv ψw hv hw * g⁻¹ := by
  refine Equiv.ext (fun u => ?_)
  have hr : Colouring.vertexRank (transportColouring g ψv) u
      = Colouring.vertexRank ψv (g.symm u) := by
    have h := vertexRank_transport g ψv (g.symm u)
    rwa [Equiv.apply_symm_apply] at h
  show rankInv ψw (Colouring.vertexRank (transportColouring g ψv) u)
      = rankSwap ψv ψw hv hw (g.symm u)
  rw [hr]
  rfl

theorem matchCol_left_mul (g : Equiv.Perm (Fin n)) (ψv ψw : Colouring n) :
    matchCol ψv (transportColouring g ψw) = (matchCol ψv ψw).map (fun t => g * t) := by
  unfold Consume.matchCol
  by_cases hv : Discrete ψv
  · by_cases hw : Discrete ψw
    · have hw' : Discrete (transportColouring g ψw) := (discrete_transport g ψw).mpr hw
      simp [dif_pos hv, dif_pos hw, dif_pos hw', rankSwap_left_mul g hv hw hw']
    · have hw' : ¬ Discrete (transportColouring g ψw) := fun hc =>
        hw ((discrete_transport g ψw).mp hc)
      simp [dif_pos hv, dif_neg hw, dif_neg hw']
  · simp [dif_neg hv]

theorem matchCol_right_mul (g : Equiv.Perm (Fin n)) (ψv ψw : Colouring n) :
    matchCol (transportColouring g ψv) ψw = (matchCol ψv ψw).map (fun t => t * g⁻¹) := by
  unfold Consume.matchCol
  by_cases hv : Discrete ψv
  · have hv' : Discrete (transportColouring g ψv) := (discrete_transport g ψv).mpr hv
    by_cases hw : Discrete ψw
    · simp [dif_pos hv, dif_pos hv', dif_pos hw, rankSwap_right_mul g hv hw hv']
    · simp [dif_pos hv, dif_pos hv', dif_neg hw]
  · have hv' : ¬ Discrete (transportColouring g ψv) := fun hc =>
      hv ((discrete_transport g ψv).mp hc)
    simp [dif_neg hv, dif_neg hv']

/-- Deepening along the `g`-image of a sequence gives the `g`-transported colouring — for `g` a
colouring-preserving automorphism, which is exactly what the supply has already **verified**. -/
theorem deepCol_aut {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) (p : List (Fin n)) :
    deepCol adj χ (p.map g) = transportColouring g (deepCol adj χ p) := by
  have h := DeepMatch.deepCol_transport g adj p χ
  rwa [hg.relabel, hg.transport] at h

/-- **★★★ THE `w`-SIDE PRUNING LICENSE.** Moving the `w`-side deepening within a known automorphism's orbit
changes the candidate only by **left-multiplication by that automorphism**. So a pruned-away candidate is
`g · c` with **both** `g` and `c` already in the generated group — the group is **unchanged**, and
`Consume.CellIsOrbit` (a *word* in the generators) still holds. -/
theorem deepCandidate_left_mul {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) (v : Fin n) (sv : List (Fin n)) (w : Fin n) (sw : List (Fin n)) :
    deepCandidate adj χ v sv (g w) (sw.map g)
      = (deepCandidate adj χ v sv w sw).map (fun t => g * t) := by
  have h : deepCol adj χ (g w :: sw.map g) = transportColouring g (deepCol adj χ (w :: sw)) := by
    simpa using deepCol_aut hg (w :: sw)
  unfold DeepMatch.deepCandidate
  rw [h, matchCol_left_mul]

/-- **★★★ THE `v`-SIDE PRUNING LICENSE** (right-multiplication by `g⁻¹`). Both sides may therefore be pruned. -/
theorem deepCandidate_right_mul {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)}
    (hg : IsColAut adj χ g) (v : Fin n) (sv : List (Fin n)) (w : Fin n) (sw : List (Fin n)) :
    deepCandidate adj χ (g v) (sv.map g) w sw
      = (deepCandidate adj χ v sv w sw).map (fun t => t * g⁻¹) := by
  have h : deepCol adj χ (g v :: sv.map g) = transportColouring g (deepCol adj χ (v :: sv)) := by
    simpa using deepCol_aut hg (v :: sv)
  unfold DeepMatch.deepCandidate
  rw [h, matchCol_right_mul]

end OrbitPrune
end ChainDescent
