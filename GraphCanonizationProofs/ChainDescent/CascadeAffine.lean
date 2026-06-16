/-
The depth-`k` scheme-separation engine (§13b/§13c) and the Phase-2 affine beachhead
(`affineScheme`, `G0cyc`/`G0pow`, Frobenius, the cyclotomic `s(C)` machinery + the
conditional seal capstones over the affine family). Split out of `Cascade.lean`
(2026-06-10) — these are leaf decls (no core decl depends on them) and carry the heavy
finite-field imports, so isolating them keeps `Cascade.lean` lighter. The general
scheme/seal substrate they build on lives in `Cascade.lean` (imported below).
-/
import ChainDescent.Cascade
import ChainDescent.Scheme
import ChainDescent.Separability
import ChainDescent.CoherentConfig

namespace ChainDescent

open scoped BigOperators

/-! ### §S-stab — warm-refinement stabilization (the multi-round propagation prerequisite)

The PV-Thm-3.1 *bridge* (`connectivity ⟹ {α,β} base ⟹ SeparatesAtBoundedBase`) re-expresses PV's
fiber-singleton propagation (Lemmas 3.2–3.3) on `warmRefine`. That propagation pins a vertex `z'` from a
*determined* (singleton-cell) neighbour, which needs to compare signatures one round past the stable
colouring — i.e. it needs `warmRefine` to be a `refineStep`-fixpoint **up to partition**. Every prior
discreteness result in the project goes through the depth-`k` *count* route (`kRoundProfileCount_eq`)
precisely to avoid this fixpoint fact; the bridge cannot, so we prove it here.

`warmRefine = (refineStep)^[n]`. The chain `χ, refineStep χ, …` refines monotonically, the cell count
(`numCells`) is non-decreasing and bounded by `n`, so a *plateau* (`samePartition` between consecutive
rounds) is reached within `n` steps; once reached it is stable forever (`refineStep` respects
`samePartition`). Hence the `n`-th round is already stable: `samePartition (warmRefine χ) (refineStep …
(warmRefine χ))`. This whole block is generic in `(adj, P)` — no scheme structure. -/
section Stabilization

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}

/-- Number of cells (distinct colours) of a colouring. -/
def numCells (χ : Colouring n) : Nat := (Finset.univ.image χ).card

/-- `refineStep` preserves `samePartition`: the next round depends only on the current partition. -/
theorem refineStep_samePartition {χ₁ χ₂ : Colouring n}
    (h : samePartition χ₁ χ₂) :
    samePartition (refineStep adj P χ₁) (refineStep adj P χ₂) := by
  have hr12 : Refines χ₁ χ₂ := fun a b hab => (h a b).mp hab
  have hr21 : Refines χ₂ χ₁ := fun a b hab => (h a b).mpr hab
  intro i j
  rw [refineStep_iff, refineStep_iff]
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨hr12 _ _ hc, signature_refines hr12 hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hr21 _ _ hc, signature_refines hr21 hs⟩

/-- The coarsening map on colours induced by `Refines χ₁ χ₂`. -/
private noncomputable def coarsen (χ₁ χ₂ : Colouring n) : Nat → Nat :=
  fun c => if h : ∃ v, χ₁ v = c then χ₂ h.choose else 0

private theorem coarsen_apply {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂) (v : Fin n) :
    coarsen χ₁ χ₂ (χ₁ v) = χ₂ v := by
  have hex : ∃ u, χ₁ u = χ₁ v := ⟨v, rfl⟩
  simp only [coarsen, dif_pos hex]
  exact href _ _ hex.choose_spec

/-- Refinement does not increase the number of cells: `Refines χ₁ χ₂ → numCells χ₂ ≤ numCells χ₁`. -/
theorem numCells_le_of_refines {χ₁ χ₂ : Colouring n} (href : Refines χ₁ χ₂) :
    numCells χ₂ ≤ numCells χ₁ := by
  classical
  unfold numCells
  apply Finset.card_le_card_of_surjOn (coarsen χ₁ χ₂)
  intro d hd
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hd ⊢
  obtain ⟨v, rfl⟩ := hd
  exact ⟨χ₁ v, ⟨v, rfl⟩, coarsen_apply href v⟩

/-- If a refinement does not strictly increase the cell count, it is partition-trivial. -/
theorem samePartition_of_refines_of_numCells_le {χ₁ χ₂ : Colouring n}
    (href : Refines χ₁ χ₂) (hcard : numCells χ₁ ≤ numCells χ₂) :
    samePartition χ₁ χ₂ := by
  classical
  have hmaps : ∀ c ∈ Finset.univ.image χ₁, coarsen χ₁ χ₂ c ∈ Finset.univ.image χ₂ := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc ⊢
    obtain ⟨v, rfl⟩ := hc
    exact ⟨v, (coarsen_apply href v).symm⟩
  have hsurj : ∀ d ∈ Finset.univ.image χ₂, ∃ c ∈ Finset.univ.image χ₁, coarsen χ₁ χ₂ c = d := by
    intro d hd
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨v, rfl⟩ := hd
    exact ⟨χ₁ v, ⟨v, rfl⟩, coarsen_apply href v⟩
  have hinj := Finset.injOn_of_surjOn_of_card_le (coarsen χ₁ χ₂)
    (s := Finset.univ.image χ₁) (t := Finset.univ.image χ₂) hmaps hsurj hcard
  intro i j
  constructor
  · exact href i j
  · intro hij
    have hi : χ₁ i ∈ Finset.univ.image χ₁ := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    have hj : χ₁ j ∈ Finset.univ.image χ₁ := Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    apply hinj hi hj
    rw [coarsen_apply href i, coarsen_apply href j, hij]

/-- A non-trivial refinement strictly increases the cell count. -/
theorem numCells_lt_of_not_samePartition {χ₁ χ₂ : Colouring n}
    (href : Refines χ₁ χ₂) (hns : ¬ samePartition χ₁ χ₂) :
    numCells χ₂ < numCells χ₁ := by
  by_contra hle
  push Not at hle
  exact hns (samePartition_of_refines_of_numCells_le href hle)

/-- The cell count is at most `n`. -/
theorem numCells_le (ψ : Colouring n) : numCells ψ ≤ n := by
  unfold numCells
  calc (Finset.univ.image ψ).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-- With at least one vertex, every colouring has at least one cell. -/
theorem numCells_pos (hn : 0 < n) (ψ : Colouring n) : 0 < numCells ψ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold numCells
  exact Finset.card_pos.2 (Finset.univ_nonempty.image ψ)

/-- **Cell-count growth bound.** If the refinement chain strictly refines at every step below `k`, the
cell count grows by at least `k`. -/
theorem numCells_iter_bound (χ : Colouring n) :
    ∀ k, (∀ j < k, ¬ samePartition ((refineStep adj P)^[j] χ) ((refineStep adj P)^[j+1] χ)) →
      numCells χ + k ≤ numCells ((refineStep adj P)^[k] χ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ m ih =>
    intro hns
    have hm : numCells χ + m ≤ numCells ((refineStep adj P)^[m] χ) :=
      ih (fun j hj => hns j (Nat.lt_succ_of_lt hj))
    have hstep : ¬ samePartition ((refineStep adj P)^[m] χ) ((refineStep adj P)^[m+1] χ) :=
      hns m (Nat.lt_succ_self m)
    have href : Refines ((refineStep adj P)^[m+1] χ) ((refineStep adj P)^[m] χ) := by
      rw [Function.iterate_succ_apply']
      exact fun a b h => refineStep_refines adj P _ h
    have hlt : numCells ((refineStep adj P)^[m] χ) < numCells ((refineStep adj P)^[m+1] χ) :=
      numCells_lt_of_not_samePartition href (fun h => hstep h.symm)
    omega

/-- **A plateau occurs within the first `n` steps.** -/
theorem exists_samePartition_step (hn : 0 < n) (χ : Colouring n) :
    ∃ k < n, samePartition ((refineStep adj P)^[k] χ) ((refineStep adj P)^[k+1] χ) := by
  by_contra hcon
  push Not at hcon
  have hb := numCells_iter_bound (adj := adj) (P := P) χ n (fun j hj => hcon j hj)
  have h1 := numCells_pos hn χ
  have h2 := numCells_le ((refineStep adj P)^[n] χ)
  omega

/-- **Once the chain plateaus, it stays put** (a fixpoint up to partition is stable forever). -/
theorem samePartition_step_stable {χ : Colouring n} {k₀ : Nat}
    (h : samePartition ((refineStep adj P)^[k₀] χ) ((refineStep adj P)^[k₀+1] χ)) :
    ∀ m, k₀ ≤ m → samePartition ((refineStep adj P)^[m] χ) ((refineStep adj P)^[m+1] χ) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ p _ ih =>
    have hnext := refineStep_samePartition (adj := adj) (P := P) ih
    have e1 : (refineStep adj P)^[p + 1] χ = refineStep adj P ((refineStep adj P)^[p] χ) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : (refineStep adj P)^[p + 1 + 1] χ = refineStep adj P ((refineStep adj P)^[p + 1] χ) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]; exact hnext

/-- **Warm refinement is a `refineStep`-fixpoint up to partition** — the stabilization lemma the
multi-round propagation bridge needs. `n` iterations reach a stable partition, so one more round of
`refineStep` does not split any cell: `samePartition (warmRefine χ) (refineStep (warmRefine χ))`. -/
theorem warmRefine_refineStep_samePartition (χ : Colouring n) :
    samePartition (warmRefine adj P χ) (refineStep adj P (warmRefine adj P χ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; intro i; exact i.elim0
  · obtain ⟨k₀, hk₀, hsp⟩ := exists_samePartition_step (adj := adj) (P := P) hn χ
    have hstab := samePartition_step_stable hsp n (Nat.le_of_lt hk₀)
    rw [Function.iterate_succ_apply'] at hstab
    unfold warmRefine
    exact hstab

end Stabilization

/-! ### §S-bridge — the PV-Thm-3.1 connectivity→base bridge (B1: relation to a determined point)

The bridge re-expresses PV Lemmas 3.2–3.3 on `warmRefine`: from connectivity of `smax`/`sα`
(`Separability.lean`) deduce that individualising a maximal-valency edge `{α,β}` discretises the
scheme (`SeparatesAtBoundedBase S 2`). Its core primitive (B1) is the *determined-point* analogue of
`relOfPair_eq_of_warmRefine_singleton`: a vertex sitting in a singleton `warmRefine` cell pins the
relation of any same-cell pair to it — the WL fact that lets a determined vertex propagate
determinacy to its forced-triangle neighbours. -/

/-- **B1 — relation to a *determined* point is cell-determined.** If `x` lies in a singleton
`warmRefine` cell (`hx`: its cell is `{x}`) and `w, u` share a `warmRefine` cell, then they have the
same relation to `x`. The determined-point analogue of `relOfPair_eq_of_warmRefine_singleton`, with the
refined colour-singleton `x` in the individualised point's slot — unblocked by the stabilization lemma
(`warmRefine_refineStep_samePartition`), which lets us read the signature one round past `warmRefine`
where `x`'s colour is already unique. -/
theorem relOfPair_eq_of_warmRefine_determined {n : Nat} (S : AssociationScheme n)
    {χ : Colouring n} {x w u : Fin n}
    (hx : ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
            = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ x → z = x)
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ u) :
    S.relOfPair x w = S.relOfPair x u := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χn := warmRefine adj P χ with hχn
  by_cases hxw : x = w
  · have hux : u = x := hx u (by rw [← h, ← hxw])
    rw [← hxw, hux]
  · by_cases hxu : x = u
    · have hwx : w = x := hx w (by rw [h, ← hxu])
      rw [← hxu, hwx]
    · -- main case: x ≠ w, x ≠ u
      have hstab := warmRefine_refineStep_samePartition (adj := adj) (P := P) χ
      have hrs : refineStep adj P χn w = refineStep adj P χn u := (hstab w u).mp h
      have hsig : signature adj P χn w = signature adj P χn u :=
        ((refineStep_iff adj P χn w u).mp hrs).2
      have hcard := signature_eq_card_eq adj P χn hsig (χn x, adj.adj w x, P w x)
      -- the `w`-side filter is exactly `{x}` (only `x` has colour `χn x`)
      have hFw : (Finset.univ.filter (fun z : Fin n =>
          z ≠ w ∧ (χn x, adj.adj w x, P w x) = (χn z, adj.adj w z, P w z))) = {x} := by
        apply Finset.ext; intro z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩
          exact hx z (congrArg Prod.fst heq).symm
        · rintro rfl; exact ⟨hxw, rfl⟩
      rw [hFw, Finset.card_singleton] at hcard
      -- the `u`-side filter then has a witness `z = x` with `adj w x = adj u x`
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (hcard ▸ Nat.one_pos)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨_, hzeq⟩ := hz
      have hzx : z = x := hx z (congrArg Prod.fst hzeq).symm
      have hval : adj.adj w x = adj.adj u x := by
        have hv := congrArg (fun p : Nat × Nat × POE => p.2.1) hzeq
        rw [hzx] at hv; exact hv
      have hrel : S.relOfPair w x = S.relOfPair u x := Fin.val_injective hval
      rw [S.relOfPair_symm x w, S.relOfPair_symm x u]; exact hrel

/-- **B2 — the base case: an individualised point is determined.** Every `t ∈ T` sits in a singleton
`warmRefine` cell after individualising `T` (its unique initial colour is preserved by refinement).
The seed of the propagation: `α, β ∈ {α,β}` are determined. -/
theorem determined_of_mem_individualized {n : Nat} (S : AssociationScheme n)
    {T : Finset (Fin n)} {α : Fin n} (hα : α ∈ T) :
    ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z
          = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) α
        → z = α := by
  intro z hz
  by_contra hzα
  exact iterate_refineStep_preserves_singleton (schemeAdj S) (fun _ _ => POE.unknown) α n
    (individualizedColouring n T) (individualizedColouring_mem_sep hα) z hzα hz

/-- **B3 — the forced-triangle propagation step (PV Lemma 3.2 core).** If the apex `α` and a point `β`
are both determined and `(β,γ)` is an `sα`-edge (the triangle `{α,β,γ}` is colour-rigid,
`c^{r(α,γ)}_{r(α,β),r(β,γ)} = 1`), then `γ` is determined: any same-`warmRefine`-cell vertex `z` shares
`γ`'s relations to `α` and `β` (B1), and the rigid triangle has a unique such vertex. -/
theorem determined_of_saAdj {n : Nat} (S : AssociationScheme n) {χ : Colouring n} {α β γ : Fin n}
    (hα : ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
            = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ α → z = α)
    (hβ : ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
            = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ β → z = β)
    (hsa : S.saAdj α β γ) :
    ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
          = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ γ → z = γ := by
  intro z hz
  have hαz : S.relOfPair α z = S.relOfPair α γ := relOfPair_eq_of_warmRefine_determined S hα hz
  have hβz : S.relOfPair β z = S.relOfPair β γ := relOfPair_eq_of_warmRefine_determined S hβ hz
  obtain ⟨_, _, hone⟩ := S.saAdj_symm α hsa
  set i := S.relOfPair α γ with hi
  set j := S.relOfPair γ β with hj
  have hcard := S.intersectionNumber_well_defined i j (S.relOfPair α β) α β (S.rel_relOfPair α β)
  rw [hone] at hcard
  set Sset := Finset.univ.filter (fun u : Fin n => S.rel i α u = true ∧ S.rel j u β = true) with hSset
  have hle1 : Sset.card ≤ 1 := le_of_eq hcard
  have hγmem : γ ∈ Sset := by
    rw [hSset]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [hi]; exact S.rel_relOfPair α γ, by rw [hj]; exact S.rel_relOfPair γ β⟩
  have hzmem : z ∈ Sset := by
    rw [hSset]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [hi]; have h2 := S.rel_relOfPair α z; rwa [hαz] at h2
    · rw [hj]
      have hzβ : S.relOfPair z β = S.relOfPair γ β := by
        rw [S.relOfPair_symm z β, hβz, ← S.relOfPair_symm γ β]
      have h2 := S.rel_relOfPair z β; rwa [hzβ] at h2
  exact Finset.card_le_one.mp hle1 z hzmem γ hγmem

/-- **B3′ — the forced-triangle propagation step, smax-free (the δ′ engine's primitive).** The content
of `determined_of_saAdj` with the `smax`-membership requirement of `saAdj` stripped away: if `α` and `β`
are both determined and the coloured triangle `{α,β,γ}` is rigid
(`c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` — a `c = 1` two-endpoint dominator pinning `γ`), then `γ` is
determined. The `saAdj` proof never used the two `smaxAdj` conjuncts — it discarded them
(`obtain ⟨_, _, hone⟩`) and consumed only the intersection-number-`= 1` fact — so this is the genuine
general step. It is exactly the `Dominates`/B3 condition the catch-up probe-gate
(`Probe_CatchUpGate_BasesAndDominators`) found discretizes from every minimal base of the rank-4
amorphic-NLS residue *at scheme level* (no extension classes needed). -/
theorem determined_of_forcedTriangle {n : Nat} (S : AssociationScheme n) {χ : Colouring n}
    {α β γ : Fin n}
    (hα : ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
            = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ α → z = α)
    (hβ : ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
            = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ β → z = β)
    (hone : S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) = 1) :
    ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
          = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ γ → z = γ := by
  intro z hz
  have hαz : S.relOfPair α z = S.relOfPair α γ := relOfPair_eq_of_warmRefine_determined S hα hz
  have hβz : S.relOfPair β z = S.relOfPair β γ := relOfPair_eq_of_warmRefine_determined S hβ hz
  set i := S.relOfPair α γ with hi
  set j := S.relOfPair γ β with hj
  have hcard := S.intersectionNumber_well_defined i j (S.relOfPair α β) α β (S.rel_relOfPair α β)
  rw [hone] at hcard
  set Sset := Finset.univ.filter (fun u : Fin n => S.rel i α u = true ∧ S.rel j u β = true) with hSset
  have hle1 : Sset.card ≤ 1 := le_of_eq hcard
  have hγmem : γ ∈ Sset := by
    rw [hSset]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [hi]; exact S.rel_relOfPair α γ, by rw [hj]; exact S.rel_relOfPair γ β⟩
  have hzmem : z ∈ Sset := by
    rw [hSset]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [hi]; have h2 := S.rel_relOfPair α z; rwa [hαz] at h2
    · rw [hj]
      have hzβ : S.relOfPair z β = S.relOfPair γ β := by
        rw [S.relOfPair_symm z β, hβz, ← S.relOfPair_symm γ β]
      have h2 := S.rel_relOfPair z β; rwa [hzβ] at h2
  exact Finset.card_le_one.mp hle1 z hzmem γ hγmem

section Bridge

variable {n : Nat}

/-- A vertex sits in a singleton `warmRefine` cell — PV's `Γ`: a singleton fiber of the point
extension `X_{base}`. The propagation predicate of the bridge. -/
abbrev DeterminedAt (S : AssociationScheme n) (χ : Colouring n) (x : Fin n) : Prop :=
  ∀ z, warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ z
        = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) χ x → z = x

/-- **B4a — determinacy propagates along an `sα`-path** (iterate B3 along `ReflTransGen (saAdj α)`). -/
theorem determinedAt_of_reflTransGen (S : AssociationScheme n) {χ : Colouring n} {α : Fin n}
    (hα : DeterminedAt S χ α) {β γ : Fin n} (hβ : DeterminedAt S χ β)
    (hpath : Relation.ReflTransGen (S.saAdj α) β γ) : DeterminedAt S χ γ := by
  induction hpath with
  | refl => exact hβ
  | tail _ hstep ih => exact determined_of_saAdj S hα ih hstep

/-- **B4b — if some `αsmax`-neighbour is determined, all of `αsmax` is** (PV claim (17), via
`SaConnected`). -/
theorem determinedAt_of_smaxAdj (S : AssociationScheme n) {χ : Colouring n} {α β : Fin n}
    (hα : DeterminedAt S χ α) (hβ : DeterminedAt S χ β) (hsmβ : S.smaxAdj α β)
    (hconn : S.SaConnected α) {γ : Fin n} (hsmγ : S.smaxAdj α γ) : DeterminedAt S χ γ :=
  determinedAt_of_reflTransGen S hα hβ (hconn β γ hsmβ hsmγ)

/-- **B4 — connectivity discretises a maximal-valency base.** If `smax` and every `sα` are connected
and `{α,β}` is a maximal-valency edge, individualising `{α,β}` makes `warmRefine` discrete (PV Lemmas
3.2–3.3 = the `Γ = Ω` propagation): seed `{α,β}` determined (B2), spread across `αsmax` (B4b), then to
all of Ω by the `smax`-component closure (PV's `Γ₀`), using `SmaxConnected`. -/
theorem discrete_of_connectivity (S : AssociationScheme n) {α β : Fin n}
    (hαβ : S.smaxAdj α β) (hsmax : S.SmaxConnected) (hsa : ∀ a, S.SaConnected a) :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown)
      (individualizedColouring n {α, β})) := by
  set χ := individualizedColouring n ({α, β} : Finset (Fin n)) with hχ
  have hα : DeterminedAt S χ α :=
    determined_of_mem_individualized S (Finset.mem_insert_self α {β})
  have hβ : DeterminedAt S χ β :=
    determined_of_mem_individualized S (Finset.mem_insert_of_mem (Finset.mem_singleton_self β))
  -- PV's `Γ₀`: determined, with all `smax`-neighbours determined.
  let Clo : Fin n → Prop := fun v => DeterminedAt S χ v ∧ ∀ w, S.smaxAdj v w → DeterminedAt S χ w
  have hCloα : Clo α := ⟨hα, fun w hw => determinedAt_of_smaxAdj S hα hβ hαβ (hsa α) hw⟩
  have hclo_step : ∀ v w, Clo v → S.smaxAdj v w → Clo w := by
    intro v w hv hvw
    have hw : DeterminedAt S χ w := hv.2 w hvw
    exact ⟨hw, fun w' hw' => determinedAt_of_smaxAdj S hw hv.1 (S.smaxAdj_symm hvw) (hsa w) hw'⟩
  have hclo_rtg : ∀ v, Relation.ReflTransGen S.smaxAdj α v → Clo v := by
    intro v hrtg
    induction hrtg with
    | refl => exact hCloα
    | tail _ hstep ih => exact hclo_step _ _ ih hstep
  have hall : ∀ v, DeterminedAt S χ v := fun v => (hclo_rtg v (hsmax α v)).1
  intro i j hij
  exact hall j i hij

/-- **B5 — the bridge, packaged for the consumer.** `smax`/`sα` connectivity at a maximal-valency edge
`{α,β}` yields `SeparatesAtBoundedBase S 2` — exactly the seal's `PersistentTwinYieldsBlock` /
`reachesRigidOrCameron` consumer. This is PV-Thm-3.1's conclusion `b(X) ≤ 2`, in the project's terms;
the remaining open content is the connectivity hypotheses (the smax half is landed in `Separability.lean`,
the `sα` half is the §3 counting grind / pieces 2–5). -/
theorem separatesAtBoundedBase_of_connectivity (S : SchurianScheme n) {α β : Fin n}
    (hαβ : S.toAssociationScheme.smaxAdj α β)
    (hsmax : S.toAssociationScheme.SmaxConnected)
    (hsa : ∀ a, S.toAssociationScheme.SaConnected a) :
    SeparatesAtBoundedBase S 2 := by
  refine ⟨{α, β}, ?_, discrete_of_connectivity S.toAssociationScheme hαβ hsmax hsa⟩
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- **Ponomarenko–Vasil'ev Theorem 3.1 (the sparse on-ramp), in the project's terms.** A schurian scheme
whose indistinguishing number `c` and maximum valency `k ≥ 2` satisfy the sparsity bound `2c(k−1) < n`
has a 2-element base that discretises it: `SeparatesAtBoundedBase S 2`. This is the **full theorem** — the
bridge (`separatesAtBoundedBase_of_connectivity`) with *both* connectivity legs now discharged from
sparsity (`smaxConnected_of_sparseSeparable` + `saConnected_of_sparseSeparable`, `Separability.lean`). It
feeds the seal's `PersistentTwinYieldsBlock` / `reachesRigidOrCameron` consumer on the sparse end of the
separability spectrum (the dense amorphic residue needs Thm 4.1's full strength — the on-going program). -/
theorem separatesAtBoundedBase_of_sparseSeparable (S : SchurianScheme n)
    (hsep : S.toAssociationScheme.SparseSeparable)
    (hk : 2 ≤ S.toAssociationScheme.maxValency) :
    SeparatesAtBoundedBase S 2 := by
  classical
  have hn1 : 0 < n := by
    have h : 2 * S.toAssociationScheme.indistinguishingNumber
        * (S.toAssociationScheme.maxValency - 1) < n := hsep
    omega
  obtain ⟨u, hu⟩ := S.toAssociationScheme.exists_inSmax
  let α : Fin n := ⟨0, hn1⟩
  have hval : 0 < S.toAssociationScheme.valency u := by rw [hu]; omega
  have hαu : (Finset.univ.filter (fun β => S.toAssociationScheme.rel u α β = true)).Nonempty := by
    rw [← Finset.card_pos, ← S.toAssociationScheme.valency_eq_card u α]; exact hval
  obtain ⟨β, hβ⟩ := hαu
  rw [Finset.mem_filter] at hβ
  have hαβ : S.toAssociationScheme.smaxAdj α β := ⟨u, hu, hβ.2⟩
  exact separatesAtBoundedBase_of_connectivity S hαβ
    (S.toAssociationScheme.smaxConnected_of_sparseSeparable hsep hk)
    (fun a => S.toAssociationScheme.saConnected_of_sparseSeparable hsep hk a)

/-! ### §S-bridge-δ — the forced-triangle dominator-closure engine (Route δ′, citation-free)

The dense-side sibling of the connectivity bridge above. `discrete_of_connectivity` derives that *every*
vertex becomes determined from `smax`/`sα` connectivity — a hypothesis that only holds on the **sparse**
end (PV-Thm-3.1, `2c(k−1) < n`). The dense amorphic residue violates it, but the catch-up probe-gate
(`Probe_CatchUpGate_BasesAndDominators`, 2026-06-12) found the *raw forced-triangle closure* — iterate
the `c = 1` two-endpoint dominator step from the base — discretizes from **every minimal base** of the
ℤ₄²/ℤ₂⁴ rank-4 amorphic-NLS residue, using only the scheme's own classes. This engine packages that:
the closure is an inductive reachability predicate (`DominatorReachable`), each reached vertex is
`DeterminedAt` (B2 seed + B3′ step), and "the closure exhausts Ω" — the single structural hypothesis the
family-level math (Stage 3) discharges — gives `Discrete` ⟹ `SeparatesAtBoundedBase` directly, with **no
CC-extension, no `Separable`, no catch-up, no citation**. It feeds the seal capstone
(`reachesRigidOrCameron_viaDominatorClosure`, §S-gate2) as a citation-free alternative to the
extension-separability checkpoint. -/

/-- **The forced-triangle closure of a base `T`** — the least set of points reachable from `T` by
iterating the `c = 1` two-endpoint dominator step. `base`: every base point is reachable; `step`: a
point `γ` pinned by a rigid coloured triangle (`c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1`) against two
already-reachable points `α, β` is reachable. The smax-free, dense-side generalisation of PV's `sα`-path
reachability (`ReflTransGen (saAdj α)`); `DominatorReachable S T = Ω` is exactly what the probe-gate
verified at every minimal base of the residue. -/
inductive DominatorReachable {n : Nat} (S : AssociationScheme n) (T : Finset (Fin n)) : Fin n → Prop
  | base {t : Fin n} (ht : t ∈ T) : DominatorReachable S T t
  | step {α β γ : Fin n} (hα : DominatorReachable S T α) (hβ : DominatorReachable S T β)
      (hone : S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) = 1) :
      DominatorReachable S T γ

/-- **The general forced-triangle criterion (any scheme).** The dominator intersection number
`c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` exactly when `γ` is the **unique** point `u` sharing `γ`'s
`relOfPair`-profile to both `α` (`r(α,u) = r(α,γ)`) and `β` (`r(u,β) = r(γ,β)`). The forced-triangle
filter `{u : r(α,u)=r(α,γ) ∧ r(u,β)=r(γ,β)}` always contains `γ` (`rel_relOfPair`); `= 1` collapses it to
`{γ}`. The scheme-agnostic core that `affineScheme_interNum_eq_one_of_unique` specialises to orbit
differences — and, via the schurian axiom, reads as `Stab(α)·γ ∩ Stab(β)·γ = {γ}`. -/
theorem interNum_eq_one_of_forcedUnique {n : Nat} (S : AssociationScheme n) {α β γ : Fin n}
    (huniq : ∀ u : Fin n, S.relOfPair α u = S.relOfPair α γ →
      S.relOfPair u β = S.relOfPair γ β → u = γ) :
    S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) = 1 := by
  classical
  have hk := S.intersectionNumber_well_defined (S.relOfPair α γ) (S.relOfPair γ β)
      (S.relOfPair α β) α β (S.rel_relOfPair α β)
  rw [← hk, Finset.card_eq_one]
  refine ⟨γ, Finset.ext (fun u => ?_)⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [S.rel_iff_relOfPair] at h1 h2
    exact huniq u h1.symm h2.symm
  · intro hu; rw [hu]
    exact ⟨S.rel_relOfPair α γ, S.rel_relOfPair γ β⟩

/-- **The general `DominatorReachable` step builder (any scheme).** From two reachable points `α, β` and
the forced-triangle uniqueness on `relOfPair`-profiles pinning `γ`, `γ` is reachable. Subsumes
`dominatorReachable_affine_step` (its orbit-difference `huniq` is this `relOfPair` one unfolded through
`affineScheme_relOfPair_eq_iff`) and covers non-affine residues directly. With `DominatorReachable.base`,
the scheme-agnostic toolkit for building closure derivations. -/
theorem dominatorReachable_step_of_unique {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    {α β γ : Fin n} (hα : DominatorReachable S T α) (hβ : DominatorReachable S T β)
    (huniq : ∀ u : Fin n, S.relOfPair α u = S.relOfPair α γ →
      S.relOfPair u β = S.relOfPair γ β → u = γ) :
    DominatorReachable S T γ :=
  DominatorReachable.step hα hβ (interNum_eq_one_of_forcedUnique S huniq)

/-- **The schurian forced-triangle criterion — the `Stab(α)·γ ∩ Stab(β)·γ = {γ}` reading.** On a schurian
scheme, `relOfPair`-profile equality is a stabiliser-orbit relation (`r(α,u) = r(α,γ) ↔ u ∈ Stab(α)·γ`,
the schurian axiom), so the forced-triangle uniqueness is *geometric*: `γ` is pinned by `α, β` exactly when
the only point fixed-relative to both `α` and `β` like `γ` is `γ` itself. This builds a `DominatorReachable`
step from the **point-stabiliser-orbit** form `huniq` — the conceptual handle for the single-base closure
argument (a base has `⋂ Stab(t) = 1`, so its stabiliser orbits intersect down to points). -/
theorem dominatorReachable_step_of_stab {n : Nat} {S : SchurianScheme n} {T : Finset (Fin n)}
    {α β γ : Fin n}
    (hα : DominatorReachable S.toAssociationScheme T α)
    (hβ : DominatorReachable S.toAssociationScheme T β)
    (huniq : ∀ u : Fin n,
      (∃ g : Equiv.Perm (Fin n), IsSchemeAut S.toAssociationScheme g ∧ g α = α ∧ g γ = u) →
      (∃ g : Equiv.Perm (Fin n), IsSchemeAut S.toAssociationScheme g ∧ g β = β ∧ g γ = u) →
      u = γ) :
    DominatorReachable S.toAssociationScheme T γ := by
  refine dominatorReachable_step_of_unique hα hβ (fun u h1 h2 => huniq u ?_ ?_)
  · obtain ⟨g, hg, hgα, hgγ⟩ := S.schurian (S.relOfPair α γ) α γ α u
      (S.rel_relOfPair α γ) (by rw [S.rel_iff_relOfPair, h1])
    exact ⟨g, hg, hgα, hgγ⟩
  · obtain ⟨g, hg, hgγ, hgβ⟩ := S.schurian (S.relOfPair γ β) γ β u β
      (S.rel_relOfPair γ β) (by rw [S.rel_iff_relOfPair, h2])
    exact ⟨g, hg, hgβ, hgγ⟩

/-- **The single-base closure from a well-founded pinning rank (the iteration engine).** To prove the
forced-triangle closure of a base `T` exhausts `Ω` it suffices to exhibit a rank function
`rank : Ω → ℕ` such that (i) every rank-`0` point lies in `T`, and (ii) every positive-rank `γ` is
forced-triangle-pinned by two points of *strictly smaller* rank (the `relOfPair`-profile uniqueness of
`interNum_eq_one_of_forcedUnique`). Strong induction on the rank then makes every point
`DominatorReachable`. This is the missing iteration brick between the step builders
(`dominatorReachable_step_of_unique` / `_of_stab` / `dominatorReachable_affine_step`) and the closure
consumer (`separatesAtBoundedBase_of_dominatorClosure`): it reduces the family-level open content from
the global "the closure exhausts `Ω`" to the concrete, checkable "exhibit a pinning rank" — the clean
sufficient condition the δ′ Stage-3 endpoint targets (a base has `⋂ Stab(t) = 1`, so the rank is the
number of pinning rounds the stabiliser-orbit intersections take to reach each point). -/
theorem dominatorReachable_of_rank {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    (rank : Fin n → Nat)
    (hbase : ∀ v : Fin n, rank v = 0 → v ∈ T)
    (hstep : ∀ γ : Fin n, 0 < rank γ → ∃ α β : Fin n,
        rank α < rank γ ∧ rank β < rank γ ∧
        ∀ u : Fin n, S.relOfPair α u = S.relOfPair α γ →
          S.relOfPair u β = S.relOfPair γ β → u = γ) :
    ∀ v : Fin n, DominatorReachable S T v := by
  have key : ∀ k : Nat, ∀ v : Fin n, rank v = k → DominatorReachable S T v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (rank v) with hr0 | hrpos
      · exact DominatorReachable.base (hbase v hr0)
      · obtain ⟨α, β, hα, hβ, huniq⟩ := hstep v hrpos
        exact dominatorReachable_step_of_unique
          (ih (rank α) (hv ▸ hα) α rfl) (ih (rank β) (hv ▸ hβ) β rfl) huniq
  intro v
  exact key (rank v) v rfl

/-- **One-round closure (the cleanest checkable sufficient condition).** If every non-base point `γ` is
forced-triangle-pinned (the `relOfPair`-profile uniqueness) by *two base points* `α, β ∈ T`, then the
dominator closure of `T` already exhausts `Ω` in a single round: `∀ v, DominatorReachable S T v`. The
`rank ∈ {0,1}` instance of `dominatorReachable_of_rank` — the simplest discharge of the seal's `hclo`,
applicable whenever the base alone pins everything (the odd-characteristic / non-midpoint regime; char-2
residues genuinely need multi-round and use the full rank engine). -/
theorem dominatorReachable_of_basePinsAll {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    (hpin : ∀ γ : Fin n, γ ∉ T → ∃ α ∈ T, ∃ β ∈ T,
        ∀ u : Fin n, S.relOfPair α u = S.relOfPair α γ →
          S.relOfPair u β = S.relOfPair γ β → u = γ) :
    ∀ v : Fin n, DominatorReachable S T v := by
  refine dominatorReachable_of_rank (fun v => if v ∈ T then 0 else 1) (fun v hv => ?_)
    (fun γ hγ => ?_)
  · by_contra hvT
    have hv' : (if v ∈ T then (0:ℕ) else 1) = 0 := hv
    rw [if_neg hvT] at hv'
    exact one_ne_zero hv'
  · have hγT : γ ∉ T := by
      intro h
      have hγ' : 0 < (if γ ∈ T then (0:ℕ) else 1) := hγ
      rw [if_pos h] at hγ'
      exact lt_irrefl 0 hγ'
    obtain ⟨α, hαT, β, hβT, hu⟩ := hpin γ hγT
    refine ⟨α, β, ?_, ?_, hu⟩
    · show (if α ∈ T then (0:ℕ) else 1) < (if γ ∈ T then (0:ℕ) else 1)
      rw [if_pos hαT, if_neg hγT]; exact one_pos
    · show (if β ∈ T then (0:ℕ) else 1) < (if γ ∈ T then (0:ℕ) else 1)
      rw [if_pos hβT, if_neg hγT]; exact one_pos

/-- **The single-base closure from an `interNum`-keyed pinning rank (the engine `ClebschConcrete` needed
privately, now general).** Identical to `dominatorReachable_of_rank` but the per-level pinning is the
`decide`-friendly intersection-number equation `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` directly, rather than the
`relOfPair`-profile uniqueness (`huniq`) form. This is the public form of `ClebschConcrete`'s local
`domReach_of_rank_pin`: the nested-implication `huniq` form has no synthesizable `Decidable`, but the
Nat-equality `interNum = 1` does, so concrete schemes (`decide`) and the rainbow-rigid family (counting,
via `interNum_eq_one_of_rainbow`) discharge their pinning through this. -/
theorem dominatorReachable_of_rank_interNum {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    (rank : Fin n → Nat)
    (hbase : ∀ v : Fin n, rank v = 0 → v ∈ T)
    (hstep : ∀ γ : Fin n, 0 < rank γ → ∃ α β : Fin n,
        rank α < rank γ ∧ rank β < rank γ ∧
        S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) = 1) :
    ∀ v : Fin n, DominatorReachable S T v := by
  have key : ∀ k : Nat, ∀ v : Fin n, rank v = k → DominatorReachable S T v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (rank v) with hr0 | hrpos
      · exact DominatorReachable.base (hbase v hr0)
      · obtain ⟨α, β, hα, hβ, hone⟩ := hstep v hrpos
        exact DominatorReachable.step
          (ih (rank α) (hv ▸ hα) α rfl) (ih (rank β) (hv ▸ hβ) β rfl) hone
  intro v
  exact key (rank v) v rfl

/-- **Rainbow rigidity** — the structural pinning mechanism the ℤ₄² Clebsch probe extracted
(`Theorem41ConditionsProbe.Probe_ExtractPinningRank`): every *rainbow* triangle (three pairwise-distinct
non-diagonal edge colours) has at most one common neighbour, so it is forced (`c = 1`). This is the
operational form of "the indistinguishing number `c(X)` is small / forced triangles are abundant" (build
doc §1B): for amorphic rank-4 schemes with the Clebsch parameters `(16,5,0,2)` it holds (`decide`-checked
in `ClebschConcrete`), and it is what drives the δ′ closure on the non-affine residue. Carried as a
hypothesis (a structural property of the parameter family, like the cited classifications), never an `axiom`. -/
def RainbowRigid {n : Nat} (S : AssociationScheme n) : Prop :=
  ∀ i j k : Fin (S.rank + 1), i ≠ 0 → j ≠ 0 → k ≠ 0 → i ≠ j → j ≠ k → i ≠ k →
    S.intersectionNumber i j k ≤ 1

/-- **A rainbow triangle is forced.** Under rainbow rigidity, a triangle `(α, γ, β)` whose three edge
colours `r(α,γ), r(γ,β), r(α,β)` are pairwise distinct and non-diagonal pins `γ`: the intersection number
is exactly `1` — `≤ 1` from rigidity, and `≥ 1` because `γ` itself realises the triangle (it lies in the
forced-triangle filter). The bridge from the purely combinatorial "rainbow" colour condition to the δ′
`interNum = 1` pinning premise. -/
theorem interNum_eq_one_of_rainbow {n : Nat} {S : AssociationScheme n} (hrig : RainbowRigid S)
    {α β γ : Fin n}
    (h0i : S.relOfPair α γ ≠ 0) (h0j : S.relOfPair γ β ≠ 0) (h0k : S.relOfPair α β ≠ 0)
    (hij : S.relOfPair α γ ≠ S.relOfPair γ β) (hjk : S.relOfPair γ β ≠ S.relOfPair α β)
    (hik : S.relOfPair α γ ≠ S.relOfPair α β) :
    S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) = 1 := by
  have hle := hrig _ _ _ h0i h0j h0k hij hjk hik
  have hcard := S.intersectionNumber_well_defined (S.relOfPair α γ) (S.relOfPair γ β)
      (S.relOfPair α β) α β (S.rel_relOfPair α β)
  have hge : 0 < S.intersectionNumber (S.relOfPair α γ) (S.relOfPair γ β) (S.relOfPair α β) := by
    rw [← hcard]
    exact Finset.card_pos.mpr
      ⟨γ, Finset.mem_filter.mpr ⟨Finset.mem_univ γ, S.rel_relOfPair α γ, S.rel_relOfPair γ β⟩⟩
  omega

/-- **The rainbow-rigid family closure (δ′).** A rainbow-rigid scheme whose base `T` admits a *rainbow rank*
— `rank : Ω → ℕ` with rank-`0` points in `T` and every positive-rank `γ` reached by a rainbow triangle
(three pairwise-distinct non-diagonal colours) against two strictly-lower-rank points — has its
forced-triangle closure exhaust `Ω`: `∀ v, DominatorReachable S T v`. This **lifts the single-scheme
`clebschZ4_closure` to the whole rainbow-rigid family**: the per-point pinning is now a purely combinatorial
colour condition (no `interNum` computation per point), with the `c = 1` arithmetic supplied once by
`interNum_eq_one_of_rainbow`. The remaining open content for a family is exactly (a) it is `RainbowRigid` and
(b) it has a rainbow rank from a bounded base — the operational `c(X_T)`-boundedness of build doc §1B. -/
theorem dominatorReachable_of_rainbowRank {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    (hrig : RainbowRigid S) (rank : Fin n → Nat)
    (hbase : ∀ v : Fin n, rank v = 0 → v ∈ T)
    (hstep : ∀ γ : Fin n, 0 < rank γ → ∃ α β : Fin n,
        rank α < rank γ ∧ rank β < rank γ ∧
        S.relOfPair α γ ≠ 0 ∧ S.relOfPair γ β ≠ 0 ∧ S.relOfPair α β ≠ 0 ∧
        S.relOfPair α γ ≠ S.relOfPair γ β ∧ S.relOfPair γ β ≠ S.relOfPair α β ∧
        S.relOfPair α γ ≠ S.relOfPair α β) :
    ∀ v : Fin n, DominatorReachable S T v := by
  refine dominatorReachable_of_rank_interNum rank hbase (fun γ hγ => ?_)
  obtain ⟨α, β, hα, hβ, h0i, h0j, h0k, hij, hjk, hik⟩ := hstep γ hγ
  exact ⟨α, β, hα, hβ, interNum_eq_one_of_rainbow hrig h0i h0j h0k hij hjk hik⟩

/-- **Every dominator-reachable point is determined.** Induction over `DominatorReachable`: the base
case is B2 (`determined_of_mem_individualized`), the step is B3′ (`determined_of_forcedTriangle`). The
bridge from the combinatorial reachability predicate to the WL-singleton-cell fact. -/
theorem determinedAt_of_dominatorReachable (S : AssociationScheme n) {T : Finset (Fin n)} {v : Fin n}
    (h : DominatorReachable S T v) :
    DeterminedAt S (individualizedColouring n T) v := by
  induction h with
  | base ht => exact determined_of_mem_individualized S ht
  | step _ _ hone ihα ihβ => exact determined_of_forcedTriangle S ihα ihβ hone

/-- **The δ′ engine — the forced-triangle closure exhausts Ω ⟹ discrete.** If every vertex is
dominator-reachable from `T`, individualising `T` discretises the scheme. The citation-free, dense-side
analogue of `discrete_of_connectivity`: there the universal determinacy came from `smax`/`sα`
connectivity, here it is the named structural hypothesis the family-level math discharges. -/
theorem discrete_of_dominatorClosure (S : AssociationScheme n) {T : Finset (Fin n)}
    (hclo : ∀ v, DominatorReachable S T v) :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown)
      (individualizedColouring n T)) := by
  intro i j hij
  exact determinedAt_of_dominatorReachable S (hclo j) i hij

/-- **δ′ packaged for the seal consumer.** A base `T` of size `≤ bound` whose forced-triangle closure
exhausts Ω discretises the scheme: `SeparatesAtBoundedBase S bound`. The citation-free sibling of
`separatesAtBoundedBase_of_connectivity` and `separatesAtBoundedBase_of_extensionPointed` — it lands
directly on the seal consumer with **no** group-base hypothesis (discreteness is supplied outright, not
via a separability transport), no CC-extension, and no catch-up. -/
theorem separatesAtBoundedBase_of_dominatorClosure (S : SchurianScheme n) {T : Finset (Fin n)}
    {bound : Nat} (hcard : T.card ≤ bound)
    (hclo : ∀ v, DominatorReachable S.toAssociationScheme T v) :
    SeparatesAtBoundedBase S bound :=
  ⟨T, hcard, discrete_of_dominatorClosure S.toAssociationScheme hclo⟩

/-- **The dominator closure is scheme-automorphism-equivariant.** A scheme automorphism `π` mapping the base
`T` into `T'` maps `T`-reachable points to `T'`-reachable points. Induction over `DominatorReachable`: the base
case is `hT`; the step survives because a scheme automorphism preserves `relOfPair`
(`IsSchemeAut.relOfPair_eq`), so the forced-triangle intersection-number premise is `π`-invariant. The
structural fact letting the δ′ family argument reduce "closure exhausts Ω" to one base per
automorphism-orbit. -/
theorem dominatorReachable_map {S : AssociationScheme n} {T T' : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : IsSchemeAut S π) (hT : ∀ t ∈ T, π t ∈ T')
    {v : Fin n} (h : DominatorReachable S T v) : DominatorReachable S T' (π v) := by
  induction h with
  | base ht => exact DominatorReachable.base (hT _ ht)
  | step _ _ hone ihα ihβ =>
      refine DominatorReachable.step ihα ihβ ?_
      rw [hπ.relOfPair_eq, hπ.relOfPair_eq, hπ.relOfPair_eq]; exact hone

/-- **Complete dominator closure transports across automorphic base images.** If base `T`'s closure exhausts
`Ω` and `π` is a scheme automorphism, then the image base `T.image π` also has complete closure. So for a
vertex-transitive residue, proving `∀ v, DominatorReachable S T v` for ONE base discharges it for the entire
`Aut(S)`-orbit of bases — the family-argument leverage `dominatorReachable_map` buys. -/
theorem dominatorReachable_univ_image {S : AssociationScheme n} {T : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : IsSchemeAut S π)
    (h : ∀ v, DominatorReachable S T v) :
    ∀ v, DominatorReachable S (T.image π) v := by
  intro v
  have hmap := dominatorReachable_map hπ (T' := T.image π)
    (fun t ht => Finset.mem_image_of_mem π ht) (h (π.symm v))
  rwa [Equiv.apply_symm_apply] at hmap

/-! ### §S-gate — the seal-bridge anchor: §S.17 `Separable` → the sink (the named transport obligation)

**Scope-and-state step (a) of the Thm 4.1 program — the gate, resolved.** The sink + bridge live in `Cascade.lean`
(`TwinsRealizedByResidualAut` / `separatesAtBoundedBase_of_twinsRealized`): a separability sink + a bounded group
base (`IsBase`) ⟹ the seal consumer `SeparatesAtBoundedBase`. **Verdict:** Thm 4.1's `Separable` is
*necessary-but-not-sufficient* — it feeds the seal only through a 3-part chain. Source-grounded: the cyclotomic
paper (arXiv:2006.13592) is *purely* a separability result — 0 occurrences of "1-regular"/"base number"/"b(X)",
55 of "separab" — so the base bound is the project's OWN work (`affinePermFin_eq_one_of_span` + a spanning base),
never the citation's. The three inputs:
- **(A) `Separable`** (`Separability.lean §S.17`) — Thm 4.1's output (the heavy S-ring / `Ωᵐ` build).
- **(B) the transport** `Separable → TwinsRealizedByResidualAut` (`SeparabilityTransports` below). By
  `twinsRealizedByResidualAut_iff_cellsAreOrbits` (`Cascade.lean`) this **is** `Separable ⟹ CellsAreOrbits at T`
  = the EP fact `s(X)=1 ⟹ b(X) ≤ b(G)` (separable schurian recovers orbits at a group base). **TRUE, but its
  proof is NOT cheap/independent (worked 2026-06-11 — corrects the earlier "B1–B5-bounded" read):** §S.17
  `Separable X` is *relation-level on the homogeneous X*, while `CellsAreOrbits at T` is about the *extension*
  `X_T`'s vertex-cells; the only bridge (individualise `u` vs `u'` ⟹ algebraically-isomorphic extensions ⟹
  separable extension ⟹ induced aut) runs through `s(X_T) ≤ s(X)` (separability inherited by point extensions),
  and `X_T` is a multi-fiber **general CC** the project's homogeneous `AssociationScheme`/`AlgIso` **cannot
  express**. So **(B) couples to the general-CC substrate that (A) builds** — it is not a cheap pre-`Ωᵐ` de-risk.
- **(C) a bounded group base** `IsBase … T, card ≤ bound` (= `b(G) ≤ bound`) — a separate, likely-citable input
  (primitive ⟹ small base; `exists_isBase_saturated` for small schemes). Thm 4.1 does NOT supply it.
See `docs/chain-descent-module-adjoin-plan.md §9` (SEAL-BRIDGE GATE). -/

/-- **The transport obligation (B) — `Separable ⟹ recovery at `T`; the step the gate runs deferred.** From the
§S.17 *algebraic* `Separable`, every same-`warmRefine`-cell twin from `T` is realised by a `T`-fixing residual
automorphism. By `twinsRealizedByResidualAut_iff_cellsAreOrbits` this is exactly `Separable ⟹ CellsAreOrbits at
T` = the EP fact `s(X)=1 ⟹ b(X) ≤ b(G)`. **Worked (2026-06-11):** TRUE, but its proof is *coupled to the
general-CC substrate*, not a cheap independent de-risk — §S.17 `Separable` is relation-level on the homogeneous
`X`, while the twin lives in the multi-fiber extension `X_T`; bridging needs `s(X_T) ≤ s(X)` (separability of a
point extension), inexpressible in the project's homogeneous `AssociationScheme`/`AlgIso`. So (B) and (A) share
the `Ωᵐ`/general-CC build. The affine instance `powAffineSeparates_of_twinsAreSemilinear` sidesteps this only
because there the realiser is the *explicit* linear `affinePermFin` (it never invokes abstract `Separable`). -/
def SeparabilityTransports (S : SchurianScheme n) (T : Finset (Fin n)) : Prop :=
  S.toAssociationScheme.Separable → TwinsRealizedByResidualAut S T

/-- **The seal-bridge, anchored on Thm 4.1's actual output.** (A) `Separable` + (B) the transport
`SeparabilityTransports` + (C) a bounded group base `IsBase` ⟹ the seal consumer `SeparatesAtBoundedBase`.
Composes the transport into the `Cascade.lean` bridge `separatesAtBoundedBase_of_twinsRealized`. Records the full
chain from the literal §S.17 `Separable` to the seal: Thm 4.1 discharges (A); (B) and (C) are the residual gate
content (the transport = the next increment, the group base = likely-citable). -/
theorem separatesAtBoundedBase_of_separable (S : SchurianScheme n)
    {T : Finset (Fin n)} {bound : Nat} (hcard : T.card ≤ bound)
    (hbase : IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T)
    (htrans : SeparabilityTransports S T) (hsep : S.toAssociationScheme.Separable) :
    SeparatesAtBoundedBase S bound :=
  separatesAtBoundedBase_of_twinsRealized S hcard hbase (htrans hsep)

/-- Helper: folding `insert` over a list grows a `Finset` by at most the list length. -/
theorem card_foldl_insert_le (bs : List (Fin n)) (T : Finset (Fin n)) :
    (bs.foldl (fun s b => insert b s) T).card ≤ T.card + bs.length := by
  induction bs generalizing T with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    calc (bs.foldl (fun s b => insert b s) (insert b T)).card
        ≤ (insert b T).card + bs.length := ih (insert b T)
      _ ≤ (T.card + 1) + bs.length := by gcongr; exact Finset.card_insert_le b T
      _ = T.card + (bs.length + 1) := by ring

/-- **The seal-bridge with the group base (C) DISCHARGED — `b(G)` is FREE for small schemes.** The `b(G)`
survey verdict, in Lean: input (C) (a bounded group base) is *not* an obstacle — it is supplied internally by
the landed `exists_greedy_base_le_log` (`Cascade.lean`, `b(G) ≤ log₂|Aut(X)|` via the greedy irredundant base +
`|Aut| = ∏ basic-orbit sizes`). So given only **(A) `Separable`** (Thm 4.1) + **(B) the transport at every base**
(`∀ T, SeparabilityTransports S T`) + the **"small" bound** `log₂|Aut(X)| ≤ bound` (exactly the seal's existing
`¬IsLargeSchemeViaAut` antecedent — small ⟹ `|Aut| ≤ poly` ⟹ `log₂|Aut| = O(log n)`), the scheme discretises at
a bounded base: `SeparatesAtBoundedBase S bound`. **Net: the seal-bridge's residual open content is exactly
{(A) `Separable` + (B) the transport}, both of which the general-CC build supplies together; (C) is closed.** -/
theorem separatesAtBoundedBase_of_separable_of_small (S : SchurianScheme n) {bound : Nat}
    (hbound : Nat.log 2 (Nat.card (StabilizerAt (schemeAdj S.toAssociationScheme)
        (fun _ _ => POE.unknown) ∅)) ≤ bound)
    (htrans : ∀ T : Finset (Fin n), SeparabilityTransports S T)
    (hsep : S.toAssociationScheme.Separable) :
    SeparatesAtBoundedBase S bound := by
  obtain ⟨bs, hbase, hlen⟩ := exists_greedy_base_le_log
    (adj := schemeAdj S.toAssociationScheme) (P := fun _ _ => POE.unknown)
  refine separatesAtBoundedBase_of_separable S ?_ hbase (htrans _) hsep
  calc (bs.foldl (fun s b => insert b s) (∅ : Finset (Fin n))).card
      ≤ (∅ : Finset (Fin n)).card + bs.length := card_foldl_insert_le bs ∅
    _ = bs.length := by simp
    _ ≤ _ := hlen
    _ ≤ bound := hbound

end Bridge

/-! ### §S-gate2 — the pointed transport into the seal (Stage 2 of the general-CC build)

The Stage-2 wiring (`docs/chain-descent-general-cc-separability.md` §5 Stage 2, 2026-06-12): the
§CC.9 transport core (`fiberTwin_realized_of_separablePointed` — pointed separability of a point
extension realizes fiber-twins by `T`-fixing automorphisms, citation-free) composed into the seal's
sink (`separatesAtBoundedBase_of_twinsRealized`). The **single carried model gap** is
`WarmTwinsAreFiberTwins` — the 1-WL↔fiber catch-up the 2026-06-12 direction check isolated — and the
**cited inputs** are `Theorem41Statement` + its probe-confirmed hypotheses on the extension, entering
exactly as the affine slice's citations did (the G3 pattern). This section also resolves the Stage-4
keying note: the chain below consumes the *general-CC* predicates directly, bypassing the
homogeneous-`Separable`-keyed `SeparabilityTransports` gate entirely. -/

section SGate2

open CoherentConfig

variable {n : Nat}

/-- **The Stage-2 catch-up predicate — THE isolated open model gap.** Every same-`warmRefine`-cell
pair from `T` lies in one fiber of the extension `E` ("1-WL twins are pair-WL twins" at `T`). The
2026-06-12 direction check (`Probe_Stage21_DirectionCheck_CellsVsFibers`) proved this **false at
arbitrary `T`** (ℤ₄² bullseye, `T = {0}`: 4 cells vs 10 fibers) and **true at every tested
`|T| ≥ 2`** — so it is carried per-base, never assumed globally. It is the project-model half of the
`dimWL(X) ≤ dimWL(X_α) + 1` individualization exchange (Cai–Fürer–Immerman 1992, Thm 5.2; quoted as
(41) in Ponomarenko arXiv:2006.13592). The converse inclusion (fiber-twins are warm twins, "2-WL
refines 1-WL") is provable and not needed here. -/
def WarmTwinsAreFiberTwins (S : SchurianScheme n) (T : Finset (Fin n))
    (E : CoherentConfig n) : Prop :=
  ∀ u u' : Fin n,
    warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
        (individualizedColouring n T) u
      = warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
        (individualizedColouring n T) u'
    → E.relOf u u = E.relOf u' u'

/-- `relOfPair` preservation is a scheme automorphism — the Bool-level converse of
`IsSchemeAut.relOfPair_eq`. -/
theorem isSchemeAut_of_relOfPair_eq {S : AssociationScheme n} {f : Equiv.Perm (Fin n)}
    (h : ∀ v w, S.relOfPair (f v) (f w) = S.relOfPair v w) : IsSchemeAut S f := by
  intro i v w
  have hiff : (S.rel i (f v) (f w) = true) ↔ (S.rel i v w = true) := by
    rw [S.rel_iff_relOfPair, S.rel_iff_relOfPair, h]
  cases hb : S.rel i v w
  · cases hb' : S.rel i (f v) (f w)
    · rfl
    · exact absurd (hiff.mp hb') (by simp [hb])
  · exact hiff.mpr hb

/-- **STAGE 2, THE TRANSPORT — landed modulo the catch-up.** Pointed separability of a point
extension of the (coerced) scheme at `T`, on every non-singleton fiber (singleton fibers — e.g. the
points of `T` themselves, exactly where the probe saw the Thm-4.1 conditions fail — need no
realizing), plus the catch-up `WarmTwinsAreFiberTwins`, yields the separability sink
`TwinsRealizedByResidualAut S T`: every warm twin is a fiber-twin (catch-up), every fiber-twin is
realized by a `T`-fixing automorphism of the extension (§CC.9, the pointed conclusion at the
identity algebraic isomorphism), and that automorphism descends to a `T`-fixing scheme automorphism
(`Refines` + `isSchemeAut_of_relOfPair_eq`). -/
theorem twinsRealized_of_extensionPointed (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    {T : Finset (Fin n)} {E : CoherentConfig n}
    (hext : IsPointExtension (S.toAssociationScheme.toCoherentConfig hne) T E)
    (hsep : ∀ u : Fin n, ¬ E.SingletonFiber u → E.SeparablePointed u)
    (hcatch : WarmTwinsAreFiberTwins S T E) :
    TwinsRealizedByResidualAut S T := by
  intro u u' hcell
  by_cases hequ : u' = u
  · subst hequ
    exact ⟨1, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, rfl⟩
  · have hfib : E.relOf u' u' = E.relOf u u := (hcatch u u' hcell).symm
    have hns : ¬ E.SingletonFiber u := fun hsing => hequ (hsing u' hfib)
    obtain ⟨f, hfX, hfT, hu⟩ :=
      fiberTwin_realized_of_separablePointed hext (hsep u hns) hfib
    have hrel : ∀ v w, S.toAssociationScheme.relOfPair (f v) (f w)
        = S.toAssociationScheme.relOfPair v w := hfX
    refine ⟨f, ⟨?_, fun _ _ => rfl, hfT⟩, hu⟩
    rw [isAut_schemeAdj_iff]
    exact isSchemeAut_of_relOfPair_eq hrel

/-- The pointed gate: catch-up + pointed extension separability + a bounded base ⟹ the seal
consumer `SeparatesAtBoundedBase`. The general-CC-keyed sibling of
`separatesAtBoundedBase_of_separable` (resolving the Stage-4 keying note: no homogeneous
`Separable`/`SeparabilityTransports` in the chain). -/
theorem separatesAtBoundedBase_of_extensionPointed (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    {T : Finset (Fin n)} {bound : Nat} (hcard : T.card ≤ bound)
    (hbase : IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T)
    {E : CoherentConfig n}
    (hext : IsPointExtension (S.toAssociationScheme.toCoherentConfig hne) T E)
    (hsep : ∀ u : Fin n, ¬ E.SingletonFiber u → E.SeparablePointed u)
    (hcatch : WarmTwinsAreFiberTwins S T E) :
    SeparatesAtBoundedBase S bound :=
  separatesAtBoundedBase_of_twinsRealized S hcard hbase
    (twinsRealized_of_extensionPointed S hne hext hsep hcatch)

/-- The pointed gate with the group base picked internally (the (C)-free form, mirroring
`separatesAtBoundedBase_of_separable_of_small`): pointedness + catch-up at every base of the
**constructed** extension (`pointExtension`, §CC.8) + the "small" bound ⟹ `SeparatesAtBoundedBase`. -/
theorem separatesAtBoundedBase_of_extensionPointed_of_small (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    {bound : Nat}
    (hbound : Nat.log 2 (Nat.card (StabilizerAt (schemeAdj S.toAssociationScheme)
        (fun _ _ => POE.unknown) ∅)) ≤ bound)
    (hsep : ∀ (T : Finset (Fin n)) (u : Fin n),
      ¬ (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).SingletonFiber u →
      (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).SeparablePointed u)
    (hcatch : ∀ T : Finset (Fin n),
      WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T)) :
    SeparatesAtBoundedBase S bound := by
  obtain ⟨bs, hbase, hlen⟩ := exists_greedy_base_le_log
    (adj := schemeAdj S.toAssociationScheme) (P := fun _ _ => POE.unknown)
  refine separatesAtBoundedBase_of_extensionPointed S hne ?_ hbase
    (isPointExtension_pointExtension _ _) (hsep _) (hcatch _)
  calc (bs.foldl (fun s b => insert b s) (∅ : Finset (Fin n))).card
      ≤ (∅ : Finset (Fin n)).card + bs.length := card_foldl_insert_le bs ∅
    _ = bs.length := by simp
    _ ≤ _ := hlen
    _ ≤ bound := hbound

/-- **THE CITATION CHECKPOINT — the general conditional seal capstone of the general-CC build
(handoff item 4; the affine-slice pattern `reachesRigidOrCameron_affineSlice`, generalized).**
Every rank-≥3 schurian residual reaches the rigid side or is a Cameron section, conditional on
exactly: the cited classification `hClassify` (G3), the cited **`Theorem41Statement`** (`hcite`) with
its **probe-confirmed hypotheses on the extension** (`hhyp` — `Theorem41ConditionsProbe.cs` verified
them on the residue's one-point extension at every non-singleton fiber), the **catch-up** `hcatch`
(the isolated 1-WL↔fiber model gap, direction-check-shaped), a bounded base (`hbase`/`hcard` — free
for small schemes via `exists_greedy_base_le_log`), and the landed `hImprim`. Stage 3 proves `hcite`
restricted to the residue family (Route β) and discharges `hhyp` witness-constructively; `hcatch` is
the remaining model content. -/
theorem reachesRigidOrCameron_viaExtensionSeparability {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    {T : Finset (Fin n)} (hcard : T.card ≤ bound)
    (hbase : IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T)
    {E : CoherentConfig n}
    (hext : IsPointExtension (S.toAssociationScheme.toCoherentConfig hne) T E)
    (hcite : Theorem41Statement)
    (hhyp : ∀ u : Fin n, ¬ E.SingletonFiber u → E.Theorem41Hypotheses u)
    (hcatch : WarmTwinsAreFiberTwins S T E)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S := by
  refine reachesRigidOrCameron_viaPersistentTwinBlock hClassify S hne hrank ?_ hImprim
  intro hn
  exact absurd (separatesAtBoundedBase_of_extensionPointed S hne hcard hbase hext
    (fun u hns => hcite n E u (hhyp u hns)) hcatch) hn

/-- **THE CITATION-FREE CHECKPOINT (Route δ′) — the seal via the forced-triangle dominator closure.**
The same conditional seal as `reachesRigidOrCameron_viaExtensionSeparability`, but its separation input
is the **citation-free** dominator closure: a bounded base `T` whose forced-triangle closure exhausts Ω
(`hclo`). Carries exactly {G3 `hClassify` + `hImprim` + the single structural hypothesis `hclo`} — no
`Theorem41Statement`, no conditions-on-the-extension, no catch-up, no group base. The probe-gate
(`Probe_CatchUpGate_BasesAndDominators`) verified `hclo` at every minimal base of both residue instances;
Stage 3's family-level math proves it for the residue family ("the `c = 1` closure completes from a
bounded base"), which is the same open content as the extension-separability route in a citation-free
form. -/
theorem reachesRigidOrCameron_viaDominatorClosure {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    {T : Finset (Fin n)} (hcard : T.card ≤ bound)
    (hclo : ∀ v, DominatorReachable S.toAssociationScheme T v)
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S := by
  refine reachesRigidOrCameron_viaPersistentTwinBlock hClassify S hne hrank ?_ hImprim
  intro hn
  exact absurd (separatesAtBoundedBase_of_dominatorClosure S hcard hclo) hn

/-! #### The δ′ engine ON THE EXTENSION → the seal (for the `n ≥ 25` residue)

The scheme-level δ′ (`separatesAtBoundedBase_of_dominatorClosure`, above) is **citation- and catch-up-free**,
but its forced triangles live in `S`'s own colours — which the `Probe_RainbowRigidFamily` finding showed
**vanish for `n ≥ 25`** (`Z5²`: `c = 1` triangles gone, scheme-level closure fails from any base). The closure
there lives in the **point extension `X_T`'s finer colours** (`CoherentConfig.DominatorReachable` on
`pointExtension`, `Sharp` discharged by `sharp_pointExtension`). Wiring that back to the `warmRefine` seal
consumer needs one model bridge: the warm cell of a point must sit inside its `X_T` fiber — which is **exactly
the catch-up `WarmTwinsAreFiberTwins`**. So lifting δ′ to the extension (necessary for `n ≥ 25`) **re-incurs the
catch-up** the scheme-level δ′ avoided — but nothing heavier: when the extension is *complete* the catch-up
*alone* discretises `warmRefine` (no separability / Thm 4.1 / group content). `Probe_RainbowRigidFamily` also
settled the scope question: the 1-WL (`warmRefine`) base equals the 2-WL base `b(X)` on every residue instance
incl. `Z5²`, so **no dimWL-exchange citation is needed** — the bridge is residue-keyed. -/

/-- **Bridge: a complete extension + the catch-up ⟹ `warmRefine` is discrete.** If every point is a singleton
fiber of `E` (the extension is complete) and warm-twins are fiber-twins (`hcatch`), then same-`warmRefine`-cell
points coincide: the catch-up sends them to one `E`-fiber, completeness makes that fiber a point. The δ′-route
analogue of `twinsRealized_of_extensionPointed` — but consuming *completeness* (from the forced-triangle closure)
instead of *separability*, so the catch-up is the **only** carried hypothesis. -/
theorem discrete_warmRefine_of_extensionComplete (S : SchurianScheme n)
    {T : Finset (Fin n)} {E : CoherentConfig n}
    (hcomplete : ∀ u, E.SingletonFiber u)
    (hcatch : WarmTwinsAreFiberTwins S T E) :
    Discrete (warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
      (individualizedColouring n T)) := by
  intro u u' hcell
  exact hcomplete u' u (hcatch u u' hcell)

/-- **The catch-up is free once `warmRefine` is discrete** (the converse of
`discrete_warmRefine_of_extensionComplete`'s use of it, for *any* `E`): same-cell points are equal, so
they trivially share every reflexive `E`-relation. **The honest accounting in Lean:** taken together
with `discrete_warmRefine_of_extensionComplete`, this says that **at a complete extension `E`,
`WarmTwinsAreFiberTwins S T E ↔ Discrete (warmRefine …)`** — the catch-up carries *no information beyond
the 1-WL discreteness the seal concludes*. So for the `n ≥ 25` residue, where the δ′ closure delivers
only the *2-WL* (`X_T`) completeness, discharging `hcatch` is **equivalent to** establishing 1-WL
discreteness directly — it is genuine content (the dimWL 1-WL↔2-WL exchange / the `c(X_T)` layer), not
plumbing. It is *free* exactly where 1-WL already discretises (next lemma). -/
theorem warmTwinsAreFiberTwins_of_warmDiscrete (S : SchurianScheme n)
    {T : Finset (Fin n)} {E : CoherentConfig n}
    (hdisc : Discrete (warmRefine (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown)
      (individualizedColouring n T))) :
    WarmTwinsAreFiberTwins S T E := by
  intro u u' hcell
  rw [hdisc u u' hcell]

/-- **The catch-up holds wherever the *scheme-level* δ′ closure does** — in particular on the order-16
residue (`clebschZ4_closure`, n=16), where the forced triangles live in `S`'s own colours and 1-WL
discretises outright. So the extension capstone `reachesRigidOrCameron_viaExtensionDominatorClosure` is
non-vacuous: on the schemes the scheme-level engine already closes, `hcatch` is discharged for free (and
the two routes agree). It does **not** extend to `n ≥ 25` — there 1-WL discreteness is exactly the open
content (see `warmTwinsAreFiberTwins_of_warmDiscrete`'s note). -/
theorem warmTwinsAreFiberTwins_of_dominatorClosure (S : SchurianScheme n)
    {T : Finset (Fin n)} {E : CoherentConfig n}
    (hclo : ∀ v, DominatorReachable S.toAssociationScheme T v) :
    WarmTwinsAreFiberTwins S T E :=
  warmTwinsAreFiberTwins_of_warmDiscrete S (discrete_of_dominatorClosure S.toAssociationScheme hclo)

/-- **δ′-on-the-extension, packaged for the seal consumer.** A bounded base `T` whose forced-triangle closure
exhausts Ω **on the point extension `X_T`** (`hclo`), with the catch-up at `T`, discretises the scheme:
`SeparatesAtBoundedBase S bound`. `Sharp` is discharged internally (`sharp_pointExtension`), so the open input
is exactly `hclo` (the `c(X_T)` content) plus the probe-green catch-up. The `n ≥ 25` sibling of
`separatesAtBoundedBase_of_dominatorClosure` (which only reaches `n = 16`). -/
theorem separatesAtBoundedBase_of_extensionDominatorClosure (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    {T : Finset (Fin n)} {bound : Nat} (hcard : T.card ≤ bound)
    (hclo : ∀ v, (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).DominatorReachable T v)
    (hcatch : WarmTwinsAreFiberTwins S T
        (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T)) :
    SeparatesAtBoundedBase S bound :=
  ⟨T, hcard, discrete_warmRefine_of_extensionComplete S
    (CoherentConfig.allSingletonFiber_of_dominatorClosure_pointExtension
      (S.toAssociationScheme.toCoherentConfig hne) T hclo) hcatch⟩

/-- **THE δ′-ON-THE-EXTENSION SEAL CHECKPOINT (the `n ≥ 25` citation-free path).** Identical plumbing to
`reachesRigidOrCameron_viaDominatorClosure`, but fed by the **extension** closure + catch-up, so it covers the
residue where `S`'s own colours have no `c = 1` triangles. Carries exactly {G3 `hClassify` + `hImprim` +
`hclo` (the open `c(X_T)` content on `X_T`) + `hcatch` (the probe-green 1-WL↔fiber catch-up at `T`)}. -/
theorem reachesRigidOrCameron_viaExtensionDominatorClosure {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    {T : Finset (Fin n)} (hcard : T.card ≤ bound)
    (hclo : ∀ v, (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).DominatorReachable T v)
    (hcatch : WarmTwinsAreFiberTwins S T
        (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S := by
  refine reachesRigidOrCameron_viaPersistentTwinBlock hClassify S hne hrank ?_ hImprim
  intro hn
  exact absurd (separatesAtBoundedBase_of_extensionDominatorClosure S hne hcard hclo hcatch) hn

/-- **THE SEAL VIA BOUNDED EXTENSION PARAMETERS (the A2 content as a clean parameter predicate).** Same
conclusion as `reachesRigidOrCameron_viaExtensionDominatorClosure`, but the open input `hclo` (the abstract
forced-triangle closure) is replaced by the concrete **A2 inequality** `hparam`: at *some* `O(1)` base `T₀`,
`(k(X_{T₀})−1)·c(X_{T₀}) < |T|` for the padded base `T ⊇ T₀`. This is the residue's **bounded WL-dimension**
content (`c(X_{T₀}), k(X_{T₀}) = O(1)` at a small base) — the genuine G2-B frontier, confirmed *open / not
citable* by the rank-3/4 SRG WL-dimension research (2026-06-14): the carve-out is validated (the unbounded-WL
SRG families — triangular/Johnson, lattice/Hamming, conference/Paley — are all large→Cameron, imprimitive, or
abelian→leg B), and the known small-automorphism primitive family (Fon-Der-Flaass/CGGP) has WL-dim ≤ 4, but no
uniform theorem covers the residue. So the seal stands **conditional `modulo {G3 + bounded-extension-params +
hcatch + hImprim}`**, with the A2 piece now a checkable parameter inequality (`§CC.18`/`§CC.19`). Axiom-clean. -/
theorem reachesRigidOrCameron_viaBoundedExtensionParams {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank)
    {T₀ T : Finset (Fin n)} (hsub : T₀ ⊆ T) (hcard : T.card ≤ bound)
    (hparam : ((pointExtension (S.toAssociationScheme.toCoherentConfig hne) T₀).maxValency - 1)
        * (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T₀).indistinguishingNumber
        < T.card)
    (hcatch : WarmTwinsAreFiberTwins S T
        (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
      ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaExtensionDominatorClosure hClassify S hne hrank hcard
    ((S.toAssociationScheme.toCoherentConfig hne).dominatorReachable_of_card_gt_subset hsub hparam)
    hcatch hImprim

/-- **THE SEAL VIA THE POTENTIAL-DROP HYPOTHESIS (the A2 open content as a per-step drop — the uniform route).**
The same conclusion as `reachesRigidOrCameron_viaBoundedExtensionParams`, but the A2 inequality `hparam` is
replaced by its *uniform* generator `hdrop : PotentialDrops B`: from any base whose potential
`(k(X_T)−1)·c(X_T)` exceeds `B`, *some* individualization at least halves it. The iteration engine
(`§CC.20 exists_small_base_of_potentialDrops`) turns that into a small base `T₀` with potential `≤ B`, which is
then padded (`§CC.18/19`) to a base `T` of size `B+1`. **`PotentialDrops` is the single open mathematical
content** — the "shattering" the probe (`A2MonovariantProbe.cs`) found holds on the non-geometric residue and
fails (climbs to 1) only on the geometric/Cameron-carved families; discharging it via the Neumaier/CGGP
dichotomy (`docs/chain-descent-a2-potential-route.md` §3) closes A2. So the seal stands **conditional
`modulo {G3 + PotentialDrops + hcatch + hImprim}`**, with the A2 piece now the per-step drop. Axiom-clean. -/
theorem reachesRigidOrCameron_viaPotentialDrop {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hdrop : (S.toAssociationScheme.toCoherentConfig hne).PotentialDrops B)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S := by
  obtain ⟨T₀, hpot, _⟩ :=
    (S.toAssociationScheme.toCoherentConfig hne).exists_small_base_of_potentialDrops hB hdrop
  set m := max T₀.card (B + 1)
  obtain ⟨T, hsub, hTcard⟩ :=
    Finset.exists_superset_card_eq (s := T₀) (n := m) (le_max_left _ _)
      (by rw [Fintype.card_fin]; exact max_le ((Finset.card_le_univ T₀).trans_eq (Fintype.card_fin n)) hroom)
  have hBT : B < T.card := by rw [hTcard]; exact lt_of_lt_of_le (Nat.lt_succ_self B) (le_max_right _ _)
  exact ⟨m, reachesRigidOrCameron_viaBoundedExtensionParams hClassify S hne hrank hsub hTcard.le
    (lt_of_le_of_lt hpot hBT) (hcatch T) hImprim⟩

/-- **THE SEAL VIA THE SHATTERING HYPOTHESIS (Stage 1b — the open content sharpened to `c`-halving).** The same
conclusion as `reachesRigidOrCameron_viaPotentialDrop`, but the per-step drop on the *product* `(k−1)c` is
replaced by its *cleaner generator* `hshatter : IndistinguishingHalves B`: from any base whose potential exceeds
`B`, some individualization at least **halves the indistinguishing number `c(X_T)`** alone. The max valency `k`
rides along free (`maxValency_mono` — build doc §1B), so `c`-halving generates the potential-halving
(`potentialDrops_of_indistinguishingHalves`), which the `§CC.20` engine turns into the seal. **So the seal's lone
open mathematical content is now exactly `IndistinguishingHalves`** — and a `c`-class that resists halving under
every individualization is a partial-geometry line system (probe `A2MonovariantProbe.Probe_SmallestEigenvalueAxis`,
`docs/chain-descent-a2-potential-route.md` §3/§5: the drop-obstruction is the line/grid geometry, not the
smallest-eigenvalue magnitude). Seal conditional **`modulo {G3 + IndistinguishingHalves + hcatch + hImprim}`**.
Axiom-clean. -/
theorem reachesRigidOrCameron_viaShattering {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hshatter : (S.toAssociationScheme.toCoherentConfig hne).IndistinguishingHalves B)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaPotentialDrop hB hClassify S hne hrank hroom
    ((S.toAssociationScheme.toCoherentConfig hne).potentialDrops_of_indistinguishingHalves hshatter)
    hcatch hImprim

/-- **THE SEAL VIA BOUNDED CONFUSION MULTIPLICITY (route §9.8 part 1 — "the residue cascades ⟹ polynomial").**
The same conclusion as `reachesRigidOrCameron_viaShattering`, but the single-vertex `c`-halving is replaced by the
*cascade-rate* hypothesis `hmult : BoundedConfusionMultiplicity B M`: from any over-`B` base, individualizing a
**bounded set of `≤ M` vertices** halves `c(X_T)` (pin the least-covered vertex, clean up the `≤ M` confusion sets
it lies in — the multiplicity reframe, `docs/chain-descent-a2-potential-route.md` §9.6, measured by the probe's
`minMult`). The `§CC.20b` engine (`exists_small_base_of_boundedConfusionMultiplicity`) turns it into a base `T₀`
with potential `≤ B` of size `O(M·log n)`, padded to a base `T` as in `viaPotentialDrop`. **Strictly weaker
hypothesis than `IndistinguishingHalves`** (which is the `M = 1`, single-vertex special case), so this is the
sharpest open form: the seal stands `modulo {G3 + BoundedConfusionMultiplicity + hcatch + hImprim}`, and the entire
open mathematical content is now the single discharge **"the residue has bounded confusion multiplicity `M`"** (the
rank-3 base case, §9.8.2 part 2 — attacked directly, no citation). Axiom-clean. -/
theorem reachesRigidOrCameron_viaBoundedMultiplicity {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B M : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hmult : (S.toAssociationScheme.toCoherentConfig hne).BoundedConfusionMultiplicity B M)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S := by
  obtain ⟨T₀, hpot, _⟩ :=
    (S.toAssociationScheme.toCoherentConfig hne).exists_small_base_of_boundedConfusionMultiplicity hB hmult
  set m := max T₀.card (B + 1)
  obtain ⟨T, hsub, hTcard⟩ :=
    Finset.exists_superset_card_eq (s := T₀) (n := m) (le_max_left _ _)
      (by rw [Fintype.card_fin]; exact max_le ((Finset.card_le_univ T₀).trans_eq (Fintype.card_fin n)) hroom)
  have hBT : B < T.card := by rw [hTcard]; exact lt_of_lt_of_le (Nat.lt_succ_self B) (le_max_right _ _)
  exact ⟨m, reachesRigidOrCameron_viaBoundedExtensionParams hClassify S hne hrank hsub hTcard.le
    (lt_of_le_of_lt hpot hBT) (hcatch T) hImprim⟩

/-- **THE SEAL VIA SMALL-AUT BOUNDED MULTIPLICITY (the sharp `minMult`-form dichotomy — route §9.9 D3).** The faithful
large/small dichotomy stated in the *achievable* quantity. Carry `hSmallAutThin : ¬IsLarge → BoundedMinMult B M`
("small Aut ⟹ some vertex lies in `≤ M` big confusion pairs at every over-`B` base", i.e. bounded `minMult`), and
`by_cases` on largeness: **large** ⟹ the cited **G3** (`exhaustiveObstruction_scheme`) gives Cameron on the primitive
floor, else `hImprim`; **small** ⟹ `hSmallAutThin` feeds `boundedConfusionMultiplicity_of_boundedMinMult` (the §CC.22d
`(1+L)`-cleanup) ⟹ `…viaBoundedMultiplicity` (the §CC.20b cascade engine). **Strictly sharper than
`…viaSmallAutShatters`:** it asks only for *bounded* load (`minMult ≤ M`), not the stronger *zero* load
(`¬BigConfusionCover` = an avoiding vertex) — which the probe (§9.7) showed rarely holds, since confusion covers are
intrinsically loose. So the carried citation `hSmallAutThin` is the **`minMult`-form of Babai's SRG structure theorem**
(small Aut ⟹ not a thick named family ⟹ bounded confusion multiplicity) — the exact computable quantity the probe
measures, and the entire open content of node 4 (route §9.9: "primitive non-Cameron ⟹ thin"). Seal `modulo
{G3 (hClassify) + hSmallAutThin (small-Aut⟹thin) + hcatch + hImprim}`. Axiom-clean. -/
theorem reachesRigidOrCameron_viaBoundedMinMult {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B M : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hSmallAutThin : ¬ IsLargeSchemeViaAut IsLarge n S →
        (S.toAssociationScheme.toCoherentConfig hne).BoundedMinMult B M)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S := by
  by_cases hlarge : IsLargeSchemeViaAut IsLarge n S
  · -- Large ⟹ the cited G3 gives Cameron on the primitive floor, else `hImprim` recovers.
    by_cases hprim : S.toAssociationScheme.IsPrimitive
    · exact ⟨0, Or.inr (exhaustiveObstruction_scheme hClassify S hne hprim hrank hlarge)⟩
    · exact ⟨0, Or.inl (Or.inl (hImprim hprim))⟩
  · -- Small Aut ⟹ bounded `minMult` ⟹ cascade (the §CC.22d cleanup + §CC.20b engine).
    exact reachesRigidOrCameron_viaBoundedMultiplicity hB hClassify S hne hrank hroom
      ((S.toAssociationScheme.toCoherentConfig hne).boundedConfusionMultiplicity_of_boundedMinMult
        (hSmallAutThin hlarge))
      hcatch hImprim

/-- **THE SEAL VIA NO BIG-CONFUSION COVER (Stage 1b, G-cite — the two citations SEPARATED to isolated literals).**
The A2 open content packaged so each carried citation is **one literal external theorem** (toward replacing each
with its Lean proof). The cover dichotomy `cover ⟹ Cameron` is *factored* into its two genuine pieces, instead of
carried as a single composite:
* the **Cameron step reuses the project's canonical G3** `hClassify` (`PrimitiveCCClassification`, Babai 1981 /
  Sun–Wilmes 2015: large primitive ⟹ Cameron) — via `exhaustiveObstruction_scheme`, no new carry;
* the only **new** carried citation is the geometric/structure direction `hNeumaier : (∃ over-`B` cover) ⟹ IsLarge`
  — *"a scheme whose extension resists discretization at a bounded base is large."* Its faithful citation is **Babai's
  SRG structure theorem** (cxt-scoping §4.2): a primitive SRG is *large-motion* (small Aut — the residue) **or** a named
  geometric family (triangular/Johnson, lattice/Hamming) of thickness `≥ √n`, hence **large Aut**; rank-4 amorphic via
  Kivva (JCTB'23). Neumaier's claw bound is only the *geometric-classification ingredient* — "geometric ⟹ large Aut"
  alone is **false** (a generic partial geometry / CGGP construction has trivial Aut). A cover is the
  *resists-individualization* witness (`card_bigClasses_mul_ge_of_cover`: `≥ n/c` near-maximal confusion classes = a
  rigid line system) ⟹ `¬large-motion` ⟹ named family ⟹ large. **⚠ Faithful only at the SUB-EXPONENTIAL largeness
  threshold** where Babai/Kivva (and G3) are proven; at a *polynomial* threshold it is the **open rank-3 base case** (a
  small-Aut SRG could have base between poly and quasipoly, giving a cover while small — falsifying it). Full scoping +
  what proving it would take: route-doc `chain-descent-a2-potential-route.md` §8.

The proof case-splits on the cover: **no cover** ⟹ every over-`B` base shatters, so
`indistinguishingHalves_of_not_bigConfusionCover` feeds `reachesRigidOrCameron_viaShattering` (recovered); **cover**
⟹ `hNeumaier` gives `IsLarge`, then **primitive** ⟹ the cited G3 (`exhaustiveObstruction_scheme`) gives Cameron,
**imprimitive** ⟹ `hImprim` recovers. So the seal stands **conditional `modulo {G3 (hClassify) + Babai-SRG-structure
(hNeumaier) + hcatch + hImprim}`** — each a single isolated literal theorem rather than a project-specific composite.
**Honest scope:** `hNeumaier` is faithful as a *sub-exponential-threshold* citation (Babai/Kivva); the *polynomial*
version is the open rank-3 base case (route-doc §8). CGGP (`n^Ω(n^{2/3})` trivial-Aut SRGs, all WL-dim ≤ 4) is the
positive anchor that the residue stays tame; row-4 (generic non-geometric) is where it bites — the probe reframe argues
row 4 has no rigid line system, hence no cover (it shatters, landing in the `¬cover` branch). Axiom-clean. -/
theorem reachesRigidOrCameron_viaNoConfusionCover {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hNeumaier : (∃ T : Finset (Fin n),
          B < (S.toAssociationScheme.toCoherentConfig hne).potential T
            ∧ (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).BigConfusionCover)
        → IsLargeSchemeViaAut IsLarge n S)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S := by
  by_cases hcov : ∃ T : Finset (Fin n),
      B < (S.toAssociationScheme.toCoherentConfig hne).potential T
        ∧ (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).BigConfusionCover
  · -- A cover ⟹ (Neumaier) large; then the cited G3 gives Cameron on the primitive floor, else `hImprim` recovers.
    have hlarge : IsLargeSchemeViaAut IsLarge n S := hNeumaier hcov
    by_cases hprim : S.toAssociationScheme.IsPrimitive
    · exact ⟨0, Or.inr (exhaustiveObstruction_scheme hClassify S hne hprim hrank hlarge)⟩
    · exact ⟨0, Or.inl (Or.inl (hImprim hprim))⟩
  · -- No cover ⟹ every over-`B` base shatters ⟹ recovered.
    push_neg at hcov
    exact reachesRigidOrCameron_viaShattering hB hClassify S hne hrank hroom
      ((S.toAssociationScheme.toCoherentConfig hne).indistinguishingHalves_of_not_bigConfusionCover B hcov)
      hcatch hImprim

/-- **THE SEAL VIA SMALL-AUT SHATTERING (Stage 1b, G-cite — the FAITHFUL-direction citation; route-doc §8.5).**
The citation-faithful sibling of `reachesRigidOrCameron_viaNoConfusionCover`: it carries the geometric/structure
citation in the **direction the literature actually proves** and case-splits on the **genuine largeness dichotomy**
(`IsLarge`?), not on "a cover exists."

* `…viaNoConfusionCover` carries `hNeumaier : (∃ over-`B` cover) ⟹ IsLarge` — the "high WL-dim ⟹ large Aut" reading,
  which is the **CGGP-false** direction ("geometric ⟹ large Aut" is false; a generic partial geometry / CGGP
  construction has trivial Aut). It states the citation *backwards* from what Babai's structure theorem gives.
* This capstone instead carries `hSmallAutDiscretizes : ¬IsLarge ⟹ ∀ over-`B` base, ¬BigConfusionCover` — *"a
  small-Aut primitive SRG shatters: a bounded base discretizes its extension, leaving no surviving confusion cover."*
  This is the **true** direction of **Babai's SRG structure theorem + Kivva** (small Aut ⟹ large-motion ⟹ bounded
  base ⟹ discretizes), and — unlike `hNeumaier`'s direction — it is *derivable from honest sources*: Phase 3 factors
  it as {Babai's cited `¬IsLarge ⟹ bounded complete base` + the provable bridge
  `not_bigConfusionCover_of_allSingletonFiber` (`complete ⟹ ¬cover`, §CC.22)}. Logically `hSmallAutDiscretizes` is the
  contrapositive of `hNeumaier`, so this is **no weaker**; the gain is faithfulness of statement + a derivation path.

Proof: `by_cases` on `IsLarge`. **Large** ⟹ primitive → the cited G3 (`exhaustiveObstruction_scheme`) → Cameron;
imprimitive → `hImprim` recovers. **¬Large** ⟹ `hSmallAutDiscretizes` gives no over-`B` cover, so
`indistinguishingHalves_of_not_bigConfusionCover` feeds `reachesRigidOrCameron_viaShattering` (recovered). Seal
**`modulo {G3 (hClassify) + Babai-SRG-structure (hSmallAutDiscretizes) + hcatch + hImprim}`**. **Honest scope
unchanged:** faithful at the *sub-exponential* threshold (Babai/Kivva/G3); the polynomial version is the open rank-3
base case (route-doc §8). Axiom-clean. -/
theorem reachesRigidOrCameron_viaSmallAutShatters {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hSmallAutDiscretizes : ¬ IsLargeSchemeViaAut IsLarge n S →
        ∀ T : Finset (Fin n),
          B < (S.toAssociationScheme.toCoherentConfig hne).potential T →
          ¬ (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).BigConfusionCover)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S := by
  by_cases hlarge : IsLargeSchemeViaAut IsLarge n S
  · -- Large ⟹ the cited G3 gives Cameron on the primitive floor, else `hImprim` recovers.
    by_cases hprim : S.toAssociationScheme.IsPrimitive
    · exact ⟨0, Or.inr (exhaustiveObstruction_scheme hClassify S hne hprim hrank hlarge)⟩
    · exact ⟨0, Or.inl (Or.inl (hImprim hprim))⟩
  · -- Small Aut ⟹ shatters (no over-`B` cover) ⟹ recovered.
    exact reachesRigidOrCameron_viaShattering hB hClassify S hne hrank hroom
      ((S.toAssociationScheme.toCoherentConfig hne).indistinguishingHalves_of_not_bigConfusionCover B
        (hSmallAutDiscretizes hlarge))
      hcatch hImprim

/-- **THE SEAL VIA DIRECT SHATTERING — the polynomial target (node 4), no largeness citation.** This is the
*unconditional* form of `…viaSmallAutShatters`/`…viaNoConfusionCover`: it carries the single hypothesis
`hShatter : ∀ over-`B` base `T`, ¬BigConfusionCover (X_T)` **with no `¬IsLarge` guard and no Cameron routing**.
Discharging `hShatter` for the residue makes the seal **polynomial** — the residue always shatters (a `c(X_T)/2`-
avoiding vertex exists at every over-`B` base, so `c` halves per individualization), giving an `O(log n)` base with
`c(X_{T₀}) = O(1)`; the Cameron disjunct is never taken on the shattering path. So **`hShatter` is exactly node 4**
(`docs/chain-descent-a2-potential-route.md` §9): the open rank-3 base case stated in the project's own language —
*a primitive, non-geometric, non-conference SRG never develops a big-confusion cover under individualization.* Its
negation (a cover) is, by `card_bigClasses_mul_ge_of_cover`, a covering of `Fin n` by `≥ n/c` near-maximal confusion
classes = a partial-geometry / near-pencil line system, which a non-geometric residue lacks (probe `Probe_Smallest
EigenvalueAxis`: the obstruction is the line/grid geometry). Carries only `{G3 (hClassify, unused on the shattering
path) + hShatter (node 4) + hcatch + hImprim}` — no Babai/Spielman/Neumaier citation, poly-capable. Pure composition
of `indistinguishingHalves_of_not_bigConfusionCover` + `reachesRigidOrCameron_viaShattering`. Axiom-clean. -/
theorem reachesRigidOrCameron_viaNoCover {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {B : Nat} (hB : 1 ≤ B)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (S : SchurianScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hrank : 2 ≤ S.rank) (hroom : B + 1 ≤ n)
    (hShatter : ∀ T : Finset (Fin n),
        B < (S.toAssociationScheme.toCoherentConfig hne).potential T →
        ¬ (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T).BigConfusionCover)
    (hcatch : ∀ T : Finset (Fin n),
        WarmTwinsAreFiberTwins S T (pointExtension (S.toAssociationScheme.toCoherentConfig hne) T))
    (hImprim : ¬ S.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered n S ∨ AbelianConsumed n S) :
    ∃ bound : Nat,
      ((SchemeBlockRecovered n S ∨ AbelianConsumed n S) ∨ SchemeRecoveredByDepth n S bound)
        ∨ IsCameronScheme n S :=
  reachesRigidOrCameron_viaShattering hB hClassify S hne hrank hroom
    ((S.toAssociationScheme.toCoherentConfig hne).indistinguishingHalves_of_not_bigConfusionCover B hShatter)
    hcatch hImprim

end SGate2


/-! ### §13b — the two-round (depth-2) separation engine on `schemeAdj` (E1)

`relOfPair_eq_of_warmRefine_singleton` (§13a) is the **depth-1** separation primitive: a `warmRefine`
cell refines the depth-1 `relOfPair` profile, and from a *single* base that already recovers
(`cellsAreOrbits_schemeAdj_singleton`). For the `s(C) ≥ 2` regime (cyclotomic and friends) one round is
insufficient — the depth-1 *joint* profile of a small base is a coset twin — and from a single base depth-2
counts collapse to intersection numbers (`AssociationScheme.intersectionCount_via_w`), adding nothing. The
genuine content is therefore inherently **multi-base, two-round**: this subsection lands the reusable
two-round count primitive, the `schemeAdj` analogue of the intersection-number separation
(`IntersectionSeparates`/`depth2Det`). It generalises the single-base depth-`k` count machinery
(`iter_succ_count_eq` &c. in `Scheme.lean`, keyed on `individualizedColouring n {v}`) to an arbitrary base
**set** `T`, keyed on the public `signature_eq_card_eq`. It is the brick the affine-cyclic bound proof (and
any future primitive-floor slice) consumes; the conversion from the one-round colour grouping to the joint
`(relOfPair t ·)_{t∈T}` profile is the consumer's job (`relOfPair_eq_of_warmRefine_singleton`, depth-1). -/

/-- **Two-round count separation (the depth-2 primitive, E1).** For `w, u` in the same
`warmRefine (schemeAdj S)`-cell after individualizing a base set `T`, the **depth-2 count profile**
coincides: for every one-round colour `c` (`refineStep` of the individualised colouring) and every relation
`b`, the number of `z ≠ w` whose one-round colour is `c` and `relOfPair w z = b` equals the corresponding
count for `u`. Mechanism: peel `warmRefine = refineStep^[n]` to `refineStep^[2]` (`warmRefine_eq_iter_eq`),
read off `signature`-equality at the one-round colouring (`refineStep_iff`), and apply the count bridge
(`signature_eq_card_eq`). The one-round colour `c` refines the joint `(relOfPair t ·)_{t∈T}` profile
(depth-1, §13a), so grouping by `c` is finer than grouping by the relations-to-`T` — that conversion is the
consumer's job. -/
theorem twoRoundCount_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (c : Nat) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  by_cases hn : 2 ≤ n
  · -- peel `warmRefine = refineStep^[n]` to `refineStep^[2]`, read `signature` at `refineStep χ`
    have h2 : ((refineStep adj P)^[2]) χ w = ((refineStep adj P)^[2]) χ u :=
      warmRefine_eq_iter_eq adj P χ 2 hn h
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one] at h2
    have hsig : signature adj P (refineStep adj P χ) w = signature adj P (refineStep adj P χ) u :=
      ((refineStep_iff adj P (refineStep adj P χ) w u).mp h2).2
    have hcard := signature_eq_card_eq adj P (refineStep adj P χ) hsig (c, b.val, POE.unknown)
    -- the two filter predicates coincide (P is always `unknown`; `adj` reads `relOfPair`)
    have hpred : ∀ x : Fin n, ∀ z : Fin n,
        (z ≠ x ∧ refineStep adj P χ z = c ∧ S.relOfPair x z = b)
          ↔ (z ≠ x ∧ (c, b.val, POE.unknown) = (refineStep adj P χ z, adj.adj x z, P x z)) := by
      intro x z
      refine and_congr_right (fun _ => ?_)
      have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
      have hPval : P x z = POE.unknown := rfl
      rw [hadjval, hPval, Prod.mk.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hcz, hbz⟩; exact ⟨hcz.symm, by rw [hbz], rfl⟩
      · rintro ⟨hc, hb, -⟩; exact ⟨hc.symm, (Fin.val_injective hb).symm⟩
    rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
    exact hcard
  · -- `n ≤ 1`: `Fin n` is subsingleton, `w = u`, the two filters coincide
    have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    rw [Subsingleton.elim w u]

/-- **The depth-2 discreteness producer (E1).** If the depth-2 count profile — for every one-round colour
`c` and relation `b`, the number of `z` at one-round colour `c` with `relOfPair · z = b` — separates all
vertices, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. The depth-2 analogue of
`discrete_of_jointProfileSeparates` (which keys on the *depth-1* joint profile, insufficient for `s(C) ≥ 2`):
same-cell vertices share the depth-2 profile (`twoRoundCount_eq_of_warmRefine`), so an injective profile
forces singletons. Composes with `stablyRecoverable_of_discrete` → `selfDetectsStably_of_discretizes`, so a
bounded base `T` with a separating depth-2 profile closes the seal on that family. This is the producer the
affine-cyclic (`s(C) ≥ 2`) bound proof discharges (exhibit such a `T` of size `base + O(1)`). -/
theorem discrete_of_twoRoundProfileSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (hsep : ∀ u u' : Fin n,
        (∀ (c : Nat) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
            S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z = c ∧
            S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun c b => twoRoundCount_eq_of_warmRefine S hcell c b)

/-- **Lemma A — the one-round colour determines the relation to each base point (the colour→relation
bridge).** If `z, z'` share their one-round colour `refineStep (schemeAdj S) … (individualizedColouring n T)`,
then for every `t ∈ T`, `relOfPair t z = relOfPair t z'`. So the one-round colour *refines* the joint profile
`(relOfPair t ·)_{t∈T}` — the missing link to re-group the depth-2 counts of
`twoRoundCount_eq_of_warmRefine` by relation rather than by the opaque colour. Mirrors
`relOfPair_eq_of_warmRefine_singleton`'s isolation argument, but at **one** `refineStep` round and a base
**set** `T`: the individualized `t ∈ T` carries a unique colour (`individualizedColouring_mem_sep`), so its
signature tuple is isolated, forcing `adj z t = adj z' t` i.e. `relOfPair z t = relOfPair z' t`. -/
theorem relOfPair_eq_of_refineStep_base {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {t : Fin n} (ht : t ∈ T) {z z' : Fin n}
    (h : refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z
       = refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z') :
    S.relOfPair t z = S.relOfPair t z' := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  have hcol : individualizedColouring n T z = individualizedColouring n T z' :=
    ((refineStep_iff adj P (individualizedColouring n T) z z').mp h).1
  have hsig : signature adj P (individualizedColouring n T) z
            = signature adj P (individualizedColouring n T) z' :=
    ((refineStep_iff adj P (individualizedColouring n T) z z').mp h).2
  have hχt : individualizedColouring n T t = t.val + 1 := by simp [individualizedColouring, ht]
  have hχ_eq_t : ∀ x : Fin n, individualizedColouring n T x = t.val + 1 → x = t := by
    intro x hx
    by_contra hxt
    exact (individualizedColouring_mem_sep ht x hxt) (hx.trans hχt.symm)
  by_cases hzt : z = t
  · have hz' : z' = t := hχ_eq_t z' (by rw [← hcol, hzt, hχt])
    rw [hzt, hz']
  · by_cases hz't : z' = t
    · exact absurd (hχ_eq_t z (by rw [hcol, hz't, hχt])) hzt
    · have hcard := signature_eq_card_eq adj P (individualizedColouring n T) hsig
        (individualizedColouring n T t, adj.adj z t, P z t)
      have hFz : (Finset.univ.filter (fun u' : Fin n => u' ≠ z ∧
          (individualizedColouring n T t, adj.adj z t, P z t)
            = (individualizedColouring n T u', adj.adj z u', P z u'))) = {t} := by
        apply Finset.ext; intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩; exact hχ_eq_t x ((congrArg Prod.fst heq).symm.trans hχt)
        · rintro rfl; exact ⟨Ne.symm hzt, rfl⟩
      rw [hFz, Finset.card_singleton] at hcard
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (hcard ▸ Nat.one_pos)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, hxeq⟩ := hx
      have hxt : x = t := hχ_eq_t x ((congrArg Prod.fst hxeq).symm.trans hχt)
      have hval : adj.adj z t = adj.adj z' t := by
        have hv := congrArg (fun p : Nat × Nat × POE => p.2.1) hxeq
        rwa [hxt] at hv
      have hrel : S.relOfPair z t = S.relOfPair z' t := Fin.val_injective hval
      rw [S.relOfPair_symm t z, S.relOfPair_symm t z']; exact hrel

/-- **Two-round count, aggregate (countP) form (E1).** The predicate-indexed generalization of
`twoRoundCount_eq_of_warmRefine`: for `w, u` in the same `warmRefine`-from-`T` cell, every count of `z`
whose one-round colour satisfies a predicate `q` and whose relation to the base point is `b` agrees between
`w` and `u`. Same peel-and-count proof but via the aggregate `signature_eq_countP_eq`. This lets the colour
grouping be re-expressed by *any* colour predicate — the vehicle for the colour→relation conversion. -/
theorem twoRoundCountP_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (q : Nat → Prop) [DecidablePred q] (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z) ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z) ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  by_cases hn : 2 ≤ n
  · have h2 : ((refineStep adj P)^[2]) χ w = ((refineStep adj P)^[2]) χ u :=
      warmRefine_eq_iter_eq adj P χ 2 hn h
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one] at h2
    have hsig : signature adj P (refineStep adj P χ) w = signature adj P (refineStep adj P χ) u :=
      ((refineStep_iff adj P (refineStep adj P χ) w u).mp h2).2
    have hcard := signature_eq_countP_eq adj P (refineStep adj P χ) hsig
      (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
    have hpred : ∀ x : Fin n, ∀ z : Fin n,
        (z ≠ x ∧ q (refineStep adj P χ z) ∧ S.relOfPair x z = b)
          ↔ (z ≠ x ∧ (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
                (refineStep adj P χ z, adj.adj x z, P x z)) := by
      intro x z
      refine and_congr_right (fun _ => ?_)
      show (q (refineStep adj P χ z) ∧ S.relOfPair x z = b)
        ↔ (q (refineStep adj P χ z) ∧ adj.adj x z = b.val)
      have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
      rw [hadjval]
      exact and_congr_right (fun _ => Fin.ext_iff)
    rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
    exact hcard
  · have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    rw [Subsingleton.elim w u]

/-- **Two-round count, joint-relation form (E1 — the colour→relation conversion, the payoff).** Re-groups
`twoRoundCount` by the **joint relation profile** `(relOfPair t z)_{t∈T}` instead of the opaque one-round
colour: for `w, u` in the same `warmRefine`-from-`T` cell, every count of `z` whose relations to all base
points match a target profile `ρ` and whose relation `relOfPair · z = b` agrees between `w` and `u`. Combines
`twoRoundCountP_eq_of_warmRefine` (aggregate) with `relOfPair_eq_of_refineStep_base` (Lemma A: the one-round
colour determines the joint profile), so the colour predicate `q c := ∃ z₀, colour z₀ = c ∧ profile z₀ = ρ`
reads exactly as the profile condition. **This is the relation-indexed depth-2 count the Frobenius / affine
separability argument consumes** — the object `relOfPair`/`G₀`-orbit counting lives in, not opaque colours. -/
theorem twoRoundProfileCount_eq {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card := by
  classical
  set q : Nat → Prop := fun c => ∃ z₀ : Fin n,
    refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z₀ = c
      ∧ ∀ t ∈ T, S.relOfPair t z₀ = ρ t with hq_def
  have hq : ∀ z : Fin n,
      q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
        ↔ ∀ t ∈ T, S.relOfPair t z = ρ t := by
    intro z
    constructor
    · rintro ⟨z₀, hz₀, hprof⟩ t ht
      exact (relOfPair_eq_of_refineStep_base S ht hz₀).symm.trans (hprof t ht)
    · intro hprof; exact ⟨z, rfl, hprof⟩
  rw [show (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
            ∧ S.relOfPair w z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z]),
    show (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          q (refineStep (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) z)
            ∧ S.relOfPair u z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z])]
  exact twoRoundCountP_eq_of_warmRefine S h q b

/-- **The relation-indexed depth-2 discreteness producer (E1 — the conversion complete).** If the joint
relation-profile counts separate all vertices — for every target profile `ρ` and relation `b`, equal counts
of `z` matching `(relOfPair t z = ρ t)_{t∈T}` together with `relOfPair · z = b` force the two vertices equal
— then `warmRefine (schemeAdj S)` from `T` is `Discrete`. The relation-form analogue of
`discrete_of_twoRoundProfileSeparates` (which keyed on the opaque one-round colour), via
`twoRoundProfileCount_eq`. **This is the producer the Frobenius / affine `s(C)` bound discharges**: exhibit a
bounded `T` whose joint relation-profile counts separate (the Galois-breaking base), then this gives
discreteness, feeding `stablyRecoverable_of_discrete` → `selfDetectsStably_of_discretizes` →
`reachesRigidOrCameron_viaAffineIrreducible`. On `affineScheme`, the `relOfPair`/profile conditions are
`G₀`-orbit-of-difference conditions (`affineScheme_relOfPair_eq_iff`/`orbMk_affine_eq_iff`), so the consumer
runs the Frobenius counting natively without a bespoke affine producer. -/
theorem discrete_of_twoRoundRelationSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (hsep : ∀ u u' : Fin n,
        (∀ (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun ρ b => twoRoundProfileCount_eq S hcell ρ b)

/-! ### §13c — the depth-`k` separation engine on `schemeAdj` (general, for §5.3)

The depth-2 engine (§13b) reads the count profile after a **single** `refineStep` round (the colour
`refineStep χ`). For families where two rounds do not separate, the depth-`k` engine reads the profile after
`k` rounds (the colour `(refineStep)^[k] χ`); `discrete_of_twoRoundProfileSeparates` is the `k = 1` instance.
It is stated for **any** `AssociationScheme`, so it serves the general primitive-floor / §5.3 crux directly —
the *engine* generalizes even though any *bound proof* that discharges it is slice-specific. (For the
affine-cyclic slice depth-2 sufficed empirically — `Probe_RoundsToDiscrete_Cyclotomic` — so this is
build-for-generality, not necessity.) The only extra hypothesis over §13b is `k + 1 ≤ n` (the meaningful
regime: there is "one more round" beyond the `k`-round colour to do the counting; consumers use `k = O(1)`
or `O(log n) ≪ n`). Same peel-and-count proof, with `(refineStep)^[k]` in place of `refineStep^[1]`. -/

/-- **Depth-`k` count separation (the general primitive).** For `w, u` in the same `warmRefine (schemeAdj S)`
cell after individualizing a base set `T`, the **depth-`(k+1)` count profile** coincides: for every
`k`-round colour `c` (`(refineStep)^[k]` of the individualised colouring) and every relation `b`, the number
of `z ≠ w` whose `k`-round colour is `c` and `relOfPair w z = b` equals the corresponding count for `u`.
Mechanism: peel `warmRefine = refineStep^[n]` to `refineStep^[k+1]` (`warmRefine_eq_iter_eq`, needs
`k + 1 ≤ n`), read `signature`-equality at `(refineStep)^[k] χ` (`refineStep_iff`), apply the count bridge
(`signature_eq_card_eq`). Generalises `twoRoundCount_eq_of_warmRefine` (the `k = 1` case). -/
theorem kRoundCount_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (k : Nat) (hk : k + 1 ≤ n) (c : Nat) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k] (individualizedColouring n T)) z = c ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k] (individualizedColouring n T)) z = c ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  -- peel `warmRefine = refineStep^[n]` to `refineStep^[k+1]`, read `signature` at `(refineStep)^[k] χ`
  have h2 : ((refineStep adj P)^[k + 1]) χ w = ((refineStep adj P)^[k + 1]) χ u :=
    warmRefine_eq_iter_eq adj P χ (k + 1) hk h
  rw [Function.iterate_succ_apply'] at h2
  have hsig : signature adj P (((refineStep adj P)^[k]) χ) w
            = signature adj P (((refineStep adj P)^[k]) χ) u :=
    ((refineStep_iff adj P (((refineStep adj P)^[k]) χ) w u).mp h2).2
  have hcard := signature_eq_card_eq adj P (((refineStep adj P)^[k]) χ) hsig (c, b.val, POE.unknown)
  have hpred : ∀ x : Fin n, ∀ z : Fin n,
      (z ≠ x ∧ ((refineStep adj P)^[k]) χ z = c ∧ S.relOfPair x z = b)
        ↔ (z ≠ x ∧ (c, b.val, POE.unknown) = (((refineStep adj P)^[k]) χ z, adj.adj x z, P x z)) := by
    intro x z
    refine and_congr_right (fun _ => ?_)
    have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
    have hPval : P x z = POE.unknown := rfl
    rw [hadjval, hPval, Prod.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hcz, hbz⟩; exact ⟨hcz.symm, by rw [hbz], rfl⟩
    · rintro ⟨hc, hb, -⟩; exact ⟨hc.symm, (Fin.val_injective hb).symm⟩
  rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
  exact hcard

/-- **The depth-`k` discreteness producer (general).** If the depth-`(k+1)` count profile — for every
`k`-round colour `c` and relation `b`, the number of `z` at `k`-round colour `c` with `relOfPair · z = b` —
separates all vertices, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. Generalises
`discrete_of_twoRoundProfileSeparates` (`k = 1`). Composes with `stablyRecoverable_of_discrete` →
`selfDetectsStably_of_discretizes`, so a bounded base `T` with a separating depth-`k` profile closes the seal
on that family. The producer a general primitive-floor / §5.3 bound proof discharges (exhibit such a `T`). -/
theorem discrete_of_kRoundProfileSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (k : Nat) (hk : k + 1 ≤ n)
    (hsep : ∀ u u' : Fin n,
        (∀ (c : Nat) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k] (individualizedColouring n T)) z = c ∧
            S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k] (individualizedColouring n T)) z = c ∧
            S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun c b => kRoundCount_eq_of_warmRefine S hcell k hk c b)

/-- **Iterated Lemma A — the `k`-round colour determines the relation to each base point.** Generalises
`relOfPair_eq_of_refineStep_base` (one round): if `z, z'` share their `k`-round colour `(refineStep)^[k] χ`
(`k ≥ 1`), then `relOfPair t z = relOfPair t z'` for every `t ∈ T`. Proof: a finer colouring refines a
coarser one (`refineStep_iter_le_eq`: `^[k]`-eq ⟹ `^[1]`-eq), then apply the one-round Lemma A. The bridge
that re-groups the depth-`k` counts by the joint relation profile. -/
theorem relOfPair_eq_of_iterateRefineStep_base {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {t : Fin n} (ht : t ∈ T) {k : Nat} (hk : 1 ≤ k) {z z' : Fin n}
    (h : ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z
       = ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z') :
    S.relOfPair t z = S.relOfPair t z' := by
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  have h1 : ((refineStep adj P)^[1]) χ z = ((refineStep adj P)^[1]) χ z' := by
    have hkeq : k = 1 + (k - 1) := by omega
    rw [hkeq] at h
    exact refineStep_iter_le_eq adj P χ 1 (k - 1) h
  rw [Function.iterate_one] at h1
  exact relOfPair_eq_of_refineStep_base S ht h1

/-- **Depth-`k` count, aggregate (countP) form.** The predicate-indexed generalization of
`kRoundCount_eq_of_warmRefine` (and depth-`k` analogue of `twoRoundCountP_eq_of_warmRefine`): for `w, u` in
the same `warmRefine`-from-`T` cell, every count of `z` whose `k`-round colour satisfies a predicate `q` and
whose relation to the base point is `b` agrees. Vehicle for the colour→relation conversion. -/
theorem kRoundCountP_eq_of_warmRefine {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (k : Nat) (hk : k + 1 ≤ n) (q : Nat → Prop) [DecidablePred q] (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        q (((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z) ∧
        S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        q (((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z) ∧
        S.relOfPair u z = b)).card := by
  classical
  set adj := schemeAdj S with hadj
  set P : PMatrix n := fun _ _ => POE.unknown with hP
  set χ := individualizedColouring n T with hχ
  have h2 : ((refineStep adj P)^[k + 1]) χ w = ((refineStep adj P)^[k + 1]) χ u :=
    warmRefine_eq_iter_eq adj P χ (k + 1) hk h
  rw [Function.iterate_succ_apply'] at h2
  have hsig : signature adj P (((refineStep adj P)^[k]) χ) w
            = signature adj P (((refineStep adj P)^[k]) χ) u :=
    ((refineStep_iff adj P (((refineStep adj P)^[k]) χ) w u).mp h2).2
  have hcard := signature_eq_countP_eq adj P (((refineStep adj P)^[k]) χ) hsig
    (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
  have hpred : ∀ x : Fin n, ∀ z : Fin n,
      (z ≠ x ∧ q (((refineStep adj P)^[k]) χ z) ∧ S.relOfPair x z = b)
        ↔ (z ≠ x ∧ (fun tup : Nat × Nat × POE => q tup.1 ∧ tup.2.1 = b.val)
              (((refineStep adj P)^[k]) χ z, adj.adj x z, P x z)) := by
    intro x z
    refine and_congr_right (fun _ => ?_)
    show (q (((refineStep adj P)^[k]) χ z) ∧ S.relOfPair x z = b)
      ↔ (q (((refineStep adj P)^[k]) χ z) ∧ adj.adj x z = b.val)
    have hadjval : adj.adj x z = (S.relOfPair x z).val := rfl
    rw [hadjval]
    exact and_congr_right (fun _ => Fin.ext_iff)
  rw [Finset.filter_congr (fun z _ => hpred w z), Finset.filter_congr (fun z _ => hpred u z)]
  exact hcard

/-- **Depth-`k` count, joint-relation form (the colour→relation conversion).** Re-groups `kRoundCount` by the
joint relation profile `(relOfPair t z)_{t∈T}` instead of the opaque `k`-round colour. Depth-`k` analogue of
`twoRoundProfileCount_eq`, combining `kRoundCountP_eq_of_warmRefine` with the iterated Lemma A
(`relOfPair_eq_of_iterateRefineStep_base`). The relation-indexed depth-`k` count a general separability
argument consumes. -/
theorem kRoundProfileCount_eq {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    {w u : Fin n}
    (h : warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) w
       = warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T) u)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)) :
    (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b)).card
    = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card := by
  classical
  set q : Nat → Prop := fun c => ∃ z₀ : Fin n,
    ((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z₀ = c
      ∧ ∀ t ∈ T, S.relOfPair t z₀ = ρ t with hq_def
  have hq : ∀ z : Fin n,
      q (((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z)
        ↔ ∀ t ∈ T, S.relOfPair t z = ρ t := by
    intro z
    constructor
    · rintro ⟨z₀, hz₀, hprof⟩ t ht
      exact (relOfPair_eq_of_iterateRefineStep_base S ht hk1 hz₀).symm.trans (hprof t ht)
    · intro hprof; exact ⟨z, rfl, hprof⟩
  rw [show (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair w z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ w ∧
          q (((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z)
            ∧ S.relOfPair w z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z]),
    show (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b))
        = (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
          q (((refineStep (schemeAdj S) (fun _ _ => POE.unknown))^[k]) (individualizedColouring n T) z)
            ∧ S.relOfPair u z = b))
      from Finset.filter_congr (fun z _ => by rw [hq z])]
  exact kRoundCountP_eq_of_warmRefine S h k hk q b

/-- **The relation-indexed depth-`k` discreteness producer (general engine).** If the joint relation-profile
counts separate all vertices, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. Depth-`k` analogue of
`discrete_of_twoRoundRelationSeparates` (`k = 1` instance). Stated for any `AssociationScheme`; the producer a
general primitive-floor / §5.3 bound proof discharges (exhibit a bounded `T` with separating depth-`k`
relation profile). -/
theorem discrete_of_kRoundRelationSeparates {n : Nat} (S : AssociationScheme n) {T : Finset (Fin n)}
    (k : Nat) (hk1 : 1 ≤ k) (hk : k + 1 ≤ n)
    (hsep : ∀ u u' : Fin n,
        (∀ (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)),
          (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card
          = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
            (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u' z = b)).card)
        → u = u') :
    Discrete (warmRefine (schemeAdj S) (fun _ _ => POE.unknown) (individualizedColouring n T)) := by
  intro u u' hcell
  exact hsep u u' (fun ρ b => kRoundProfileCount_eq S hcell k hk1 hk ρ b)

/-! ### Step 2.3 — the counting reduction of the seal's open content (`s(C)`)

Steps 2.1 + 2.2 reduced the seal's open content to `RecoversWhileSymmetric S₀` = `CellsAreOrbits (schemeAdj S)`
at every **non-base** prefix `T ⊇ S₀` (warmRefine-cells = `Stab(T)`-orbits, the symmetric phase). This block
performs the **counting reduction** (the `s(C)` route): it produces `CellsAreOrbits` — the *orbits* (non-base)
analogue of `discrete_of_kRoundRelationSeparates`, which produces *singletons* (base) — from the landed
relation-profile counting engine (`kRoundProfileCount_eq`). The resulting open hypothesis
(`RelCountsDetermineOrbit`) is a **concrete, finite counting non-existence**: no two vertices with equal
relation-profile counts (the same bounded-depth invariant `discrete_of_kRoundRelationSeparates` uses — `u`'s
neighbours `z` histogrammed by `(T`-profile of `z`, `u`–`z` relation`)`) lie in different `Stab(T)`-orbits — no
*persistent count-twin across orbits*. This is exactly what the catalogue / affine probes measure
(`SeparatesAtBoundedBase`). It is the sharpest *provable* form of the open `s(C)` conjecture — the GI-adjacent
core (G2-B) stays open, but is now a finite counting statement in the existing machinery, not a warmRefine-fixpoint
claim. **Honest scope:** this is a *reduction*, not a closure; `RelCountsDetermineOrbit` is FALSE for high-`s(C)`
schemes (the block-construction converse is proven dead on the primitive floor — a persistent twin is a
non-congruence amorphic fusion). The count is the fixed bounded-depth invariant of the engine (`k`-independent —
`k` drives only the peeling in `kRoundProfileCount_eq`), so this captures the depth-bounded-recoverable class. -/

/-- **Relation counts determine the `Stab(T)`-orbit (the open `s(C)` hypothesis, counting form).** Two vertices
with equal relation-profile counts (relative to base `T`: the histogram of neighbours `z` by `(T`-profile of `z`,
relation to the vertex`)` — the bounded-depth invariant of `discrete_of_kRoundRelationSeparates`) lie in the same
`Stab(T)`-orbit (`OrbitPartition (schemeAdj S) … T`). The orbit-analogue of that engine's separation hypothesis
(`= u'` weakened to "same orbit", for the non-base symmetric phase). For a primitive small scheme the conjecture
is that this holds from a base + `O(1)` set; it is genuinely open (G2-B). -/
def RelCountsDetermineOrbit {n : Nat} (S : AssociationScheme n) (T : Finset (Fin n)) : Prop :=
  ∀ u u' : Fin n,
    (∀ (ρ : Fin n → Fin (S.rank + 1)) (b : Fin (S.rank + 1)),
      (Finset.univ.filter (fun z : Fin n => z ≠ u ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u z = b)).card
      = (Finset.univ.filter (fun z : Fin n => z ≠ u' ∧
        (∀ t ∈ T, S.relOfPair t z = ρ t) ∧ S.relOfPair u' z = b)).card)
    → OrbitPartition (schemeAdj S) (fun _ _ => POE.unknown) T u u'

/-- **`CellsAreOrbits` from the counting condition (step 2.3 — the counting producer).** The orbits (non-base)
analogue of `discrete_of_kRoundRelationSeparates`: if relation counts determine the `Stab(T)`-orbit
(`RelCountsDetermineOrbit`), then warmRefine-from-`T` cells coincide with `Stab(T)`-orbits. Proof mirrors the
discreteness producer verbatim — a same-cell pair shares its relation-count profile (`kRoundProfileCount_eq` at
`k = 1`), and the hypothesis lifts that to an orbit relation. Axiom-clean. -/
theorem cellsAreOrbits_of_relCountsDetermineOrbit {n : Nat} (S : AssociationScheme n)
    {T : Finset (Fin n)} (hn : 2 ≤ n) (hdet : RelCountsDetermineOrbit S T) :
    CellsAreOrbits (schemeAdj S) (fun _ _ => POE.unknown) T := by
  intro u u' hcell
  exact hdet u u' (fun ρ b => kRoundProfileCount_eq S hcell 1 le_rfl (by omega) ρ b)

/-- **`RecoversWhileSymmetric` from per-prefix orbit determination (step 2.3).** The seal's symmetric-phase
recovery from `S₀` reduces to: at every non-base prefix `T ⊇ S₀`, relation counts determine the `Stab(T)`-orbit.
Each prefix's `CellsAreOrbits` is produced by `cellsAreOrbits_of_relCountsDetermineOrbit`. Axiom-clean. -/
theorem recoversWhileSymmetric_of_relCountsDetermineOrbit {n : Nat} (S : SchurianScheme n) (hn : 2 ≤ n)
    {S₀ : Finset (Fin n)}
    (h : ∀ T : Finset (Fin n), S₀ ⊆ T →
        ¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T →
        RelCountsDetermineOrbit S.toAssociationScheme T) :
    RecoversWhileSymmetric (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) S₀ := by
  intro T hsub hnb
  exact cellsAreOrbits_of_relCountsDetermineOrbit S.toAssociationScheme hn (h T hsub hnb)

/-- **Self-detection reduced to the counting condition (step 2.3 — the seal-facing reduction).**
`SelfDetectsWhileSymmetric` from "primitive small ⟹ ∃ bounded `S₀`, every non-base `T ⊇ S₀` has its
`Stab(T)`-orbits determined by relation counts". This is the **entire open content of the seal** as a concrete,
finite counting non-existence — the sharpest provable form of the `s(C)` conjecture (`base(G)` banked by step 2.1
into `bound`; the layer reduction by step 2.2; the counting engine here). The GI-adjacent core (whether the
hypothesis holds for all primitive small schemes) stays open. Axiom-clean. -/
theorem selfDetectsWhileSymmetric_of_relCountsDetermineOrbit {n : Nat} (S : SchurianScheme n) (hn : 2 ≤ n)
    {IsLarge : Nat → Prop} {bound : Nat}
    (h : S.toAssociationScheme.IsPrimitive ∧ ¬ IsLargeSchemeViaAut IsLarge n S →
      ∃ S₀ : Finset (Fin n), S₀.card ≤ bound ∧
        ∀ T : Finset (Fin n), S₀ ⊆ T →
          ¬ IsBase (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) T →
          RelCountsDetermineOrbit S.toAssociationScheme T) :
    SelfDetectsWhileSymmetric S IsLarge bound := by
  intro hps
  obtain ⟨S₀, hcard, hrec⟩ := h hps
  exact ⟨S₀, hcard, recoversWhileSymmetric_of_relCountsDetermineOrbit S hn hrec⟩

/-! ### Phase 2, M0.3 — the affine instance `V ⋊ G₀` over `F_p^d`

The concrete beachhead family: the orbital scheme of the affine group `V ⋊ G₀` acting on `V = F_p^d`,
built by instantiating the general `orbitalScheme` (M0) at the subgroup of `Perm (Fin (p^d))` generated
by the affine permutations `x ↦ g₀ x + t` (`g₀ ∈ G₀`, `t ∈ V`), transported along `V ≃ Fin (p^d)`.

**Generalization note (the reusable shape).** The construction uses only: a *regular abelian* group of
translations (giving transitivity) and a point-stabilizer `G₀` *closed under negation* (giving the
symmetric/generous-transitivity hypothesis — `LinearEquiv.neg ∈ G₀`). Nothing here is special to
`F_p^d` beyond `V` being a finite module; the same shape models any **translation scheme** (`T ⋊ G₀`,
`T` regular abelian — the Schur-ring setting of M2). The linear structure of `V` only enters later, at
M1 (block ⟺ `G₀`-invariant subspace) and M2 (irreducible `G₀` ⟹ recovery). -/

section AffineScheme

variable {p d : ℕ} [Fact p.Prime]

/-- `card (F_p^d) = p^d`. -/
private theorem affV_card : Fintype.card (Fin d → ZMod p) = p ^ d := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The transport `F_p^d ≃ Fin (p^d)` (the scheme lives on `Fin (p^d)`). -/
noncomputable def affineE : (Fin d → ZMod p) ≃ Fin (p ^ d) :=
  Fintype.equivFinOfCardEq affV_card

/-- The affine permutation `x ↦ g₀ x + t` of `V = F_p^d`. -/
def affineEquivV (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (t : Fin d → ZMod p) :
    Equiv.Perm (Fin d → ZMod p) where
  toFun := fun x => g₀ x + t
  invFun := fun y => g₀.symm (y - t)
  left_inv := fun x => by simp
  right_inv := fun y => by simp

/-- The affine permutation transported to `Perm (Fin (p^d))`. -/
noncomputable def affinePermFin (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) : Equiv.Perm (Fin (p ^ d)) :=
  affineE.permCongr (affineEquivV g₀ t)

@[simp] private theorem affinePermFin_apply (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) (i : Fin (p ^ d)) :
    affinePermFin g₀ t i = affineE (g₀ (affineE.symm i) + t) := by
  simp only [affinePermFin, Equiv.permCongr_apply, affineEquivV, Equiv.coe_fn_mk]

/-- The identity is the trivial affine perm. -/
theorem affinePermFin_one :
    affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (0 : Fin d → ZMod p) = 1 := by
  ext i; simp [affinePermFin_apply, LinearEquiv.coe_one]

/-- **Affine perms compose to affine perms** (`x ↦ g₀x+t` ∘ `x ↦ h₀x+s` = `x ↦ (g₀h₀)x + (g₀s+t)`). -/
theorem affinePermFin_mul (g₀ h₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t s : Fin d → ZMod p) :
    affinePermFin g₀ t * affinePermFin h₀ s = affinePermFin (g₀ * h₀) (g₀ s + t) := by
  ext i
  simp only [Equiv.Perm.mul_apply, affinePermFin_apply, Equiv.symm_apply_apply,
    LinearEquiv.mul_apply, map_add]
  congr 1; abel_nf

/-- The inverse of an affine perm is affine. -/
theorem affinePermFin_inv (g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (t : Fin d → ZMod p) :
    (affinePermFin g₀ t)⁻¹ = affinePermFin g₀⁻¹ (-(g₀⁻¹ t)) := by
  have h : affinePermFin g₀⁻¹ (-(g₀⁻¹ t)) * affinePermFin g₀ t = 1 := by
    rw [affinePermFin_mul, inv_mul_cancel, add_neg_cancel, affinePermFin_one]
  exact inv_eq_of_mul_eq_one_left h

variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- The affine permutations whose linear part lies in `G₀` — the generating set of `V ⋊ G₀`. -/
def affineGenSet : Set (Equiv.Perm (Fin (p ^ d))) :=
  { σ | ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p), g₀ ∈ G₀ ∧ ∃ t, σ = affinePermFin g₀ t }

/-- **The affine group `V ⋊ G₀`** as a subgroup of `Perm (Fin (p^d))`. Defined as the carrier set of
affine perms (closed under product/inverse/identity by `affinePermFin_mul`/`_inv`/`_one`), so membership
is *transparently* "is an affine perm with linear part in `G₀`" — what the orbital characterization (M1.0b)
needs. -/
noncomputable def affineG : Subgroup (Equiv.Perm (Fin (p ^ d))) where
  carrier := affineGenSet G₀
  mul_mem' := by
    rintro a b ⟨g₀, hg₀, t, rfl⟩ ⟨h₀, hh₀, s, rfl⟩
    exact ⟨g₀ * h₀, mul_mem hg₀ hh₀, g₀ s + t, affinePermFin_mul g₀ h₀ t s⟩
  one_mem' := ⟨1, one_mem _, 0, affinePermFin_one.symm⟩
  inv_mem' := by
    rintro a ⟨g₀, hg₀, t, rfl⟩
    exact ⟨g₀⁻¹, inv_mem hg₀, -(g₀⁻¹ t), affinePermFin_inv g₀ t⟩

/-- **Membership in `affineG` is being an affine perm with linear part in `G₀`** (the transparent carrier). -/
theorem mem_affineG_iff {σ : Equiv.Perm (Fin (p ^ d))} :
    σ ∈ affineG G₀ ↔ ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p),
      g₀ ∈ G₀ ∧ ∃ t, σ = affinePermFin g₀ t :=
  Iff.rfl

/-- A translation lies in `affineG` (linear part `1 ∈ G₀`). -/
private theorem affinePermFin_one_mem (t : Fin d → ZMod p) :
    affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) t ∈ affineG G₀ :=
  ⟨1, one_mem _, t, rfl⟩

/-- **Transitivity** — translations act transitively on `F_p^d`. -/
theorem affineG_isPretransitive : MulAction.IsPretransitive (affineG G₀) (Fin (p ^ d)) := by
  refine ⟨fun i j => ?_⟩
  refine ⟨⟨affinePermFin 1 (affineE.symm j - affineE.symm i), affinePermFin_one_mem G₀ _⟩, ?_⟩
  show affinePermFin (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
      (affineE.symm j - affineE.symm i) i = j
  rw [affinePermFin_apply]
  have : (1 : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (affineE.symm i)
      + (affineE.symm j - affineE.symm i) = affineE.symm j := by
    rw [LinearEquiv.coe_one, id_eq]; abel
  rw [this, Equiv.apply_symm_apply]

/-- **Generous transitivity** — with `-1 ∈ G₀`, the orbital of `(x,y)` equals that of `(y,x)` (the
affine map `u ↦ -u + (x+y)` swaps them), so the orbital scheme is symmetric. -/
theorem affineG_generous (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (x y : Fin (p ^ d)) :
    (orbMk x y : Orbital (affineG G₀)) = orbMk y x := by
  rw [orbMk_eq_iff]
  refine ⟨⟨affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y),
      ⟨_, hneg, _, rfl⟩⟩, ?_, ?_⟩
  · show affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y) y = x
    rw [affinePermFin_apply]
    have : (LinearEquiv.neg (ZMod p)) (affineE.symm y) + (affineE.symm x + affineE.symm y)
        = affineE.symm x := by
      simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq]; abel
    rw [this, Equiv.apply_symm_apply]
  · show affinePermFin (LinearEquiv.neg (ZMod p)) (affineE.symm x + affineE.symm y) x = y
    rw [affinePermFin_apply]
    have : (LinearEquiv.neg (ZMod p)) (affineE.symm x) + (affineE.symm x + affineE.symm y)
        = affineE.symm y := by
      simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq]; abel
    rw [this, Equiv.apply_symm_apply]

/-- **The affine scheme `V ⋊ G₀` over `F_p^d`** (Phase 2, M0.3) — the concrete beachhead family.
The orbital scheme of the affine group acting on `Fin (p^d)`: relations are the `G₀`-orbits on
differences, `relOfPair x y` = the orbit of `y − x`. A `SchurianScheme (p^d)`, pluggable into
`SelfDetectsStably` and the seal. The hypothesis `-1 ∈ G₀` makes the scheme symmetric (generous
transitivity). **Next:** M1 (`IsPrimitive` ⟺ `G₀` irreducible), M2 (irreducible ⟹ recovers). -/
noncomputable def affineScheme (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : SchurianScheme (p ^ d) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Nonempty (Fin (p ^ d)) := ⟨⟨0, Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne p))⟩⟩
  orbitalScheme (affineG G₀) (affineG_isPretransitive G₀) (affineG_generous G₀ hneg)

/-! #### M1.0b — the orbital ⟺ `G₀`-orbit-of-difference characterization (the Schur-ring statement)

This is the affine scheme's defining structure made precise: **two pairs lie in the same orbital iff their
difference vectors are `G₀`-related**. It is exactly the "translation scheme = orbit Schur ring `A(G₀)`"
identity — relations of `affineScheme` ↔ `G₀`-orbits on `V` (differences). It is the bridge M1's
block ⟺ invariant-subspace argument runs on. -/

/-- **Orbital ⟺ `G₀`-orbit of the difference.** `(x,y)` and `(x',y')` are in the same orbital of
`affineG G₀` iff some `g₀ ∈ G₀` carries the difference `e⁻¹y' − e⁻¹x'` to `e⁻¹y − e⁻¹x`. -/
theorem orbMk_affine_eq_iff {x y x' y' : Fin (p ^ d)} :
    (orbMk x y : Orbital (affineG G₀)) = orbMk x' y' ↔
      ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p), g₀ ∈ G₀ ∧
        g₀ (affineE.symm y' - affineE.symm x') = affineE.symm y - affineE.symm x := by
  rw [orbMk_eq_iff]
  constructor
  · rintro ⟨a, hax, hay⟩
    obtain ⟨g₀, hg₀, t, ha⟩ := a.2
    refine ⟨g₀, hg₀, ?_⟩
    rw [ha, affinePermFin_apply] at hax hay
    have hx : g₀ (affineE.symm x') + t = affineE.symm x := by
      have := congrArg affineE.symm hax; rwa [Equiv.symm_apply_apply] at this
    have hy : g₀ (affineE.symm y') + t = affineE.symm y := by
      have := congrArg affineE.symm hay; rwa [Equiv.symm_apply_apply] at this
    rw [map_sub, ← hx, ← hy]; abel
  · rintro ⟨g₀, hg₀, hg⟩
    refine ⟨⟨affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')), ⟨g₀, hg₀, _, rfl⟩⟩, ?_, ?_⟩
    · show affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')) x' = x
      rw [affinePermFin_apply]
      have : g₀ (affineE.symm x') + (affineE.symm x - g₀ (affineE.symm x')) = affineE.symm x := by abel
      rw [this, Equiv.apply_symm_apply]
    · show affinePermFin g₀ (affineE.symm x - g₀ (affineE.symm x')) y' = y
      rw [affinePermFin_apply]
      have hg2 : g₀ (affineE.symm y') - g₀ (affineE.symm x') = affineE.symm y - affineE.symm x := by
        rw [← map_sub]; exact hg
      have : g₀ (affineE.symm y') + (affineE.symm x - g₀ (affineE.symm x')) = affineE.symm y := by
        rw [show g₀ (affineE.symm y') + (affineE.symm x - g₀ (affineE.symm x'))
              = (g₀ (affineE.symm y') - g₀ (affineE.symm x')) + affineE.symm x from by abel, hg2]
        abel
      rw [this, Equiv.apply_symm_apply]

/-! ### Phase 2, M1.1/M1.2 — primitive ⟹ `G₀` irreducible (the block ⟺ invariant-subspace bridge)

The seal's cascade branch hands you `IsPrimitive (affineScheme)`; M2 (recovery) needs `G₀` irreducible.
This block is the bridge — and it is the **concrete rehearsal of the §5.3 general crux template** ("a block
is a sub-structure; primitivity forbids it"): here the *block* is a `ClosedSubset I`, the *sub-structure* is
a `G₀`-invariant `Submodule`, and the proof builds one from the other. The general crux swaps `Submodule` ↔
fusion / `ClosedSubset` and "invariant subspace" ↔ "block system"; do the affine one first. The direction
that matters is `¬irreducible → ¬IsPrimitive` (contrapositive of what M3 consumes). -/

/-- `Fin (p^d)` is nonempty (`p^d ≥ 1` since `p` is prime). Needed for the orbital indexing/diagonal facts
used below outside the `affineScheme` definition. -/
private instance instNonemptyAffV : Nonempty (Fin (p ^ d)) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  ⟨⟨0, Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne p))⟩⟩

/-- **M1.1a (rel characterization).** A pair `(x,y)` lies in relation `i` of `affineScheme` iff its orbital
is the one indexed by `i`. Unfolds the orbital-scheme `rel` field (a `decide` of orbital equality). -/
theorem affineScheme_rel_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {i : Fin ((affineScheme G₀ hneg).rank + 1)} {x y : Fin (p ^ d)} :
    (affineScheme G₀ hneg).rel i x y = true ↔ orbitalIdx (affineG G₀) i = orbMk x y := by
  simp only [affineScheme, orbitalScheme, orbitalAssocScheme, decide_eq_true_eq]

/-- `relOfPair` for `affineScheme` is the index of the pair's orbital. -/
theorem affineScheme_relOfPair (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (x y : Fin (p ^ d)) :
    (affineScheme G₀ hneg).relOfPair x y = (orbitalIdx (affineG G₀)).symm (orbMk x y) := by
  have h : (affineScheme G₀ hneg).rel ((orbitalIdx (affineG G₀)).symm (orbMk x y)) x y = true := by
    rw [affineScheme_rel_iff]; exact Equiv.apply_symm_apply _ _
  exact ((affineScheme G₀ hneg).relOfPair_unique h).symm

/-- **M1.1a (relOfPair characterization).** Two pairs have the same relation iff they have the same orbital.
The `relOfPair`-level form of `orbMk_affine_eq_iff`, used to transport difference-membership across a
relation. -/
theorem affineScheme_relOfPair_eq_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {x y x' y' : Fin (p ^ d)} :
    (affineScheme G₀ hneg).relOfPair x y = (affineScheme G₀ hneg).relOfPair x' y' ↔
      (orbMk x y : Orbital (affineG G₀)) = orbMk x' y' := by
  rw [affineScheme_relOfPair, affineScheme_relOfPair]
  exact (orbitalIdx (affineG G₀)).symm.injective.eq_iff

/-- **M1.1b — `G₀` acts irreducibly** (self-contained, no `IsSimpleModule`): the only `G₀`-invariant
subspaces are `⊥` and `⊤`. The hypothesis M2's recovery argument consumes; primitivity of `affineScheme`
delivers it (M1.2). -/
def G₀Irreducible : Prop :=
  ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
    (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

/-- The **difference of a relation**: the difference `y₀ − x₀` of `i`'s chosen representative pair
`(x₀,y₀)`. Well-defined as a `G₀`-orbit (different representatives give `G₀`-translates, so membership in a
`G₀`-invariant subspace is rep-independent — `affineRelDiff_mem_iff`). -/
noncomputable def affineRelDiff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (i : Fin ((affineScheme G₀ hneg).rank + 1)) : Fin d → ZMod p :=
  affineE.symm (orbitalIdx (affineG G₀) i).out.2 - affineE.symm (orbitalIdx (affineG G₀) i).out.1

/-- The diagonal relation `R_0` has difference `0` (its representative pair is `(v,v)`). -/
theorem affineRelDiff_zero (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) :
    affineRelDiff G₀ hneg 0 = 0 := by
  -- The representative pair of the diagonal relation `R₀` is `(v, v)`, so its difference is `0`.
  -- Work at the diagonal index `(0 : Fin ((affineScheme ...).rank + 1))` throughout (`rel_zero_iff_eq`
  -- lives at this rank type, avoiding the `orbitalRank` vs `affineScheme.rank` ascription mismatch).
  have hr : (affineScheme G₀ hneg).rel 0
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1))).out.1
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1))).out.2 = true := by
    rw [affineScheme_rel_iff]
    exact (orbMk_out (affineG G₀)
      (orbitalIdx (affineG G₀) (0 : Fin ((affineScheme G₀ hneg).rank + 1)))).symm
  have heq := ((affineScheme G₀ hneg).rel_zero_iff_eq _ _).mp hr
  unfold affineRelDiff
  rw [← heq, sub_self]

/-- **Difference-membership is constant along a relation.** If `(x,y) ∈ R_i` then `affineRelDiff i ∈ W`
iff `(e⁻¹y − e⁻¹x) ∈ W`, for any `G₀`-invariant `W`. This is where invariance does the work: any two pairs
of `R_i` differ by a `G₀`-translate (`orbMk_affine_eq_iff`), so a `G₀`-invariant subspace cannot tell them
apart. The key well-definedness lemma for the `ClosedSubset` construction. -/
theorem affineRelDiff_mem_iff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {W : Submodule (ZMod p) (Fin d → ZMod p)}
    (hWinv : ∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W)
    {i : Fin ((affineScheme G₀ hneg).rank + 1)} {x y : Fin (p ^ d)}
    (hrel : (affineScheme G₀ hneg).rel i x y = true) :
    affineRelDiff G₀ hneg i ∈ W ↔ affineE.symm y - affineE.symm x ∈ W := by
  have hidx : orbitalIdx (affineG G₀) i = orbMk x y := (affineScheme_rel_iff G₀ hneg).mp hrel
  have hout : (orbMk (orbitalIdx (affineG G₀) i).out.1 (orbitalIdx (affineG G₀) i).out.2
      : Orbital (affineG G₀)) = orbMk x y := by rw [orbMk_out, hidx]
  obtain ⟨g, hg₀, hgeq⟩ := (orbMk_affine_eq_iff G₀).mp hout
  -- `hgeq : g (e⁻¹y − e⁻¹x) = e⁻¹ out.2 − e⁻¹ out.1`, which is `affineRelDiff i` by definition.
  have hgeq' : g (affineE.symm y - affineE.symm x) = affineRelDiff G₀ hneg i := hgeq
  have hgg : (g⁻¹ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (affineRelDiff G₀ hneg i)
      = affineE.symm y - affineE.symm x := by
    rw [← hgeq', ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq]
  constructor
  · intro hmem
    rw [← hgg]
    exact hWinv _ (inv_mem hg₀) _ hmem
  · intro hmem
    rw [← hgeq']
    exact hWinv _ hg₀ _ hmem

/-- **M1.2 — primitive ⟹ `G₀` irreducible.** The bridge M3 consumes, by contrapositive: from a proper
`G₀`-invariant subspace `W`, build the closed subset `I := {i | affineRelDiff i ∈ W}` — a genuine block
system, contradicting primitivity. `0 ∈ I` (diagonal diff `0 ∈ W`); closure follows because a composable
triple's differences add (`exists_composable_of_intersectionNumber` + `W.add_mem`); `I ≠ {0}` from a
nonzero `w ∈ W`; `I ≠ univ` from a `v ∉ W`. **This is the §5.3 template instantiated** (`Submodule` for the
sub-structure, `ClosedSubset` for the block). -/
theorem isPrimitive_affineScheme_imp_irreducible (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (hprim : (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive) :
    G₀Irreducible G₀ := by
  intro W hWinv
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hWT⟩ := hcon
  classical
  set I : Finset (Fin ((affineScheme G₀ hneg).rank + 1)) :=
    Finset.univ.filter (fun i => affineRelDiff G₀ hneg i ∈ W) with hIdef
  have hmemI : ∀ i, i ∈ I ↔ affineRelDiff G₀ hneg i ∈ W := by
    intro i; rw [hIdef, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
  -- `I` is a closed subset (a block system).
  have hcl : (affineScheme G₀ hneg).toAssociationScheme.ClosedSubset I := by
    refine ⟨?_, ?_⟩
    · rw [hmemI, affineRelDiff_zero]; exact W.zero_mem
    · intro i hi j hj k hk
      have hkne : ∃ x z, (affineScheme G₀ hneg).rel k x z = true :=
        ⟨_, _, (affineScheme_rel_iff G₀ hneg).mpr
          (orbMk_out (affineG G₀) (orbitalIdx (affineG G₀) k)).symm⟩
      obtain ⟨x, y, z, hxy, hyz, hxz⟩ :=
        (affineScheme G₀ hneg).toAssociationScheme.exists_composable_of_intersectionNumber hkne hk
      have hi' : affineE.symm y - affineE.symm x ∈ W :=
        (affineRelDiff_mem_iff G₀ hneg hWinv hxy).mp ((hmemI i).mp hi)
      have hj' : affineE.symm z - affineE.symm y ∈ W :=
        (affineRelDiff_mem_iff G₀ hneg hWinv hyz).mp ((hmemI j).mp hj)
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hxz,
        show affineE.symm z - affineE.symm x
          = (affineE.symm y - affineE.symm x) + (affineE.symm z - affineE.symm y) from by abel]
      exact W.add_mem hi' hj'
  -- `I ≠ {0}`: a nonzero `w ∈ W` gives a nondiagonal relation in `I`.
  have hIne0 : I ≠ {0} := by
    obtain ⟨w, hwW, hwne⟩ := (Submodule.ne_bot_iff W).mp hW0
    have hrel : (affineScheme G₀ hneg).rel
        ((affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w)) (affineE 0) (affineE w) = true :=
      (affineScheme G₀ hneg).rel_relOfPair _ _
    have hdiff : affineE.symm (affineE w) - affineE.symm (affineE (0 : Fin d → ZMod p)) = w := by
      simp only [Equiv.symm_apply_apply, sub_zero]
    have hi₀I : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w) ∈ I := by
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hrel, hdiff]; exact hwW
    have hi₀ne : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w) ≠ 0 := by
      intro hzero
      rw [(affineScheme G₀ hneg).relOfPair_eq_zero_iff] at hzero
      exact hwne (affineE.injective hzero).symm
    intro hI0
    rw [hI0, Finset.mem_singleton] at hi₀I
    exact hi₀ne hi₀I
  -- `I ≠ univ`: a `v ∉ W` gives a relation outside `I`.
  have hInu : I ≠ Finset.univ := by
    have hexv : ∃ v, v ∉ W := by
      by_contra h
      push Not at h
      exact hWT (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hvnotW⟩ := hexv
    have hrel : (affineScheme G₀ hneg).rel
        ((affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v)) (affineE 0) (affineE v) = true :=
      (affineScheme G₀ hneg).rel_relOfPair _ _
    have hdiff : affineE.symm (affineE v) - affineE.symm (affineE (0 : Fin d → ZMod p)) = v := by
      simp only [Equiv.symm_apply_apply, sub_zero]
    have hi₁notI : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∉ I := by
      rw [hmemI, affineRelDiff_mem_iff G₀ hneg hWinv hrel, hdiff]; exact hvnotW
    intro hIu
    rw [hIu] at hi₁notI
    exact hi₁notI (Finset.mem_univ _)
  rcases hprim I hcl with h | h
  · exact hIne0 h
  · exact hInu h

/-- **M2-B, affine depth-1 discreteness (the `G₀`-orbit-of-difference form).** Specializes
`discrete_of_jointProfileSeparates` to `affineScheme`: if individualizing `T` makes the `G₀`-orbits of the
differences `(u − t)_{t ∈ T}` jointly separate `V`, then `warmRefine` from `T` is `Discrete`. Concretely the
**depth-1 affine separability** condition — `∀ u u'`, if for every `t ∈ T` some `g₀ ∈ G₀` carries
`e⁻¹u′ − e⁻¹t` to `e⁻¹u − e⁻¹t` (same `G₀`-orbit of difference), then `u = u'`. This is the finite,
checkable target the affine probe measures at depth 1; combined with `stablyRecoverable_of_discrete` +
`selfDetectsStably_of_discretizes` it discharges the seal for any depth-1-separating primitive small affine
residual. The open remainder (cyclotomic / `s(C) ≥ 2`) is the *iterated* version of this same separation. -/
theorem discrete_affineScheme_of_jointSeparates (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {T : Finset (Fin (p ^ d))}
    (hsep : ∀ u u' : Fin (p ^ d),
      (∀ t ∈ T, ∃ g₀ ∈ G₀,
        g₀ (affineE.symm u' - affineE.symm t) = affineE.symm u - affineE.symm t) → u = u') :
    Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
      (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)) := by
  apply discrete_of_jointProfileSeparates
  intro u u' hjp
  refine hsep u u' (fun t ht => ?_)
  exact (orbMk_affine_eq_iff G₀).mp ((affineScheme_relOfPair_eq_iff G₀ hneg).mp (hjp t ht))

/-- **F2a — translation-invariance of the affine relation (the load-bearing depth-2 → coset bridge).**
`relOfPair t z` depends only on the difference `e⁻¹z − e⁻¹t`: it equals the relation of that difference
measured from the origin (`g₀ = 1` carries one orbital representative to the other). So the depth-2 profile
`(relOfPair t z)_{t ∈ T}` is exactly the **multi-coset membership** `(e⁻¹z − e⁻¹t ∈ C_·)_{t ∈ T}` — the
object the Frobenius `s(C)` count (F2b, self-detection-plan §11.8) lives in. -/
theorem affineScheme_relOfPair_translation (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (t z : Fin (p ^ d)) :
    (affineScheme G₀ hneg).relOfPair t z
      = (affineScheme G₀ hneg).relOfPair (affineE 0)
          (affineE (affineE.symm z - affineE.symm t)) := by
  rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff]
  refine ⟨1, one_mem _, ?_⟩
  simp only [Equiv.symm_apply_apply, sub_zero, LinearEquiv.coe_one, id_eq]

/-- **F2a — the depth-2 affine discreteness producer, difference (coset) form.** Specializes the general
depth-2 engine `discrete_of_twoRoundRelationSeparates` to `affineScheme`, with the relation conditions
rewritten — via `affineScheme_relOfPair_translation` — as **difference-relation** conditions: the depth-2
profile of `z` is `(relation of e⁻¹z − e⁻¹t from the origin)_{t ∈ T}` together with `(relation of
e⁻¹z − e⁻¹u)`. So if, for every difference-relation profile `ρ` and tail relation `b`, the counts of such
`z` agree between `u` and `u'` only when `u = u'`, then `warmRefine` from `T` is `Discrete`. This is the
**multi-coset-intersection injectivity** the Frobenius `s(C)` bound (F2b) discharges — the clean affine target
the probe `Probe_RoundsToDiscrete_Cyclotomic` measures. -/
theorem discrete_affineScheme_of_twoRoundDiffSeparates (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {T : Finset (Fin (p ^ d))}
    (hsep : ∀ u u' : Fin (p ^ d),
      (∀ (ρ : Fin (p ^ d) → Fin ((affineScheme G₀ hneg).rank + 1))
          (b : Fin ((affineScheme G₀ hneg).rank + 1)),
        (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u)) = b)).card
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u')) = b)).card) → u = u') :
    Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
      (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)) := by
  apply discrete_of_twoRoundRelationSeparates
  intro u u' hcounts
  refine hsep u u' (fun ρ b => ?_)
  have key : ∀ w : Fin (p ^ d),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair t z = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair w z = b))
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
          (∀ t ∈ T, (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme G₀ hneg).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm w)) = b)) := by
    intro w
    apply Finset.filter_congr
    intro z _
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · exact forall₂_congr fun t _ => by rw [affineScheme_relOfPair_translation G₀ hneg t z]
    · rw [affineScheme_relOfPair_translation G₀ hneg w z]
  rw [← key u, ← key u']
  exact hcounts ρ b

/-- **E3 — the seal reduced to the affine irreducible-discreteness bound (the affine-cyclic slice).**
Specializes the fused seal `reachesRigidOrCameron_viaFusedSeal` to the affine model `affineScheme G₀ hneg`,
discharging its self-detection input through `selfDetectsStably_of_discretizes` and converting the seal's
`IsPrimitive` antecedent into `G₀Irreducible` via **M1.2** (`isPrimitive_affineScheme_imp_irreducible`). So
the affine slice's seal is reduced to a **single open hypothesis** `hbound`: *irreducible `G₀` (and small) ⟹
a bounded individualization warm-refines to a discrete colouring* — exactly the cyclotomic / Schur-ring
separability target (E2.4: the Frobenius/Galois `s(C)` bound for cyclic irreducible `G₀`). The "cyclotomic
family" needs **no new model**: it is `affineScheme` with cyclic `G₀`, and `hbound` is the only open content.

**⚠️ CONDITIONAL — not the closed seal.** It still carries `hClassify` (G3), `hImprim` (landed/earned,
tower-reducible to the primitive floor), and the **open** `hbound`. Closing `hbound` — even for cyclic `G₀`
— is uncited open `s(C)` mathematics (seal-handoff §6 insight 2). The engine that *discharges* `hbound` is
§13b (`twoRoundCount_eq_of_warmRefine` / `discrete_of_twoRoundProfileSeparates`) fed by the multi-base
Frobenius separation (the `O(d)` Γ-breaking base individualizing into a discrete colouring). Do **not** read
this as "the seal is closed for the affine/cyclotomic family." -/
theorem reachesRigidOrCameron_viaAffineIrreducible {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (hne : ∀ i : Fin ((affineScheme G₀ hneg).rank + 1),
        ∃ v w, (affineScheme G₀ hneg).rel i v w = true)
    (hrank : 2 ≤ (affineScheme G₀ hneg).rank)
    (hbound : G₀Irreducible G₀ ∧ ¬ IsLargeSchemeViaAut IsLarge (p ^ d) (affineScheme G₀ hneg) →
        ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
          Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
            (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T)))
    (hImprim : ¬ (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
          ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg)) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
        ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme G₀ hneg) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme G₀ hneg) := by
  refine reachesRigidOrCameron_viaFusedSeal hClassify (affineScheme G₀ hneg) hne hrank ?_ hImprim
  apply selfDetectsStably_of_discretizes
  rintro ⟨hprim, hsmall⟩
  exact hbound ⟨isPrimitive_affineScheme_imp_irreducible G₀ hneg hprim, hsmall⟩

/-! ### §S-stage3 — the affine forced-triangle criterion (the δ′ family target, difference-coordinates)

Stage 3 of the general-CC build, δ′ branch (`docs/chain-descent-general-cc-separability.md` §5 Stage 3): the
open content is `∀ v, DominatorReachable S T v` for the residue family. This block translates the abstract
dominator step (`DominatorReachable.step`'s `intersectionNumber … = 1` premise) into the affine model's
**`G₀`-orbit uniqueness on differences** — the form the family combinatorics (and the probe-gate
`Probe_CatchUpGate_BasesAndDominators`) actually reason in. It is the dominator-engine analogue of
`affineScheme_relOfPair_translation` / `discrete_affineScheme_of_jointSeparates`: the forced-triangle filter
is exhibited as the singleton `{γ}`, so the `= 1` premise reduces to "the only point sharing `γ`'s
orbit-relations to `α` and `β` is `γ`". -/

/-- **The affine forced-triangle criterion.** For `affineScheme G₀`, the dominator intersection number
`c^{r(α,β)}_{r(α,γ),r(γ,β)}` equals `1` exactly when `γ` is the **unique** point `u` sharing `γ`'s
`G₀`-orbit-of-difference both to `α` (`u − α ∼ γ − α`) and from `β` (`β − u ∼ β − γ`). Proof: the
forced-triangle filter `{u : r(α,u) = r(α,γ) ∧ r(u,β) = r(γ,β)}` is exactly `{γ}` — `γ` lies in it
(`rel_relOfPair`), and the uniqueness hypothesis collapses it (each membership clause unfolds to a
`G₀`-orbit-of-difference equation via `affineScheme_rel_iff` + `orbMk_affine_eq_iff`). The criterion that
feeds `DominatorReachable.step` from affine data, with no scheme-level intersection-number bookkeeping. -/
theorem affineScheme_interNum_eq_one_of_unique (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {α β γ : Fin (p ^ d)}
    (huniq : ∀ u : Fin (p ^ d),
      (∃ g₀ ∈ G₀, g₀ (affineE.symm u - affineE.symm α) = affineE.symm γ - affineE.symm α) →
      (∃ g₀ ∈ G₀, g₀ (affineE.symm β - affineE.symm u) = affineE.symm β - affineE.symm γ) →
      u = γ) :
    (affineScheme G₀ hneg).intersectionNumber
        ((affineScheme G₀ hneg).relOfPair α γ)
        ((affineScheme G₀ hneg).relOfPair γ β)
        ((affineScheme G₀ hneg).relOfPair α β) = 1 := by
  classical
  have hidx : ∀ x y : Fin (p ^ d),
      orbitalIdx (affineG G₀) ((affineScheme G₀ hneg).relOfPair x y) = orbMk x y := by
    intro x y; rw [affineScheme_relOfPair G₀ hneg]; exact Equiv.apply_symm_apply _ _
  have hmem : ∀ u : Fin (p ^ d),
      ((affineScheme G₀ hneg).rel ((affineScheme G₀ hneg).relOfPair α γ) α u = true ∧
       (affineScheme G₀ hneg).rel ((affineScheme G₀ hneg).relOfPair γ β) u β = true) ↔ u = γ := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩
      rw [affineScheme_rel_iff G₀ hneg, hidx] at h1 h2
      exact huniq u ((orbMk_affine_eq_iff G₀).mp h1) ((orbMk_affine_eq_iff G₀).mp h2)
    · intro hu; rw [hu]
      exact ⟨(affineScheme G₀ hneg).rel_relOfPair α γ, (affineScheme G₀ hneg).rel_relOfPair γ β⟩
  have hk := (affineScheme G₀ hneg).intersectionNumber_well_defined
      ((affineScheme G₀ hneg).relOfPair α γ) ((affineScheme G₀ hneg).relOfPair γ β)
      ((affineScheme G₀ hneg).relOfPair α β) α β ((affineScheme G₀ hneg).rel_relOfPair α β)
  rw [← hk, Finset.card_eq_one]
  refine ⟨γ, Finset.ext (fun u => ?_)⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact hmem u

/-- **The affine `DominatorReachable` step builder.** From two dominator-reachable points `α, β` and the
affine forced-triangle uniqueness condition pinning `γ`, `γ` is dominator-reachable. The bridge that lets the
δ′ family argument construct `DominatorReachable (affineScheme G₀ hneg) T` derivations purely from
`G₀`-orbit-of-difference uniqueness facts — no abstract intersection numbers. `DominatorReachable.base`
(`t ∈ T`) and this step are the complete toolkit; "the closure exhausts Ω" (`∀ v, DominatorReachable … v`)
for a residue family — the lone open content of the δ′ seal capstone — is built from them. -/
theorem dominatorReachable_affine_step (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    {T : Finset (Fin (p ^ d))} {α β γ : Fin (p ^ d)}
    (hα : DominatorReachable (affineScheme G₀ hneg).toAssociationScheme T α)
    (hβ : DominatorReachable (affineScheme G₀ hneg).toAssociationScheme T β)
    (huniq : ∀ u : Fin (p ^ d),
      (∃ g₀ ∈ G₀, g₀ (affineE.symm u - affineE.symm α) = affineE.symm γ - affineE.symm α) →
      (∃ g₀ ∈ G₀, g₀ (affineE.symm β - affineE.symm u) = affineE.symm β - affineE.symm γ) →
      u = γ) :
    DominatorReachable (affineScheme G₀ hneg).toAssociationScheme T γ :=
  DominatorReachable.step hα hβ (affineScheme_interNum_eq_one_of_unique G₀ hneg huniq)

end AffineScheme

/-! ### Phase 2 / F0 — the cyclic (cyclotomic) affine instance

`affineScheme` instantiated at a **cyclic irreducible** `G₀ = ⟨σ⟩`, where `σ` is multiplication by a
generator of `F_qˣ` (`q = p^d`) transported to the coordinate space `F_p^d = Fin d → ZMod p` along a field
basis `efield : F_q ≃ₗ F_p^d`. This delivers the two model inputs the seal capstone
`reachesRigidOrCameron_viaAffineIrreducible` is stated against on the cyclic floor:
- `G0cyc_irreducible : G₀Irreducible (G0cyc hd)` — EARNED, via the multiplicative-orbit argument (a
  `mul·α`-invariant nonzero subspace contains a full `F_qˣ`-orbit = all nonzero elements ⟹ is `⊤`); no
  `IsSimpleModule` / `F_p[α]=F_q` algebra needed, just that `α` generates `F_qˣ`.
- `neg_mem_G0cyc : neg ∈ G0cyc hd` — the symmetry hypothesis `hneg` (`-1 = α^k` for some `k`, so
  `neg = σ^k`).
The Frobenius `s(C)` bound (F1/F2, self-detection-plan §11.8) targets the remaining `hbound` (discreteness)
on this instance. The two transport homs `mulUnitHom` (mult-by-unit) and `conjHom` (conjugation by `efield`)
make `σ^k` reduce to `α^k` for free (`MonoidHom.map_zpow`), which is what both deliverables turn on. -/

section CyclicAffine

variable {p d : ℕ} [Fact p.Prime]

/-- `GaloisField p d` is finite; equip it with a `Fintype` (no direct instance exists). -/
noncomputable local instance instFintypeGaloisField : Fintype (GaloisField p d) :=
  Fintype.ofFinite _

/-- The field basis isomorphism `F_q ≃ₗ F_p^d` (`q = p^d`), from `finrank = d`. -/
noncomputable def efield (hd : d ≠ 0) : GaloisField p d ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  ((Module.finBasis (ZMod p) (GaloisField p d)).reindex
    (finCongr (GaloisField.finrank p hd))).equivFun

/-- Multiplication-by-a-unit as an `F_p`-linear automorphism of `F_q` — a monoid hom from `F_qˣ`. The
engine for `σ` (mult by a multiplicative generator); being a monoid hom is what lets `σ^k` reduce to `α^k`. -/
noncomputable def mulUnitHom :
    (GaloisField p d)ˣ →* (GaloisField p d ≃ₗ[ZMod p] GaloisField p d) where
  toFun u := LinearEquiv.ofBijective (LinearMap.mulLeft (ZMod p) (u : GaloisField p d))
    ⟨fun x y h => mul_left_cancel₀ u.ne_zero (by simpa [LinearMap.mulLeft_apply] using h),
     fun y => ⟨(↑u⁻¹ : GaloisField p d) * y, by
        rw [LinearMap.mulLeft_apply, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ u.ne_zero]⟩⟩
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [LinearMap.mulLeft_apply, LinearEquiv.mul_apply, Units.val_mul]

@[simp] private theorem mulUnitHom_apply (u : (GaloisField p d)ˣ) (x : GaloisField p d) :
    mulUnitHom u x = (u : GaloisField p d) * x := by
  simp [mulUnitHom]

/-- Conjugation by `efield`: a monoid hom `(F_q ≃ₗ F_q) →* (F_p^d ≃ₗ F_p^d)`. -/
noncomputable def conjHom (hd : d ≠ 0) :
    (GaloisField p d ≃ₗ[ZMod p] GaloisField p d) →*
      ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) where
  toFun e := (efield hd).symm.trans (e.trans (efield hd))
  map_one' := by ext u; simp
  map_mul' a b := by ext u; simp [LinearEquiv.mul_apply]

@[simp] private theorem conjHom_apply (hd : d ≠ 0) (e : GaloisField p d ≃ₗ[ZMod p] GaloisField p d)
    (u : Fin d → ZMod p) : conjHom hd e u = efield hd (e ((efield hd).symm u)) := by
  simp [conjHom]

/-- A multiplicative generator of `F_qˣ` (cyclic). -/
noncomputable def fqGen : (GaloisField p d)ˣ :=
  (IsCyclic.exists_generator (α := (GaloisField p d)ˣ)).choose

theorem fqGen_spec (x : (GaloisField p d)ˣ) : x ∈ Subgroup.zpowers (fqGen (p := p) (d := d)) :=
  (IsCyclic.exists_generator (α := (GaloisField p d)ˣ)).choose_spec x

/-- `σ` — multiplication by `fqGen`, transported to the coordinate space; the generator of `G₀`. -/
noncomputable def sigmaCyc (hd : d ≠ 0) : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd (mulUnitHom (fqGen (p := p) (d := d)))

/-- The cyclic affine group `G₀ = ⟨σ⟩ ≤ GL(F_p^d)`. -/
noncomputable def G0cyc (hd : d ≠ 0) : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
  Subgroup.zpowers (sigmaCyc hd)

/-- `σ^k` acts as multiplication by `α^k` through the field iso — the load-bearing reduction
(`σ^k` ↦ `α^k` for free, since `σ = conjHom (mulUnitHom α)` and both are monoid homs). -/
private theorem sigmaCyc_zpow_apply (hd : d ≠ 0) (k : ℤ) (u : Fin d → ZMod p) :
    (sigmaCyc hd ^ k) u
      = efield hd (((fqGen (p := p) (d := d) ^ k : (GaloisField p d)ˣ) : GaloisField p d)
          * (efield hd).symm u) := by
  have hpow : sigmaCyc hd ^ k = conjHom hd (mulUnitHom (fqGen (p := p) (d := d) ^ k)) := by
    rw [sigmaCyc, ← MonoidHom.map_zpow, ← MonoidHom.map_zpow]
  rw [hpow, conjHom_apply, mulUnitHom_apply]

/-- Every nonzero `z ∈ F_q` is a natural power of the generator `α` (the multiplicative-orbit fact). -/
private theorem exists_npow_fqGen (z : GaloisField p d) (hz : z ≠ 0) :
    ∃ k : ℕ, ((fqGen (p := p) (d := d)) : GaloisField p d) ^ k = z := by
  have hmem : (Units.mk0 z hz) ∈ Submonoid.powers (fqGen (p := p) (d := d)) :=
    mem_powers_iff_mem_zpowers.2 (fqGen_spec _)
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have hv := congrArg (Units.val) hk
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at hv

/-- **`hneg` for the cyclic instance** — `neg ∈ G0cyc` (since `-1 = α^k`, `neg = σ^k`). -/
theorem neg_mem_G0cyc (hd : d ≠ 0) : LinearEquiv.neg (ZMod p) ∈ G0cyc hd := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (fqGen_spec (-1 : (GaloisField p d)ˣ))
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  ext u
  rw [sigmaCyc_zpow_apply, hk]
  have h1 : ((-1 : (GaloisField p d)ˣ) : GaloisField p d) = -1 := by simp
  rw [h1, neg_one_mul, map_neg, LinearEquiv.apply_symm_apply, LinearEquiv.neg_apply]

/-- **`G₀Irreducible` for the cyclic instance** — EARNED via the multiplicative-orbit argument:
a `σ`-invariant nonzero subspace `W` contains, for `0 ≠ w₀ ∈ W`, the full orbit `{α^k · w₀}`, which
(since `α` generates `F_qˣ`) is every nonzero element ⟹ `W = ⊤`. -/
theorem G0cyc_irreducible (hd : d ≠ 0) : G₀Irreducible (G0cyc (p := p) hd) := by
  intro W hWinv
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  refine Or.inr ?_
  have hσmem : sigmaCyc (p := p) hd ∈ G0cyc (p := p) hd := Subgroup.mem_zpowers _
  obtain ⟨w₀, hw₀W, hw₀0⟩ := (Submodule.ne_bot_iff W).1 hWbot
  set x₀ : GaloisField p d := (efield hd).symm w₀ with hx₀def
  have hx₀0 : x₀ ≠ 0 := by
    rw [hx₀def, ne_eq, LinearEquiv.map_eq_zero_iff]; exact hw₀0
  rw [eq_top_iff]
  intro v _
  by_cases hv0 : (efield hd).symm v = 0
  · have hvz : v = 0 := by
      have hcong := congrArg (efield hd) hv0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at hcong
    rw [hvz]; exact W.zero_mem
  · set y : GaloisField p d := (efield hd).symm v with hydef
    obtain ⟨k, hk⟩ := exists_npow_fqGen (y * x₀⁻¹) (mul_ne_zero hv0 (inv_ne_zero hx₀0))
    have hmemk : (sigmaCyc hd ^ (k : ℤ)) w₀ ∈ W :=
      hWinv _ (Subgroup.zpow_mem _ hσmem k) w₀ hw₀W
    have hval : (sigmaCyc hd ^ (k : ℤ)) w₀ = v := by
      rw [sigmaCyc_zpow_apply,
        show ((fqGen (p := p) (d := d) ^ (k : ℤ) : (GaloisField p d)ˣ) : GaloisField p d)
            = ((fqGen (p := p) (d := d)) : GaloisField p d) ^ k from by
          rw [zpow_natCast, Units.val_pow_eq_pow_val],
        hk, ← hx₀def, mul_assoc, inv_mul_cancel₀ hx₀0, mul_one, hydef,
        LinearEquiv.apply_symm_apply]
    rwa [hval] at hmemk

/-- The **cyclic affine scheme** — `affineScheme` at `G0cyc`. Irreducible (`G0cyc_irreducible`) and symmetric
(`neg_mem_G0cyc`). **⚠️ NOTE (2026-06-09): this is the rank-2 complete graph `K_{p^d}`** — `G0cyc` uses a
*full* multiplicative generator, so `⟨mul fqGen⟩` is transitive on `V ∖ {0}` (one nonzero orbit). It is the
degenerate *large* case (routed to Cameron), **not** the cyclotomic leak candidate. The genuine F2b target is
`G0pow β` for a **proper** `β = α^m` (see the "F2b target correction" subsection below); use
`G0pow_irreducible` there, not this. -/
noncomputable def cyclicAffineScheme (hd : d ≠ 0) : SchurianScheme (p ^ d) :=
  affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)

/-! #### F1 — the Frobenius structure (the `Ĝ ⊋ G` separability gap, made concrete)

The Frobenius `φ : x ↦ x^p` is `ZMod p`-**linear** (because `c^p = c` on the prime field), so it sits in
`GL(d,p)`, and it conjugates `σ` (mult by the generator `α`) to `σ^p` (`φ(α·x) = α^p·φ(x)`). Hence `φ`
**normalizes** `G0cyc = ⟨σ⟩` but generally is **not in it**: `⟨σ, φ⟩ = ΓL(1,q) ⊋ ⟨σ⟩`. That extra Galois
symmetry is an *algebraic* automorphism of the scheme the group does not realize — the `Ĝ ⊋ G` gap, and the
degeneracy a `Γ`-fixed base would suffer (F2). **General-theorem shadow:** this conjugation relation
`φσφ⁻¹ = σ^p` is exactly "an algebraic automorphism not in the group", which is what the `s(C)` leak is in
general — here it is finite-dimensional and explicit. -/

/-- Frobenius `x ↦ x^p` as a `ZMod p`-**linear** automorphism of `F_q` (linear since `c^p = c` on the prime
field, `ZMod.pow_card`). The algebraic automorphism witnessing the `Ĝ ⊋ G` gap. -/
noncomputable def frobLinear : GaloisField p d ≃ₗ[ZMod p] GaloisField p d where
  toFun := frobeniusEquiv (GaloisField p d) p
  map_add' := map_add _
  map_smul' c x := by
    show frobeniusEquiv (GaloisField p d) p (c • x)
        = (RingHom.id (ZMod p)) c • frobeniusEquiv (GaloisField p d) p x
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [frobeniusEquiv_def, ← map_pow, ZMod.pow_card]
  invFun := (frobeniusEquiv (GaloisField p d) p).symm
  left_inv := (frobeniusEquiv (GaloisField p d) p).left_inv
  right_inv := (frobeniusEquiv (GaloisField p d) p).right_inv

@[simp] private theorem frobLinear_apply (x : GaloisField p d) :
    frobLinear (p := p) (d := d) x = x ^ p := frobeniusEquiv_def (GaloisField p d) p x

/-- **The twist relation** `φ(α·x) = α^p · φ(x)` — Frobenius is a ring hom, so it carries multiplication by
`α` to multiplication by `α^p`. The algebraic core of the gap. -/
private theorem frobLinear_mul (α x : GaloisField p d) :
    frobLinear (α * x) = α ^ p * frobLinear x := by
  simp only [frobLinear_apply, mul_pow]

/-- `φ` carries `mul·α` to `(mul·α)^p` under conjugation, as an identity of linear automorphisms
(`φ ∘ (mul α) ∘ φ⁻¹ = (mul α)^p`). -/
private theorem frobLinear_conj_mulUnit :
    frobLinear (p := p) (d := d) * mulUnitHom (fqGen) * (frobLinear)⁻¹
      = (mulUnitHom (fqGen (p := p) (d := d))) ^ p := by
  ext x
  have hinv : frobLinear (p := p) (d := d) ((frobLinear (p := p) (d := d))⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [← map_pow, mulUnitHom_apply, Units.val_pow_eq_pow_val, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, mulUnitHom_apply, frobLinear_mul, hinv]

/-- Frobenius transported to the coordinate space `F_p^d` — an element of `GL(d,p)` (the linear part of a
Galois twist of the affine group). -/
noncomputable def frobCoord (hd : d ≠ 0) : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd frobLinear

/-- **The normalizing relation** `frobCoord · σ · frobCoord⁻¹ = σ^p` — Frobenius conjugates the cyclic
generator to its `p`-th power. So `frobCoord` normalizes `G0cyc = ⟨σ⟩` but lies in it only when `φ ∈ ⟨σ⟩`;
in general `⟨σ, frobCoord⟩ = ΓL(1,q) ⊋ ⟨σ⟩` — the algebraic-automorphism gap (`Ĝ ⊋ G`) the cyclotomic
`s(C)` leak would exploit, here finite and explicit. -/
theorem frobCoord_conj_sigmaCyc (hd : d ≠ 0) :
    frobCoord (p := p) hd * sigmaCyc hd * (frobCoord hd)⁻¹ = sigmaCyc hd ^ p := by
  rw [frobCoord, sigmaCyc, ← map_inv, ← map_mul, ← map_mul, frobLinear_conj_mulUnit, map_pow]

/-! #### F2b frame — the cyclic separation crux as a single named proposition

This packages the entire open content of the affine-cyclic slice into ONE Lean proposition
(`CyclicAffineSeparates`) and wires it to the seal (`reachesRigidOrCameron_viaCyclicSeparation`). It does
**not** prove the crux — `CyclicAffineSeparates` is carried as a hypothesis, exactly the uncited open `s(C)`
counting (self-detection-plan §11.8 F2b). Its value is turning the prose conjecture into one falsifiable
statement about **multi-coset-intersection counts**, the object F1's Frobenius structure acts on (a `Γ`-fixed
base produces `φ`-twins; a Γ-breaking base is conjectured to separate — the de-risk probe
`Probe_RoundsToDiscrete_Cyclotomic` confirms this empirically at `|T| = O(d)`, depth 2). -/

/-- **The cyclic-affine separation crux (the single open proposition).** A bounded individualization set `T`
whose depth-2 **difference profile** is injective: for every difference-relation profile `ρ` and tail
relation `b`, the multi-coset-intersection counts of matching `z` separate every pair of vertices. This is
the Frobenius `s(C)` bound; `discrete_affineScheme_of_twoRoundDiffSeparates` consumes it to discharge
`hbound`. **Open** — the empirically-confirmed (probe) but uncited counting core. -/
def CyclicAffineSeparates (hd : d ≠ 0) (bound : Nat) : Prop :=
  ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
    ∀ u u' : Fin (p ^ d),
      (∀ (ρ : Fin (p ^ d) → Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1))
          (b : Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1)),
        (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
          (∀ t ∈ T, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u)) = b)).card
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
          (∀ t ∈ T, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm t)) = ρ t)
          ∧ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).relOfPair (affineE 0)
              (affineE (affineE.symm z - affineE.symm u')) = b)).card) → u = u'

/-- **The seal on the cyclic-affine family, reduced to the single crux `CyclicAffineSeparates`.** Instantiates
`reachesRigidOrCameron_viaAffineIrreducible` at the cyclic `G₀ = G0cyc`, discharging `hbound` from
`CyclicAffineSeparates` via the F2a producer `discrete_affineScheme_of_twoRoundDiffSeparates`.

**⚠️ CONDITIONAL — NOT the closed seal.** It carries `hClassify` (G3, cited), `hne`/`hrank` (the scheme is a
genuine rank-≥2 association scheme — discharged per instance), `hImprim` (landed/earned, tower-reducible), and
the **open** `hsep : CyclicAffineSeparates` (the Frobenius `s(C)` counting, F2b — uncited). Closing the seal on
this family ⟺ proving `CyclicAffineSeparates`, which is open `s(C)` mathematics.

**⚠️ DEGENERATE TARGET — prefer `reachesRigidOrCameron_viaPowSeparation`.** `G0cyc` is a *full* multiplicative
generator, so this scheme is the rank-2 `K_{p^d}` and `CyclicAffineSeparates` is *false* (unsatisfiable: no
bounded base discretizes `K_q`). The genuine rank-≥3 leak candidate is `affineScheme (G0pow hd β)` (proper
`β = α^m`); use `reachesRigidOrCameron_viaPowSeparation` / `PowAffineSeparates` (below) — that is where the
Frobenius step-1 work and `clebschWitness_irreducible` live. This cyclic version is kept as the documented
degenerate reference. -/
theorem reachesRigidOrCameron_viaCyclicSeparation (hd : d ≠ 0)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank + 1),
        ∃ v w, (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).rank)
    (hsep : CyclicAffineSeparates (p := p) hd bound)
    (hImprim : ¬ (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0cyc (p := p) hd) (neg_mem_G0cyc hd)) := by
  refine reachesRigidOrCameron_viaAffineIrreducible (G₀ := G0cyc hd) hClassify (neg_mem_G0cyc hd)
    hne hrank ?_ hImprim
  rintro ⟨-, -⟩
  obtain ⟨T, hcard, hTsep⟩ := hsep
  exact ⟨T, hcard, discrete_affineScheme_of_twoRoundDiffSeparates (G0cyc hd) (neg_mem_G0cyc hd) hTsep⟩

/-! #### F2b target correction — proper cyclic subgroups (the genuine cyclotomic schemes)

**Gap (found 2026-06-09).** `G0cyc` uses a *full* multiplicative generator `fqGen`, so `⟨mul fqGen⟩` is
transitive on `V ∖ {0}` ⟹ `cyclicAffineScheme` is the **rank-2 complete graph `K_{p^d}`** — the *large* case
(`|Aut| = (p^d)!`, routed to Cameron), NOT the cyclotomic leak candidate (for which `CyclicAffineSeparates`
is in fact false: no bounded base discretizes `K_q`). The genuine F2b target is a **proper** cyclic subgroup
`G0pow β = ⟨mul β⟩` (`β = α^m`, e.g. the index-3 Clebsch family on `F_16`), `rank ≥ 3`, where irreducibility
comes from `β` **field-generating** `F_q` — NOT from the orbit being everything. `G0pow_irreducible` is the
§5.3 "invariant subspace ⟺ subfield" template: a `mul·β`-invariant subspace closed under `mul·β` is closed
under `mul·F_p[β] = mul·F_q`, hence `⊥` or `⊤`. F1's `Ĝ ⊋ G` Frobenius gap is the Galois action permuting
these (subfield-free) cosets. **Open:** proving separation (`CyclicAffineSeparates`-analogue) for `G0pow β`
is the uncited `s(C)` crux. -/

/-- `σ_β` — multiplication by an arbitrary unit `β`, transported to `F_p^d`. Generalizes `sigmaCyc`
(`= sigmaPow fqGen`). -/
noncomputable def sigmaPow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  conjHom hd (mulUnitHom β)

/-- The cyclic affine group `G₀ = ⟨mul β⟩` for an arbitrary unit `β` (the proper-subgroup / cyclotomic case
when `β = α^m`). Generalizes `G0cyc` (`= G0pow fqGen`). -/
noncomputable def G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
  Subgroup.zpowers (sigmaPow hd β)

/-- `σ_β^k` acts as multiplication by `β^k` through the field iso. Generalizes `sigmaCyc_zpow_apply`. -/
private theorem sigmaPow_zpow_apply (hd : d ≠ 0) (β : (GaloisField p d)ˣ) (k : ℤ) (u : Fin d → ZMod p) :
    (sigmaPow hd β ^ k) u
      = efield hd (((β ^ k : (GaloisField p d)ˣ) : GaloisField p d) * (efield hd).symm u) := by
  have hpow : sigmaPow hd β ^ k = conjHom hd (mulUnitHom (β ^ k)) := by
    rw [sigmaPow, ← MonoidHom.map_zpow, ← MonoidHom.map_zpow]
  rw [hpow, conjHom_apply, mulUnitHom_apply]

/-- **`hneg` for the proper cyclic instance** — `neg ∈ G0pow β` when `-1 ∈ ⟨β⟩`. Generalizes `neg_mem_G0cyc`. -/
theorem neg_mem_G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) :
    LinearEquiv.neg (ZMod p) ∈ G0pow hd β := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hβneg
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  ext u
  rw [sigmaPow_zpow_apply, hk]
  have h1 : ((-1 : (GaloisField p d)ˣ) : GaloisField p d) = -1 := by simp
  rw [h1, neg_one_mul, map_neg, LinearEquiv.apply_symm_apply, LinearEquiv.neg_apply]

/-- **`G₀Irreducible (G0pow β)` via field-generation** (the §5.3 subfield template). If the `F_p`-span of the
powers of `β` is all of `F_q` (`β` field-generates), then `⟨mul β⟩` acts irreducibly: a `mul·β`-invariant
nonzero subspace `W` contains, for `0 ≠ w₀ ∈ W`, the image `f '' {β^k}` where `f : c ↦ efield (x₀ · c)`
(`x₀ = e⁻¹w₀`); since `span {β^k} = ⊤` and `f` is surjective, that image spans `⊤`, so `W = ⊤`. This is the
proper-subgroup irreducibility the orbit argument (`G0cyc_irreducible`) could not give — the genuine
cyclotomic case. -/
theorem G0pow_irreducible (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβspan : Submodule.span (ZMod p)
        (Set.range (fun k : ℕ => ((β : GaloisField p d)) ^ k)) = ⊤) :
    G₀Irreducible (G0pow hd β) := by
  intro W hWinv
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  refine Or.inr ?_
  obtain ⟨w₀, hw₀W, hw₀0⟩ := (Submodule.ne_bot_iff W).1 hWbot
  have hx₀0 : (efield hd).symm w₀ ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]; exact hw₀0
  set f : GaloisField p d →ₗ[ZMod p] (Fin d → ZMod p) :=
    (efield hd).toLinearMap ∘ₗ LinearMap.mulLeft (ZMod p) ((efield hd).symm w₀) with hfdef
  have hf_surj : Function.Surjective f := by
    intro z
    refine ⟨((efield hd).symm w₀)⁻¹ * (efield hd).symm z, ?_⟩
    simp only [hfdef, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
    rw [mul_inv_cancel_left₀ hx₀0, LinearEquiv.apply_symm_apply]
  have hfmem : ∀ y ∈ (f '' Set.range (fun k : ℕ => (β : GaloisField p d) ^ k)), y ∈ W := by
    rintro y ⟨c, ⟨k, rfl⟩, rfl⟩
    have hmem := hWinv (sigmaPow hd β ^ (k : ℤ))
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k) w₀ hw₀W
    rw [sigmaPow_zpow_apply, zpow_natCast, Units.val_pow_eq_pow_val] at hmem
    rw [hfdef]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
    rwa [mul_comm] at hmem
  rw [eq_top_iff]
  calc (⊤ : Submodule (ZMod p) (Fin d → ZMod p))
      = Submodule.map f ⊤ := by rw [Submodule.map_top, LinearMap.range_eq_top.2 hf_surj]
    _ = Submodule.map f (Submodule.span (ZMod p)
          (Set.range (fun k : ℕ => (β : GaloisField p d) ^ k))) := by rw [hβspan]
    _ = Submodule.span (ZMod p) (f '' Set.range (fun k : ℕ => (β : GaloisField p d) ^ k)) :=
        Submodule.map_span f _
    _ ≤ W := Submodule.span_le.2 hfmem

/-- **`G₀Irreducible (G0pow β)` from field-generation `Algebra.adjoin = ⊤`** (the clean hypothesis form). The
`F_p`-subalgebra generated by `β` is the span of its powers (`Algebra.adjoin_eq_span`), so `β` generating
`F_q` as an `F_p`-algebra is exactly `G0pow_irreducible`'s span hypothesis. This is the form a concrete witness
discharges (`β` a primitive/field-generating element). -/
theorem G0pow_irreducible_of_adjoin (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβ : Algebra.adjoin (ZMod p) {(β : GaloisField p d)} = ⊤) :
    G₀Irreducible (G0pow hd β) := by
  refine G0pow_irreducible hd β ?_
  have h1 := Algebra.adjoin_eq_span (ZMod p) ({(β : GaloisField p d)} : Set (GaloisField p d))
  rw [hβ, Algebra.top_toSubmodule] at h1
  rw [h1]
  congr 1
  ext x
  simp [Submonoid.mem_closure_singleton, Set.mem_range, eq_comm]

/-! #### §S-stage3-δ — the affine cyclic arithmetic reduction (G0pow forced-triangle in `F_q` powers)

Increment 4b of the δ′ Stage 3 (`docs/chain-descent-general-cc-separability.md` §5 "Stage 3 (δ′ route)").
The affine forced-triangle criterion (`affineScheme_interNum_eq_one_of_unique`) states pinning via
`G₀`-orbit-of-difference uniqueness; for the **cyclotomic family** `G₀ = G0pow g = ⟨mul g⟩` that orbit is a
multiplicative `⟨g⟩`-orbit in `F_q`. This block translates the orbit condition into pure `F_q`-power
arithmetic: a `G0pow g`-orbit relation is multiplication by `g^k` through the field iso (`G0pow_orbit_iff`,
from `sigmaPow_zpow_apply`), so the pinning of `γ` by `α, β` reads as "the only `u` with
`g^k·(fieldOf u − fieldOf α) = fieldOf γ − fieldOf α` and `g^k·(fieldOf β − fieldOf u) = fieldOf β −
fieldOf γ` is `γ`" (`dominatorReachable_G0pow_step`). This is the idiom the cyclotomic `s(C)` closure
argument reasons in — the `(r+1 − r·h) ∈ ⟨g⟩ → h = 1` reduction of §5 is this with the field difference
ratios divided out (the further packaging, deferred to incr 4c). -/

/-- The **field coordinate** of a point: `Fin (p^d) → F_p^d → F_q` (`(efield).symm ∘ affineE.symm`). The
bijection carrying the affine point set into the field, in which the cyclotomic orbit-of-difference becomes a
multiplicative `⟨g⟩`-orbit. -/
noncomputable def fieldOf (hd : d ≠ 0) (x : Fin (p ^ d)) : GaloisField p d :=
  (efield hd).symm (affineE.symm x)

/-- `fieldOf` is injective (it is the composite of two injective `Equiv.symm` maps). The distinctness
transport: distinct affine points have distinct field coordinates. -/
theorem fieldOf_injective (hd : d ≠ 0) : Function.Injective (fieldOf (p := p) (d := d) hd) := by
  intro x y h
  simp only [fieldOf] at h
  exact affineE.symm.injective ((efield hd).symm.injective h)

/-- **The cyclotomic orbit reduction (the core arithmetic translation).** A `G0pow g`-orbit relation between
coordinate vectors `v, w` is exactly multiplication by a power of `g` through the field iso:
`∃ g₀ ∈ G0pow g, g₀ v = w` ↔ `∃ k : ℤ, g^k · (efield.symm v) = efield.symm w`. From `sigmaPow_zpow_apply`
(`σ_g^k` acts as `·g^k` through `efield`) and injectivity of `efield`. The brick converting the cyclic
affine action into `F_q` multiplication — the foundation of the δ′ cyclotomic family argument. -/
theorem G0pow_orbit_iff (hd : d ≠ 0) (g : (GaloisField p d)ˣ) (v w : Fin d → ZMod p) :
    (∃ g₀ ∈ G0pow hd g, g₀ v = w) ↔
      ∃ k : ℤ, ((g ^ k : (GaloisField p d)ˣ) : GaloisField p d) * (efield hd).symm v
        = (efield hd).symm w := by
  constructor
  · rintro ⟨g₀, hg₀, hgw⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₀
    refine ⟨k, ?_⟩
    rw [sigmaPow_zpow_apply] at hgw
    have hcong := congrArg (efield hd).symm hgw
    rwa [LinearEquiv.symm_apply_apply] at hcong
  · rintro ⟨k, hk⟩
    refine ⟨sigmaPow hd g ^ k, Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩, ?_⟩
    rw [sigmaPow_zpow_apply, hk, LinearEquiv.apply_symm_apply]

/-- **The cyclotomic `DominatorReachable` step builder (`F_q`-power form).** The forced-triangle step for the
cyclotomic family `affineScheme (G0pow g)`, with the pinning condition in pure `F_q` powers: from two
dominator-reachable points `α, β`, if the only `u` with
`g^k·(fieldOf u − fieldOf α) = fieldOf γ − fieldOf α` (for some `k`) and
`g^k·(fieldOf β − fieldOf u) = fieldOf β − fieldOf γ` (for some `k`) is `γ`, then `γ` is dominator-reachable.
Obtained from `dominatorReachable_affine_step` by `G0pow_orbit_iff` (orbit ⟹ power form on each hypothesis,
`efield.symm` linear over the difference). The toolkit the cyclotomic single-base closure (incr 4c) builds
its `DominatorReachable` derivations with — pure `F_q` arithmetic, no orbital/intersection-number bookkeeping. -/
theorem dominatorReachable_G0pow_step (hd : d ≠ 0) (g : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd g)
    {T : Finset (Fin (p ^ d))} {α β γ : Fin (p ^ d)}
    (hα : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T α)
    (hβ : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T β)
    (huniq : ∀ u : Fin (p ^ d),
      (∃ k : ℤ, ((g ^ k : (GaloisField p d)ˣ) : GaloisField p d)
          * (fieldOf hd u - fieldOf hd α) = fieldOf hd γ - fieldOf hd α) →
      (∃ k : ℤ, ((g ^ k : (GaloisField p d)ˣ) : GaloisField p d)
          * (fieldOf hd β - fieldOf hd u) = fieldOf hd β - fieldOf hd γ) →
      u = γ) :
    DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T γ := by
  refine dominatorReachable_affine_step (G0pow hd g) hneg hα hβ (fun u h1 h2 => huniq u ?_ ?_)
  · obtain ⟨k, hk⟩ := (G0pow_orbit_iff hd g _ _).mp h1
    rw [map_sub, map_sub] at hk
    exact ⟨k, hk⟩
  · obtain ⟨k, hk⟩ := (G0pow_orbit_iff hd g _ _).mp h2
    rw [map_sub, map_sub] at hk
    exact ⟨k, hk⟩

/-- **The cyclotomic ratio-form step builder (incr 4c — the `s(C)` arithmetic boundary).** The
forced-triangle step with the two field-difference equations *divided through*: for distinct field
coordinates (`c ≠ a`, `b ≠ c`), `γ` is pinned by `α, β` once the only field element `h` that is **both** a
power of `g` and has `1 + r·(1 − h)` a power of `g` (with the cross-ratio `r = (c−a)/(b−c)`,
`a = fieldOf α`, etc.) is `h = 1`. Obtained from `dominatorReachable_G0pow_step` by setting
`h = (x−a)/(c−a)` for the variable point `x = fieldOf u` (so cond 1 ⟺ `h ∈ ⟨g⟩`) and computing
`(b−x)/(b−c) = 1 + r(1−h)` (so cond 2 ⟺ `1 + r(1−h) ∈ ⟨g⟩`); `h = 1 ⟺ x = c ⟺ u = γ`. This is the
`(r+1 − r·h) ∈ ⟨g⟩ → h = 1` reduction of §5 — the closest Lean form to the open cyclotomic `s(C)`
arithmetic, and the one exposing the **char-2-midpoint obstruction**: when `r = 1` (γ the midpoint),
`1 + (1 − h) = 2 − h = h` in characteristic 2, so *every* `h` satisfies the antecedent and nothing is
pinned — char-2 residues need non-midpoint triangles (`docs/chain-descent-general-cc-separability.md`
§5 "Stage 3 (δ′ route)"). -/
theorem dominatorReachable_G0pow_ratio_step (hd : d ≠ 0) (g : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd g)
    {T : Finset (Fin (p ^ d))} {α β γ : Fin (p ^ d)}
    (hca : fieldOf hd γ ≠ fieldOf hd α) (hbc : fieldOf hd β ≠ fieldOf hd γ)
    (hα : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T α)
    (hβ : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T β)
    (hpin : ∀ h : GaloisField p d,
        (∃ k : ℤ, (g : GaloisField p d) ^ k = h) →
        (∃ k : ℤ, (g : GaloisField p d) ^ k
          = 1 + (fieldOf hd γ - fieldOf hd α) / (fieldOf hd β - fieldOf hd γ) * (1 - h)) →
        h = 1) :
    DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T γ := by
  refine dominatorReachable_G0pow_step hd g hneg hα hβ (fun u hc1 hc2 => ?_)
  obtain ⟨k1, hk1⟩ := hc1
  obtain ⟨k2, hk2⟩ := hc2
  rw [Units.val_zpow_eq_zpow_val] at hk1 hk2
  set a := fieldOf hd α with ha
  set b := fieldOf hd β with hb
  set c := fieldOf hd γ with hc
  set x := fieldOf hd u with hxdef
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hca
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hxa : x - a ≠ 0 := fun h0 => hca' (by rw [h0, mul_zero] at hk1; exact hk1.symm)
  have hbx : b - x ≠ 0 := fun h0 => hbc' (by rw [h0, mul_zero] at hk2; exact hk2.symm)
  set h := (x - a) / (c - a) with hh
  have hg1 : (g : GaloisField p d) ^ k1 = (c - a) / (x - a) := (eq_div_iff hxa).2 hk1
  have hg2 : (g : GaloisField p d) ^ k2 = (b - c) / (b - x) := (eq_div_iff hbx).2 hk2
  have halg : (b - x) / (b - c) = 1 + (c - a) / (b - c) * (1 - h) := by
    rw [hh]; field_simp; ring
  have hph : ∃ k : ℤ, (g : GaloisField p d) ^ k = h := by
    refine ⟨-k1, ?_⟩; rw [zpow_neg, hg1, hh, inv_div]
  have hpw : ∃ k : ℤ, (g : GaloisField p d) ^ k = 1 + (c - a) / (b - c) * (1 - h) := by
    refine ⟨-k2, ?_⟩; rw [zpow_neg, hg2, inv_div, halg]
  have hh1 : h = 1 := hpin h hph hpw
  have hxc : x = c := by
    have he : x - a = c - a := (div_eq_one_iff_eq hca').1 (by rw [← hh]; exact hh1)
    exact sub_left_inj.1 he
  have hfin : fieldOf hd u = fieldOf hd γ := by rw [← hxdef, ← hc]; exact hxc
  simp only [fieldOf] at hfin
  exact affineE.symm.injective ((efield hd).symm.injective hfin)

/-- In a field, the powers of `-1` are exactly `±1`: `(∃ k:ℤ, (-1)^k = h) ↔ h = 1 ∨ h = -1`. The
multiplicative-group `⟨-1⟩ = {1, -1}` fact, in `zpow` form for the `H = {±1}` family. -/
private theorem exists_zpow_neg_one_iff {F : Type*} [Field F] {h : F} :
    (∃ k : ℤ, (-1 : F) ^ k = h) ↔ h = 1 ∨ h = -1 := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

/-- **The `H = {±1}` cyclotomic family closes from any 2-base (odd characteristic) — the first end-to-end
discharge of the δ′ seal's closure hypothesis on a real `affineScheme` family.** For `g = -1` (so
`G₀ = ⟨mul (-1)⟩`, `⟨g⟩ = {1, -1}`) over odd characteristic (`p ≠ 2`), **every** point is
dominator-reachable from any 2-element base `{α, β}` (`α ≠ β`): each `γ ∉ {α,β}` is forced-triangle-pinned
by `α, β` in one round. Arithmetic (via `dominatorReachable_G0pow_ratio_step`): the cross-ratio
`r = (c−a)/(b−c)` of pairwise-distinct points satisfies `r ∉ {0, -1}`, so for the only nontrivial
`h = -1 ∈ ⟨g⟩` the value `1 + r·(1 − (-1)) = 1 + 2r ∉ {1, -1} = ⟨g⟩` (uses `2 ≠ 0`), the pinning
antecedent fails, and only `h = 1` survives. This proves `∀ v, DominatorReachable … {α,β} v`, the seal's
`hclo`, for the whole `g = -1` family — removing the cyclotomic citation for it and showing the δ′ route
is not vacuous. (Char ≠ 2 is essential: it is exactly the char-2-midpoint obstruction — at `p = 2`,
`⟨g⟩ = {1}` and the argument collapses.) -/
theorem dominatorReachable_G0pow_neg (hd : d ≠ 0) (hp2 : p ≠ 2)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd (-1))
    {α β : Fin (p ^ d)} (hαβ : α ≠ β) :
    ∀ v : Fin (p ^ d),
      DominatorReachable (affineScheme (G0pow hd (-1)) hneg).toAssociationScheme {α, β} v := by
  have h2 : (2 : GaloisField p d) ≠ 0 := by
    rw [show (2 : GaloisField p d) = ((2 : ℕ) : GaloisField p d) by push_cast; ring,
      Ne, CharP.cast_eq_zero_iff (GaloisField p d) p 2]
    intro hdvd
    rcases (Nat.prime_two.eq_one_or_self_of_dvd p hdvd) with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp2 h
  have hinj := fieldOf_injective (p := p) (d := d) hd
  intro v
  by_cases hv : v = α ∨ v = β
  · rcases hv with h | h
    · rw [h]; exact DominatorReachable.base (Finset.mem_insert_self α {β})
    · rw [h]; exact DominatorReachable.base (Finset.mem_insert_of_mem (Finset.mem_singleton_self β))
  · push Not at hv
    obtain ⟨hvα, hvβ⟩ := hv
    have hca : fieldOf hd v ≠ fieldOf hd α := fun h => hvα (hinj h)
    have hbc : fieldOf hd β ≠ fieldOf hd v := fun h => hvβ (hinj h).symm
    have hab : fieldOf hd α ≠ fieldOf hd β := fun h => hαβ (hinj h)
    refine dominatorReachable_G0pow_ratio_step hd (-1) hneg hca hbc
      (DominatorReachable.base (Finset.mem_insert_self α {β}))
      (DominatorReachable.base (Finset.mem_insert_of_mem (Finset.mem_singleton_self β)))
      (fun h hh hw => ?_)
    simp only [Units.val_neg, Units.val_one] at hh hw
    rw [exists_zpow_neg_one_iff] at hh hw
    rcases hh with rfl | rfl
    · rfl
    · exfalso
      set r := (fieldOf hd v - fieldOf hd α) / (fieldOf hd β - fieldOf hd v) with hr
      have hr0 : r ≠ 0 := by
        rw [hr]; exact div_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hbc)
      have hrm1 : r ≠ -1 := by
        rw [hr]; intro heq
        rw [div_eq_iff (sub_ne_zero.mpr hbc)] at heq
        exact hab (by linear_combination -heq)
      rcases hw with hw1 | hw1
      · rcases mul_eq_zero.mp (show (2 : GaloisField p d) * r = 0 by linear_combination hw1) with h | h
        · exact h2 h
        · exact hr0 h
      · rcases mul_eq_zero.mp
          (show (2 : GaloisField p d) * (r + 1) = 0 by linear_combination hw1) with h | h
        · exact h2 h
        · exact hrm1 (by linear_combination h)

/-- **The seal on the `H = {±1}` cyclotomic family, with the δ′ closure DISCHARGED (not assumed).**
Instantiates the citation-free checkpoint `reachesRigidOrCameron_viaDominatorClosure` at
`affineScheme (G0pow (-1))` (odd characteristic), feeding its closure hypothesis `hclo` from
`dominatorReachable_G0pow_neg` (any 2-base closes). So the seal holds for this whole family carrying only
the *standard* {G3 `hClassify` + `hne` + `hrank` + `hImprim`} — **the open `hclo` is gone, proved rather
than carried.** The first family on which the δ′ route discharges the seal's open mathematical content
outright; concrete evidence the route is not vacuous. (rank ≥ 3 — i.e. `q ≥ 5` — is carried as `hrank`,
the only restriction beyond odd characteristic.) -/
theorem reachesRigidOrCameron_viaG0powNeg {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat} (hbd : 2 ≤ bound)
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hd : d ≠ 0) (hp2 : p ≠ 2)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd (-1))
    (hne : ∀ i : Fin ((affineScheme (G0pow hd (-1)) hneg).rank + 1),
        ∃ v w, (affineScheme (G0pow hd (-1)) hneg).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0pow hd (-1)) hneg).rank)
    {α β : Fin (p ^ d)} (hαβ : α ≠ β)
    (hImprim : ¬ (affineScheme (G0pow hd (-1)) hneg).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd (-1)) hneg)
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd (-1)) hneg)) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd (-1)) hneg)
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd (-1)) hneg))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0pow hd (-1)) hneg) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0pow hd (-1)) hneg) := by
  refine reachesRigidOrCameron_viaDominatorClosure hClassify
    (affineScheme (G0pow hd (-1)) hneg) hne hrank (T := {α, β}) ?_ ?_ hImprim
  · calc ({α, β} : Finset (Fin (p ^ d))).card
        ≤ ({β} : Finset (Fin (p ^ d))).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
      _ ≤ bound := hbd
  · exact dominatorReachable_G0pow_neg hd hp2 hneg hαβ

/-! #### §S-stage3-δ (multi-round) — the subfield family `H = K^×` and its 2-round closure

The genuine multi-round content (`docs/chain-descent-general-cc-separability.md` §5 "Stage 3 (δ′ route)"):
for `|H| > 2`, one round from a 2-base no longer pins every point, so the closure must iterate. The clean
tractable larger-`H` family is `H = K^×` for a subfield `K ⊊ F_q` (canonically `K = F_p ⊆ F_{p^d}`,
`d ≥ 2`). The pinning sufficient condition is **size-free**: if the cross-ratio `r = (c−a)/(b−c) ∉ K`
then `γ` is pinned by `α, β` (for `h ∈ K^×∖{1}`, `1−h ∈ K^×` so `r(1−h) ∉ K`, hence `1+r(1−h) ∉ K ⊇ H`,
the antecedent fails). The base `{α,β}` of `K`-points closes `F_q` in **two rounds**: round 1 pins every
non-`K` point (ratio `(nonK−K)/(K−nonK) ∉ K`), round 2 pins every `K` point via `α` and a reached non-`K`
point (ratio `(K−K)/(nonK−K) ∉ K`). The field facts `⟨g⟩ = K^×` (`hHK`) and a non-`K` witness are carried
hypotheses; the instantiation (`K = F_p`, `g = fqGen^{(p^d−1)/(p−1)}`) is the field-theory follow-on. -/

/-- Subfield ratio fact (numerator out of `K`): `a, b ∈ K`, `c ∉ K`, `a ≠ b` ⟹ `(c−a)/(b−c) ∉ K`. The
round-1 pinning datum (pin a non-`K` point by two `K`-base points). -/
private theorem ratio_not_mem_num_out {F : Type*} [Field F] {K : Subfield F} {a b c : F}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∉ K) (hab : a ≠ b) : (c - a) / (b - c) ∉ K := by
  have hbc : b - c ≠ 0 := fun h => hc (by rw [← sub_eq_zero.mp h]; exact hb)
  intro hmem
  set r := (c - a) / (b - c) with hr
  have key : r * (b - c) = c - a := by rw [hr]; field_simp
  by_cases h1 : (1 : F) + r = 0
  · have hr1 : r = -1 := by linear_combination h1
    rw [hr1] at key
    exact hab (by linear_combination key)
  · apply hc
    have hceq : c = (a + r * b) / (1 + r) := by rw [eq_div_iff h1]; linear_combination -key
    rw [hceq]
    exact K.div_mem (K.add_mem ha (K.mul_mem hmem hb)) (K.add_mem K.one_mem hmem)

/-- Subfield ratio fact (denominator out of `K`): `a, c ∈ K`, `b ∉ K`, `c ≠ a` ⟹ `(c−a)/(b−c) ∉ K`. The
round-2 pinning datum (pin a `K` point by a `K`-base point and a reached non-`K` point). -/
private theorem ratio_not_mem_denom_out {F : Type*} [Field F] {K : Subfield F} {a b c : F}
    (ha : a ∈ K) (hb : b ∉ K) (hc : c ∈ K) (hca : c ≠ a) : (c - a) / (b - c) ∉ K := by
  have hbc : b - c ≠ 0 := fun h => hb (by rw [sub_eq_zero.mp h]; exact hc)
  intro hmem
  set r := (c - a) / (b - c) with hr
  have key : r * (b - c) = c - a := by rw [hr]; field_simp
  by_cases h0 : r = 0
  · apply hca
    rw [h0, zero_mul] at key
    linear_combination -key
  · apply hb
    have hbc_mem : b - c ∈ K := by
      have he : b - c = (c - a) / r := by rw [eq_div_iff h0]; linear_combination key
      rw [he]; exact K.div_mem (K.sub_mem hc ha) hmem
    have he2 : b = (b - c) + c := by ring
    rw [he2]; exact K.add_mem hbc_mem hc

/-- **The subfield pinning step (`r ∉ K ⟹ pinned`) — the genuine multi-round content.** For the family
`affineScheme (G0pow g)` with `⟨g⟩ = K^×` (the carried hypothesis `hHK`, `K` a subfield), if the
cross-ratio `r = (c−a)/(b−c) ∉ K` then `γ` is forced-triangle-pinned by `α, β` (two reachable points). The
arithmetic: from the ratio step's `hh : h ∈ K^×` and `hw : 1+r(1−h) ∈ K^×`, if `h ≠ 1` then `1−h ∈ K^×`
and `r = (r(1−h))/(1−h) ∈ K` — contradicting `r ∉ K`; so `h = 1`. Size-free (works for any `|K| ≥ 2`),
unlike the one-round `H={±1}` case. -/
theorem dominatorReachable_G0pow_subfield_step (hd : d ≠ 0) (g : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd g)
    (K : Subfield (GaloisField p d))
    (hHK : ∀ h : GaloisField p d, (∃ k : ℤ, (g : GaloisField p d) ^ k = h) ↔ (h ∈ K ∧ h ≠ 0))
    {T : Finset (Fin (p ^ d))} {α β γ : Fin (p ^ d)}
    (hca : fieldOf hd γ ≠ fieldOf hd α) (hbc : fieldOf hd β ≠ fieldOf hd γ)
    (hr : (fieldOf hd γ - fieldOf hd α) / (fieldOf hd β - fieldOf hd γ) ∉ K)
    (hα : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T α)
    (hβ : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T β) :
    DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme T γ := by
  refine dominatorReachable_G0pow_ratio_step hd g hneg hca hbc hα hβ (fun h hh hw => ?_)
  rw [hHK] at hh hw
  obtain ⟨hhK, _⟩ := hh
  obtain ⟨hwK, _⟩ := hw
  by_contra hne1
  apply hr
  set r := (fieldOf hd γ - fieldOf hd α) / (fieldOf hd β - fieldOf hd γ) with hrdef
  have h1h : (1 : GaloisField p d) - h ∈ K := K.sub_mem K.one_mem hhK
  have h1h0 : (1 : GaloisField p d) - h ≠ 0 := sub_ne_zero.mpr (fun he => hne1 he.symm)
  have hrh : r * (1 - h) ∈ K := by
    have he : r * (1 - h) = (1 + r * (1 - h)) - 1 := by ring
    rw [he]; exact K.sub_mem hwK K.one_mem
  have hrr : r = r * (1 - h) / (1 - h) := by rw [mul_div_assoc, div_self h1h0, mul_one]
  rw [hrr]; exact K.div_mem hrh h1h

/-- **The 2-round closure for the subfield family `H = K^×` — a genuine MULTI-ROUND closure of a
larger-`H` cyclotomic scheme.** For `affineScheme (G0pow g)` with `⟨g⟩ = K^×` (`hHK`, `K` a subfield),
a base `{α, β}` of two distinct `K`-points closes all of `F_q` from a non-`K` witness (`hext`, present
whenever `K ⊊ F_q`, i.e. `d ≥ 2` for `K = F_p`): **round 1** pins every non-`K` point by `α, β`
(`ratio_not_mem_num_out`), **round 2** pins every `K` point by `α` and a round-1 non-`K` point
(`ratio_not_mem_denom_out`). This discharges the seal's `hclo` for the whole `K^×` family — the first
genuinely multi-round (`|H| > 2`) closure, contrasting the one-round `H={±1}` case. The carried `hHK` and
`hext` are field facts; the instantiation (`K = F_p`, `g` a generator of `F_p^×`, `θ` any non-prime-field
element) is the field-theory follow-on. -/
theorem dominatorReachable_G0pow_subfield (hd : d ≠ 0) (g : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd g)
    (K : Subfield (GaloisField p d))
    (hHK : ∀ h : GaloisField p d, (∃ k : ℤ, (g : GaloisField p d) ^ k = h) ↔ (h ∈ K ∧ h ≠ 0))
    {α β : Fin (p ^ d)} (hαK : fieldOf hd α ∈ K) (hβK : fieldOf hd β ∈ K) (hαβ : α ≠ β)
    (hext : ∃ w : Fin (p ^ d), fieldOf hd w ∉ K) :
    ∀ v : Fin (p ^ d),
      DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme {α, β} v := by
  have hinj := fieldOf_injective (p := p) (d := d) hd
  have hαr : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme {α, β} α :=
    DominatorReachable.base (Finset.mem_insert_self α {β})
  have hβr : DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme {α, β} β :=
    DominatorReachable.base (Finset.mem_insert_of_mem (Finset.mem_singleton_self β))
  have round1 : ∀ w : Fin (p ^ d), fieldOf hd w ∉ K →
      DominatorReachable (affineScheme (G0pow hd g) hneg).toAssociationScheme {α, β} w := by
    intro w hwK
    have hwα : fieldOf hd w ≠ fieldOf hd α := fun h => hwK (by rw [h]; exact hαK)
    have hwβ : fieldOf hd β ≠ fieldOf hd w := fun h => hwK (by rw [← h]; exact hβK)
    exact dominatorReachable_G0pow_subfield_step hd g hneg K hHK hwα hwβ
      (ratio_not_mem_num_out hαK hβK hwK (fun h => hαβ (hinj h))) hαr hβr
  obtain ⟨θ, hθK⟩ := hext
  have hθr := round1 θ hθK
  intro v
  by_cases hvK : fieldOf hd v ∈ K
  · by_cases hvα : v = α
    · rw [hvα]; exact hαr
    by_cases hvβ : v = β
    · rw [hvβ]; exact hβr
    have hvα' : fieldOf hd v ≠ fieldOf hd α := fun h => hvα (hinj h)
    have hθv : fieldOf hd θ ≠ fieldOf hd v := fun h => hθK (by rw [h]; exact hvK)
    exact dominatorReachable_G0pow_subfield_step hd g hneg K hHK hvα' hθv
      (ratio_not_mem_denom_out hαK hθK hvK hvα') hαr hθr
  · exact round1 v hvK

/-! #### The genuine F2b separation crux + seal capstone, over `G0pow β` (the rank-≥3 leak candidate)

`CyclicAffineSeparates` / `reachesRigidOrCameron_viaCyclicSeparation` (above) are stated over
`cyclicAffineScheme = affineScheme (G0cyc …)`, which is the **degenerate rank-2 `K_{p^d}`** (full
multiplicative generator ⟹ transitive ⟹ complete graph; `CyclicAffineSeparates` is *false* there — no
bounded base discretizes `K_q`). The genuine rank-≥3 cyclotomic leak candidate — the one on which the
Frobenius step-1 work (`relOfPair_frobPerm_hom`) and the concrete `clebschWitness_irreducible` actually
live — is `affineScheme (G0pow hd β)` for a **proper** `β = α^m`. These re-target the conditional seal
capstone to that scheme, so a proof of the separation closes the seal over the genuine leak family, not
over the degenerate `K_q`. Pure re-instantiation of `reachesRigidOrCameron_viaAffineIrreducible` at
`G₀ := G0pow hd β` (mirroring the cyclic version verbatim, scheme swapped). -/

/-- The **depth-2 difference (multi-coset-intersection) count** for vertex `u` over `affineScheme (G0pow hd β)`,
at relation-profile `ρ` and relation `b`: the number of `z ≠ u` whose difference-relation to every base point
`t ∈ T` is `ρ t` and to `u` is `b`. (= `|⋂_{t∈T}(t + C_{ρt}) ∩ (u − C_b)|` in the coset notation.)
`PowAffineSeparates` is its injectivity in `u`; `discrete_affineScheme_of_twoRoundDiffSeparates` consumes it. -/
noncomputable def affineDepth2Count (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) (T : Finset (Fin (p ^ d)))
    (u : Fin (p ^ d))
    (ρ : Fin (p ^ d) → Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1))
    (b : Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1)) : ℕ :=
  (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
    (∀ t ∈ T, (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).relOfPair (affineE 0)
        (affineE (affineE.symm z - affineE.symm t)) = ρ t)
    ∧ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).relOfPair (affineE 0)
        (affineE (affineE.symm z - affineE.symm u)) = b)).card

/-- **The genuine F2b separation crux, over the proper cyclic subgroup `G0pow β`.** The depth-2
difference (multi-coset-intersection) profile `affineDepth2Count` is injective over `affineScheme (G0pow hd β)`
from some bounded base `T`. Mirrors `CyclicAffineSeparates` but over the rank-≥3 leak candidate (`G0pow`), not
the degenerate rank-2 `K_q` (`G0cyc`). This is the Frobenius `s(C)` bound for the proper-subgroup cyclotomic
scheme — the genuine uncited open core (F2b). -/
def PowAffineSeparates (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) (bound : Nat) : Prop :=
  ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
    ∀ u u' : Fin (p ^ d),
      (∀ ρ b, affineDepth2Count hd β hβneg T u ρ b = affineDepth2Count hd β hβneg T u' ρ b) → u = u'

/-- **The seal on the genuine cyclotomic family `G0pow β`, reduced to the single crux `PowAffineSeparates`.**
The `G0pow` analogue of `reachesRigidOrCameron_viaCyclicSeparation`, re-targeted from the degenerate rank-2
`cyclicAffineScheme` (`G0cyc`) to the rank-≥3 leak candidate `affineScheme (G0pow hd β)` — the scheme on
which the Frobenius step-1 work and the `clebschWitness_irreducible` actually live.

**⚠️ CONDITIONAL — NOT the closed seal.** Carries `hClassify` (G3, cited), `hne`/`hrank` (genuine rank-≥2,
discharged per instance — e.g. via `G0pow_irreducible_of_adjoin`/`clebschWitness_irreducible`), `hImprim`
(landed/earned, tower-reducible), and the **open** `hsep : PowAffineSeparates` (the Frobenius `s(C)`
counting, F2b — uncited; `relOfPair_frobPerm_hom` is its step 1). Closing the seal on this genuine family
⟺ proving `PowAffineSeparates`, which is open `s(C)` mathematics. -/
theorem reachesRigidOrCameron_viaPowSeparation (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1),
        ∃ v w, (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank)
    (hsep : PowAffineSeparates hd β hβneg bound)
    (hImprim : ¬ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) := by
  refine reachesRigidOrCameron_viaAffineIrreducible (G₀ := G0pow hd β) hClassify
    (neg_mem_G0pow hd β hβneg) hne hrank ?_ hImprim
  rintro ⟨-, -⟩
  obtain ⟨T, hcard, hTsep⟩ := hsep
  exact ⟨T, hcard, discrete_affineScheme_of_twoRoundDiffSeparates (G0pow hd β)
    (neg_mem_G0pow hd β hβneg) hTsep⟩

/-- **Field-generation from element order** (the finite-field core for cyclotomic witnesses). If `β ∈ F_qˣ`
has multiplicative order `r` and **no proper divisor** `e ∣ d` has `r ∣ p^e − 1`, then `β` generates `F_q`
as an `F_p`-algebra (`Algebra.adjoin = ⊤`). Proof: `K' := F_p⟮β⟯` is a subfield of size `p^e`
(`e := finrank ∣ d`) containing the order-`r` element `β`, so `β^(p^e) = β` ⟹ `r ∣ p^e − 1`; the hypothesis
forces `e = d`, hence `K' = ⊤`. Feeds `G0pow_irreducible_of_adjoin` for a concrete cyclotomic witness. -/
theorem adjoin_eq_top_of_orderOf (hd : d ≠ 0) (β : (GaloisField p d)ˣ) (r : ℕ)
    (hr : orderOf β = r)
    (hcop : ∀ e : ℕ, e ∣ d → e < d → ¬ r ∣ (p ^ e - 1)) :
    Algebra.adjoin (ZMod p) {(β : GaloisField p d)} = ⊤ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set K' : IntermediateField (ZMod p) (GaloisField p d) :=
    IntermediateField.adjoin (ZMod p) {(β : GaloisField p d)} with hK'def
  haveI : Fintype K' := Fintype.ofFinite _
  have hβmem : (β : GaloisField p d) ∈ K' := IntermediateField.mem_adjoin_simple_self _ _
  set e := Module.finrank (ZMod p) K' with hedef
  have hed : e ∣ d := by
    have h1 := IntermediateField.finrank_dvd_of_le_right (show K' ≤ ⊤ from le_top)
    rw [IntermediateField.finrank_top', GaloisField.finrank p hd] at h1
    exact h1
  have hcard : Fintype.card K' = p ^ e := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K'), ZMod.card, ← hedef]
  have hβ0 : (β : GaloisField p d) ≠ 0 := Units.ne_zero β
  have hpow : (β : GaloisField p d) ^ (p ^ e) = (β : GaloisField p d) := by
    have hb := FiniteField.pow_card (⟨(β : GaloisField p d), hβmem⟩ : K')
    rw [hcard] at hb
    have hb' := congrArg (fun x : K' => (x : GaloisField p d)) hb
    simpa using hb'
  have hpe1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hrdvd : r ∣ p ^ e - 1 := by
    rw [← hr, ← orderOf_units]
    apply orderOf_dvd_of_pow_eq_one
    have hmul : (β : GaloisField p d) * (β : GaloisField p d) ^ (p ^ e - 1)
        = (β : GaloisField p d) * 1 := by
      rw [mul_one, ← pow_succ', Nat.sub_add_cancel hpe1, hpow]
    exact mul_left_cancel₀ hβ0 hmul
  have hed2 : e = d :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hed)
      (Nat.not_lt.1 (fun h => hcop e hed h hrdvd))
  have hK'top : K' = ⊤ := by
    have hfr : Module.finrank (ZMod p) K' = Module.finrank (ZMod p) (GaloisField p d) := by
      rw [← hedef, hed2, GaloisField.finrank p hd]
    have h2 : K'.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hfr
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ K'.toSubmodule := by rw [h2]; exact Submodule.mem_top
    exact hx
  have hconv : K'.toSubalgebra = Algebra.adjoin (ZMod p) {(β : GaloisField p d)} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)
  rw [← hconv, hK'top, IntermediateField.top_toSubalgebra]

/-- The chosen generator `fqGen` has order `p^d − 1` (= `|F_qˣ|`), since it generates the cyclic unit group. -/
theorem orderOf_fqGen (hd : d ≠ 0) : orderOf (fqGen : (GaloisField p d)ˣ) = p ^ d - 1 := by
  haveI : DecidableEq (GaloisField p d) := Classical.decEq _
  rw [orderOf_eq_card_of_forall_mem_zpowers fqGen_spec, Nat.card_eq_fintype_card, Fintype.card_units]
  congr 1
  rw [← Nat.card_eq_fintype_card, GaloisField.card p d hd]

/-- **The cyclotomic witness family** — `G0pow (fqGen^m)` is irreducible whenever `β = fqGen^m` has order `r`
that field-generates (no proper divisor `e ∣ d` has `r ∣ p^e − 1`). Combines `G0pow_irreducible_of_adjoin`
with `adjoin_eq_top_of_orderOf`. For a *proper* `m` (so `⟨fqGen^m⟩ ⊊ F_qˣ`) this is the genuine rank-≥3
cyclotomic leak candidate (vs `G0cyc = G0pow fqGen` = rank-2 `K_q`). -/
theorem G0pow_pow_irreducible (hd : d ≠ 0) (m r : ℕ)
    (hr : orderOf ((fqGen : (GaloisField p d)ˣ) ^ m) = r)
    (hcop : ∀ e : ℕ, e ∣ d → e < d → ¬ r ∣ (p ^ e - 1)) :
    G₀Irreducible (G0pow hd ((fqGen : (GaloisField p d)ˣ) ^ m)) :=
  G0pow_irreducible_of_adjoin hd _ (adjoin_eq_top_of_orderOf hd _ r hr hcop)

/-! #### Separation obstruction — Frobenius is a configuration automorphism (the `Ĝ ⊋ G` gap, separation step 1)

The Frobenius permutation `frobPerm` of `V` (additive, the transported `frobCoord`) **preserves the scheme's
relation partition** (`relOfPair_frobPerm_hom`): it is an automorphism of the coherent configuration that the
group `V ⋊ G0pow β` does **not** realize. This is **part of** the concrete `Ĝ ⊋ G` separability gap — a
**Galois** member of the WL-closure symmetry group the actual group misses. **⚠️ It is not the whole gap:** for
the index-3 / Clebsch witness `Ĝ/G` is an `S₃`-on-relations and Frobenius realizes only a `Z₂` of it (the
amorphic remainder is not Galois; seal-handoff §G2 board). So `frobPerm` witnesses the gap is non-trivial (a
lower bound on `Ĝ/G`), but the gap's mechanism is *not* Frobenius in general — the honest open kernel is the
mechanism-agnostic `PowAffineSeparates`, and the general crux is the relation-level P3. The mechanism:
`frobCoord` **normalizes** `G0pow β`
(`frobCoord_conj_sigmaPow`: `frobCoord·σ·frobCoord⁻¹ = σ^p ∈ ⟨σ⟩`), and Frobenius is additive, so it carries
`G0pow β`-orbits of differences to `G0pow β`-orbits of differences. **General-theorem shadow:** "a normalizing
algebraic automorphism is a configuration automorphism," the exact shape of the general `s(C)` obstruction. -/

/-- `φ ∘ (mul β) ∘ φ⁻¹ = (mul β)^p` for an arbitrary unit `β` (generalizes `frobLinear_conj_mulUnit`). -/
private theorem frobLinear_conj_mulUnit' (β : (GaloisField p d)ˣ) :
    frobLinear (p := p) (d := d) * mulUnitHom β * (frobLinear)⁻¹ = (mulUnitHom β) ^ p := by
  ext x
  have hinv : frobLinear (p := p) (d := d) ((frobLinear (p := p) (d := d))⁻¹ x) = x := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [← map_pow, mulUnitHom_apply, Units.val_pow_eq_pow_val, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, mulUnitHom_apply, frobLinear_mul, hinv]

/-- **`frobCoord` conjugates `σ_β` to `σ_β^p`** (generalizes `frobCoord_conj_sigmaCyc`) — so `frobCoord`
normalizes `G0pow β = ⟨σ_β⟩`. -/
theorem frobCoord_conj_sigmaPow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) :
    frobCoord (p := p) hd * sigmaPow hd β * (frobCoord hd)⁻¹ = (sigmaPow hd β) ^ p := by
  rw [frobCoord, sigmaPow, ← map_inv, ← map_mul, ← map_mul, frobLinear_conj_mulUnit', map_pow]

/-- **`frobCoord` normalizes `G0pow β`** (forward inclusion): `g ∈ G0pow β ⟹ frobCoord·g·frobCoord⁻¹ ∈ G0pow β`.
From `frobCoord_conj_sigmaPow` (`σ ↦ σ^p`) and conjugation distributing over `zpow`. -/
theorem frobCoord_conj_mem_G0pow (hd : d ≠ 0) (β : (GaloisField p d)ˣ) {g}
    (hg : g ∈ G0pow hd β) : frobCoord hd * g * (frobCoord hd)⁻¹ ∈ G0pow hd β := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hconj : frobCoord hd * g * (frobCoord hd)⁻¹
      = (frobCoord hd * sigmaPow hd β * (frobCoord hd)⁻¹) ^ k := by
    rw [← hk, ← MulAut.conj_apply, ← MulAut.conj_apply, ← map_zpow]
  rw [hconj, frobCoord_conj_sigmaPow]
  exact Subgroup.zpow_mem _ (pow_mem (Subgroup.mem_zpowers _) p) k

/-- The **Frobenius permutation** of `V = F_p^d` — the additive automorphism `frobCoord` transported to
`Fin (p^d)` (linear part `frobCoord`, zero translation). -/
noncomputable def frobPerm (hd : d ≠ 0) : Equiv.Perm (Fin (p ^ d)) :=
  affinePermFin (frobCoord hd) 0

/-- The difference-coordinate of `frobPerm` is `frobCoord` of the coordinate (additive on differences). -/
theorem affineE_symm_frobPerm (hd : d ≠ 0) (x : Fin (p ^ d)) :
    affineE.symm (frobPerm hd x) = frobCoord hd (affineE.symm x) := by
  rw [frobPerm, affinePermFin_apply, add_zero, Equiv.symm_apply_apply]

/-- **The Frobenius permutation preserves the relation partition** (separation step 1, the configuration
automorphism). If `(x,y)` and `(x',y')` lie in the same relation, so do their `frobPerm`-images — because
`frobCoord` normalizes `G0pow β` and is additive. So `frobPerm` is an automorphism of the coherent
configuration not realized by `V ⋊ G0pow β` — the concrete `Ĝ ⊋ G` separability gap. -/
theorem relOfPair_frobPerm_hom (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G0pow hd β) {x y x' y' : Fin (p ^ d)}
    (h : (affineScheme (G0pow hd β) hneg).relOfPair x y
        = (affineScheme (G0pow hd β) hneg).relOfPair x' y') :
    (affineScheme (G0pow hd β) hneg).relOfPair (frobPerm hd x) (frobPerm hd y)
      = (affineScheme (G0pow hd β) hneg).relOfPair (frobPerm hd x') (frobPerm hd y') := by
  rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff] at h ⊢
  obtain ⟨g₀, hg₀, hg⟩ := h
  refine ⟨frobCoord hd * g₀ * (frobCoord hd)⁻¹, frobCoord_conj_mem_G0pow hd β hg₀, ?_⟩
  have hinv : (frobCoord hd)⁻¹ (frobCoord hd (affineE.symm y' - affineE.symm x'))
      = affineE.symm y' - affineE.symm x' := by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; exact (LinearEquiv.eq_symm_apply 1).mp rfl
  rw [affineE_symm_frobPerm, affineE_symm_frobPerm, affineE_symm_frobPerm, affineE_symm_frobPerm,
    ← map_sub (frobCoord hd), ← map_sub (frobCoord hd), LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hinv, hg]

/-! #### Frobenius is killed by a field-generating base — the Galois sub-part of the gap

A power of Frobenius `φ : x ↦ x^p` fixing a field-generating set is `1`. Concretely: individualizing a
Γ-breaking (field-generating) base removes the Galois symmetry `φ` from the gap.

> **⚠️ SCOPE CORRECTION (2026-06-10).** An earlier framing treated this as "step 2 of 4" of a *Frobenius*
> separation proof whose open crux was "every profile-twin is a Frobenius image" (`TwinsAreFrobenius`, since
> **removed**). That premise is **false**: the cyclotomic separability gap `Ĝ/G` is the full WL-closure
> relation-symmetry group — for the index-3 / Clebsch witness it is an **`S₃`-on-relations**, of which the
> Galois `φ` realizes only a `Z₂` (`φ` acts as `i ↦ 2i mod 3`, a transposition; seal-handoff §G2 board). So
> killing Frobenius kills only the Galois `Z₂` *sub-part* of the gap, **not** the amorphic remainder. These
> lemmas are correct and characterize that Galois sub-part (a genuine lower bound on `Ĝ/G`), but they are
> **insufficient for separation** — the honest, mechanism-agnostic open kernel is `PowAffineSeparates`
> itself, and the right *general* crux is the relation-level P3 (`persistent twin ⟹ ClosedSubset ⟹
> imprimitive`), agnostic to whether the gap is Galois or amorphic. Do not rebuild a Frobenius-only
> separation route.
-/

/-- `frobLinear^j` acts as `x ↦ x^(p^j)` (iterating Frobenius `x ↦ x^p`). -/
theorem frobLinear_pow_apply (j : ℕ) (x : GaloisField p d) :
    (frobLinear (p := p) (d := d) ^ j) x = x ^ p ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, frobLinear_apply, ← pow_mul, ← pow_succ]

/-- **Separation step 2 — a Frobenius power fixing a field-generating set is the identity.** If
`frobLinear^j` (`= x ↦ x^(p^j)`) fixes every element of `S` and `S` generates `F_q` as an `F_p`-algebra
(`Algebra.adjoin (ZMod p) S = ⊤`), then `frobLinear^j = 1`. The fixed points `{x | x^(p^j) = x}` form a
subalgebra (closed under `+` by the freshman's dream `add_pow_char_pow`, containing `F_p` by
`ZMod.pow_card_pow`), so if it contains a generating `S` it is all of `F_q`. This is the precise sense in
which a **Γ-breaking** (field-generating) base removes the Galois degeneracy: no nontrivial Frobenius power
survives it. (The cyclic instance of "base-homogeneous gap ⟹ invariant sub-structure"; for cyclic `G₀` the
sub-structure is a subfield / `Γ`-eigenspace.) -/
theorem frobLinear_pow_eq_one_of_adjoin {j : ℕ} {S : Set (GaloisField p d)}
    (hgen : Algebra.adjoin (ZMod p) S = ⊤)
    (hfix : ∀ s ∈ S, (frobLinear (p := p) (d := d) ^ j) s = s) :
    frobLinear (p := p) (d := d) ^ j = 1 := by
  -- The fixed points `x^(p^j) = x` form a subalgebra `K`.
  set K : Subalgebra (ZMod p) (GaloisField p d) :=
    { carrier := {x : GaloisField p d | x ^ p ^ j = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, mul_pow] at *; rw [ha, hb]
      one_mem' := by simp only [Set.mem_setOf_eq, one_pow]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_pow_char_pow] at *; rw [ha, hb]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        exact zero_pow (pow_ne_zero j (Fact.out : p.Prime).pos.ne')
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, ← map_pow, ZMod.pow_card_pow] } with hKdef
  have hSK : S ⊆ (K : Set (GaloisField p d)) := by
    intro s hs
    have hs' := hfix s hs
    rw [frobLinear_pow_apply] at hs'
    exact hs'
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hgen]; exact Algebra.adjoin_le hSK
  ext x
  have hx : x ∈ K := by rw [hKtop]; exact Algebra.mem_top
  have hxfix : x ^ p ^ j = x := hx
  rw [frobLinear_pow_apply, hxfix]
  rfl

/-! ##### Step 2 — lifting the field statement to `frobPerm` on scheme points (the iso alignment)

Step 2 above is a clean *field* statement (`frobLinear^j = 1` on `F_q`). The separation argument needs it on
**scheme points** (`frobPerm^j = 1` on `Fin (p^d)`). The model uses two isos — `affineE : F_p^d ≃ Fin(p^d)`
(scheme points) and `efield : F_q ≃ F_p^d` (the field). Their composite `x ↦ efield⁻¹(affineE⁻¹ x)` is the
**field coordinate** of a scheme point, and under it `frobPerm` acts as `frobLinear` (both are "raise to the
`p`-th power"). These lemmas make that alignment explicit and lift the field statement to a directly-usable
`frobPerm^j = 1` (the scheme-point form of "a field-generating base kills Galois"). See the ⚠️ scope
correction above: this removes only the Galois `Z₂` sub-part of the gap, not the full amorphic remainder. -/

/-- `frobCoord^j` is `frobLinear^j` conjugated through `efield` (`frobCoord = conjHom frobLinear`, `conjHom`
a monoid hom). The field-coordinate alignment of the linear part. -/
theorem frobCoord_pow_apply (hd : d ≠ 0) (j : ℕ) (u : Fin d → ZMod p) :
    (frobCoord hd ^ j) u = efield hd ((frobLinear (p := p) (d := d) ^ j) ((efield hd).symm u)) := by
  rw [frobCoord, ← map_pow, conjHom_apply]

/-- `affineE.symm (frobPerm^j x) = (frobCoord^j) (affineE.symm x)` — the `j`-fold iterate of
`affineE_symm_frobPerm` (`frobPerm` is the additive `frobCoord` transported, zero translation). -/
theorem affineE_symm_frobPerm_pow (hd : d ≠ 0) (j : ℕ) (x : Fin (p ^ d)) :
    affineE.symm ((frobPerm hd ^ j) x) = (frobCoord hd ^ j) (affineE.symm x) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (frobPerm hd) k, Equiv.Perm.mul_apply, affineE_symm_frobPerm, ih,
      ← LinearEquiv.mul_apply, ← pow_succ']

/-- **A Frobenius power fixing a field-generating base is the identity permutation (scheme-point form).** If
the field coordinates `efield⁻¹(affineE⁻¹ t)` of the base `T` generate `F_q` (Γ-breaking) and `frobPerm^j`
fixes `T` pointwise, then `frobPerm^j = 1`. Lifts `frobLinear_pow_eq_one_of_adjoin` to `Fin (p^d)` via the
alignment lemmas. Removes the **Galois `Z₂` sub-part** of the separability gap; insufficient for separation on
its own (the full gap `Ĝ/G` is amorphic, larger than Galois — see the ⚠️ scope correction above). -/
theorem frobPerm_pow_eq_one_of_adjoin (hd : d ≠ 0) {j : ℕ} {T : Finset (Fin (p ^ d))}
    (hgen : Algebra.adjoin (ZMod p)
        ((fun t : Fin (p ^ d) => (efield hd).symm (affineE.symm t)) '' (↑T)) = ⊤)
    (hfix : ∀ t ∈ T, (frobPerm (p := p) hd ^ j) t = t) :
    frobPerm (p := p) hd ^ j = 1 := by
  have hfl : frobLinear (p := p) (d := d) ^ j = 1 := by
    refine frobLinear_pow_eq_one_of_adjoin hgen ?_
    rintro s ⟨t, ht, rfl⟩
    have h1 : (frobCoord hd ^ j) (affineE.symm t) = affineE.symm t := by
      rw [← affineE_symm_frobPerm_pow, hfix t ht]
    have h2 := frobCoord_pow_apply hd j (affineE.symm t)
    rw [h1] at h2
    have h3 := congrArg (efield hd).symm h2
    rw [LinearEquiv.symm_apply_apply] at h3
    exact h3.symm
  refine Equiv.Perm.ext (fun x => ?_)
  apply affineE.symm.injective
  rw [affineE_symm_frobPerm_pow, frobCoord_pow_apply, hfl]
  show efield hd ((efield hd).symm (affineE.symm x)) = affineE.symm x
  rw [LinearEquiv.apply_symm_apply]

/-! #### The module-adjoin "kill" lemma — the `ΓL` generalization (linear-algebra half)

`frobPerm_pow_eq_one_of_adjoin` kills only the **Galois** (Frobenius) sub-part of the `Ĝ⊋G` gap. The
`Probe_ModuleAdjoin_AmorphicGapIsSemilinear` validation showed the *full* gap is semilinear (`ΓL₁`), with the
non-Galois remainder being `mult-by-α ∈ GL`. Both `mult-by-c` and Frobenius are `F_p`-**linear**, so the whole
gap lives in `GL_{F_p}(F_q)`, and the clean unified "kill" statement is purely linear: an `F_p`-linear
automorphism fixing a **spanning** base is the identity. (The landed Frobenius lemma trades this spanning
hypothesis for the weaker field-generation `Algebra.adjoin = ⊤`, valid only because Frobenius is
*multiplicative*; `mult-by-c` is not, so for the whole gap the spanning/linear form is the right one.) -/

/-- **Module-adjoin (linear "kill" half, the `ΓL₁` generalization of `frobPerm_pow_eq_one_of_adjoin`).** ANY
`F_p`-linear automorphism `g₀` whose induced affine permutation (zero translation) fixes a base `T` pointwise,
where the coordinate vectors `affineE.symm '' T` **span** `F_p^d`, is the identity permutation. Since
`ΓL₁ ⊆ GL_{F_p}`, individualizing a spanning (`O(d) = O(log n)`) base kills the entire `ΓL₁` separability gap —
the linear-algebra half of the corrected module-adjoin route. -/
theorem affinePermFin_eq_one_of_span
    {g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)} {T : Finset (Fin (p ^ d))}
    (hspan : Submodule.span (ZMod p)
        ((fun t : Fin (p ^ d) => affineE.symm t) '' (↑T : Set (Fin (p ^ d)))) = ⊤)
    (hfix : ∀ t ∈ T, affinePermFin g₀ (0 : Fin d → ZMod p) t = t) :
    affinePermFin g₀ (0 : Fin d → ZMod p) = 1 := by
  have hg0 : (g₀ : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p)) = LinearMap.id := by
    refine LinearMap.ext_on hspan ?_
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h := hfix t (Finset.mem_coe.mp ht)
    rw [affinePermFin_apply, add_zero] at h
    have h2 := congrArg affineE.symm h
    rw [Equiv.symm_apply_apply] at h2
    simpa using h2
  have hg1 : g₀ = 1 := by
    refine LinearEquiv.ext (fun v => ?_)
    have hv := LinearMap.congr_fun hg0 v
    simpa using hv
  rw [hg1]; exact affinePermFin_one

/-! #### The reduction — `PowAffineSeparates` from "twins are semilinear" (cited) + the kill lemma

With the linear "kill" lemma `affinePermFin_eq_one_of_span`, the open counting crux `PowAffineSeparates`
reduces to the **cited `s(C)`-content**: *every depth-2 profile-twin is realised by an `F_p`-linear automorphism
fixing the base*. That is the operational form of **cyclotomic 2-separability** — Ponomarenko, *On the
separability of cyclotomic schemes over finite field* (arXiv:2006.13592), Theorem 1.1: every cyclotomic scheme
over a finite field is 2-separable, with finitely many explicit exceptions (F₁₆ Clebsch `(2,4)` and F₂₅ `(5,2)`
are NOT exceptions). Carried as a theorem-statement **hypothesis** (axiom hygiene — cited results are hypotheses,
never fresh `axiom`s). The net: the raw counting `PowAffineSeparates` is replaced by the cleaner, cited
`TwinsAreSemilinear`. -/

/-- **"Twins are semilinear" — the cited `s(C)`-half (cyclotomic 2-separability), operational form.** Every
depth-2 profile-twin `(u, u')` from the base `T` is realised by an `F_p`-linear automorphism `g₀` (zero
translation — faithful when the base pins the origin, as a `T`-fixing automorphism of a translation scheme does)
that fixes `T` pointwise and maps `u` to `u'`. Justified by cyclotomic 2-separability (Ponomarenko,
arXiv:2006.13592, Thm 1.1); the realiser is stated `F_p`-linear because that is exactly what the kill lemma
`affinePermFin_eq_one_of_span` consumes (and `ΓL₁ ⊆ GL_{F_p}`, so the cited `ΓL₁` realiser is a fortiori one). -/
def TwinsAreSemilinear (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) (T : Finset (Fin (p ^ d))) : Prop :=
  ∀ u u' : Fin (p ^ d),
    (∀ ρ b, affineDepth2Count hd β hβneg T u ρ b = affineDepth2Count hd β hβneg T u' ρ b) →
    ∃ g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p),
      (∀ t ∈ T, affinePermFin g₀ (0 : Fin d → ZMod p) t = t) ∧
      affinePermFin g₀ (0 : Fin d → ZMod p) u = u'

/-- **The reduction — `PowAffineSeparates` from `TwinsAreSemilinear` on a SPANNING base.** If `T` is spanning
(`affineE.symm '' T` linearly spans `F_p^d`) and twins from `T` are semilinear, then `T` separates: a twin's
realiser `g₀` fixes the spanning `T`, so by `affinePermFin_eq_one_of_span` its affine perm is the identity,
forcing `u = u'`. This reduces the open counting crux `PowAffineSeparates` to the cited `TwinsAreSemilinear`
(cyclotomic 2-separability) — the "close" half of the module-adjoin route, modulo exhibiting a bounded spanning
base (a basis image, `card = d ≤ bound`). -/
theorem powAffineSeparates_of_twinsAreSemilinear (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β) {bound : Nat}
    {T : Finset (Fin (p ^ d))} (hcard : T.card ≤ bound)
    (hspan : Submodule.span (ZMod p)
        ((fun t : Fin (p ^ d) => affineE.symm t) '' (↑T : Set (Fin (p ^ d)))) = ⊤)
    (htwin : TwinsAreSemilinear hd β hβneg T) :
    PowAffineSeparates hd β hβneg bound := by
  refine ⟨T, hcard, fun u u' hprof => ?_⟩
  obtain ⟨g₀, hfix, hmap⟩ := htwin u u' hprof
  rw [affinePermFin_eq_one_of_span hspan hfix] at hmap
  simpa using hmap

/-- **The seal on the cyclotomic family, reduced to the cited `TwinsAreSemilinear` + a spanning base.**
Composes `powAffineSeparates_of_twinsAreSemilinear` (the kill-lemma reduction) into
`reachesRigidOrCameron_viaPowSeparation`. So the seal on `affineScheme (G0pow β)` follows from: `hClassify`
(G3, cited), `hne`/`hrank` (per-instance, e.g. `clebschWitness_irreducible`), `hImprim` (landed/earned), a
**spanning** base `T` (`card ≤ bound`), and **`TwinsAreSemilinear`** — the latter being the cited cyclotomic
2-separability (Ponomarenko arXiv:2006.13592 Thm 1.1, which covers F₁₆/F₂₅). The open counting `PowAffineSeparates`
is gone, replaced by the cited statement; the only remaining build step to a fully unconditional affine slice is
exhibiting the spanning base as a basis image (`card = d ≤ bound`) — mechanical. -/
theorem reachesRigidOrCameron_viaTwinsAreSemilinear (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1),
        ∃ v w, (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank)
    {T : Finset (Fin (p ^ d))} (hcard : T.card ≤ bound)
    (hspan : Submodule.span (ZMod p)
        ((fun t : Fin (p ^ d) => affineE.symm t) '' (↑T : Set (Fin (p ^ d)))) = ⊤)
    (htwin : TwinsAreSemilinear hd β hβneg T)
    (hImprim : ¬ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) :=
  reachesRigidOrCameron_viaPowSeparation hd β hβneg hClassify hne hrank
    (powAffineSeparates_of_twinsAreSemilinear hd β hβneg hcard hspan htwin) hImprim

/-- **A bounded spanning base exists** — the standard basis `Pi.basisFun` of `F_p^d`, transported through
`affineE`: `∃ T`, `card ≤ d`, with `affineE.symm '' T` spanning `F_p^d`. Discharges the `hspan`/`hcard`
hypotheses of `powAffineSeparates_of_twinsAreSemilinear` / `…viaTwinsAreSemilinear` for any `bound ≥ d`. Pure
linear algebra (basis image + `Basis.span_eq`). -/
theorem exists_spanning_base :
    ∃ T : Finset (Fin (p ^ d)), T.card ≤ d ∧
      Submodule.span (ZMod p)
        ((fun t : Fin (p ^ d) => affineE.symm t) '' (↑T : Set (Fin (p ^ d)))) = ⊤ := by
  classical
  refine ⟨Finset.univ.image (fun i : Fin d => affineE ((Pi.basisFun (ZMod p) (Fin d)) i)), ?_, ?_⟩
  · calc (Finset.univ.image (fun i : Fin d => affineE ((Pi.basisFun (ZMod p) (Fin d)) i))).card
        ≤ Finset.univ.card := Finset.card_image_le
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  · have hrw : (fun t : Fin (p ^ d) => affineE.symm t) ''
        (↑(Finset.univ.image (fun i : Fin d => affineE ((Pi.basisFun (ZMod p) (Fin d)) i)))
          : Set (Fin (p ^ d)))
        = Set.range ⇑(Pi.basisFun (ZMod p) (Fin d)) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hrw]
    exact (Pi.basisFun (ZMod p) (Fin d)).span_eq

/-- **The affine cyclotomic slice of the seal, fully reduced to the cited cyclotomic 2-separability.** Picks the
canonical bounded spanning base (`exists_spanning_base`) internally, so the **only** affine-specific open input
is `hcite : ∀ T, TwinsAreSemilinear …` — the *global* form of cyclotomic 2-separability (Ponomarenko
arXiv:2006.13592 Thm 1.1: every profile-twin from *any* base is realised ≡ the scheme is 2-separable; covers
F₁₆/F₂₅). With `d ≤ bound`, the seal on `affineScheme (G0pow β)` follows from {G3 (cited), this citation,
`hne`/`hrank`, `hImprim`} — **no carried counting crux, no spanning-base hypothesis.** The fully-reduced affine
slice. -/
theorem reachesRigidOrCameron_affineSlice (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β)
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin ((affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank + 1),
        ∃ v w, (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rel i v w = true)
    (hrank : 2 ≤ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).rank)
    (hdb : d ≤ bound)
    (hcite : ∀ T : Finset (Fin (p ^ d)), TwinsAreSemilinear hd β hβneg T)
    (hImprim : ¬ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
          ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) := by
  obtain ⟨T, hcard, hspan⟩ := exists_spanning_base (p := p) (d := d)
  exact reachesRigidOrCameron_viaTwinsAreSemilinear hd β hβneg hClassify hne hrank
    (le_trans hcard hdb) hspan (hcite T) hImprim

end CyclicAffine

/-! #### The concrete cyclotomic witness — `F₁₆`, the index-3 Clebsch family

`β = fqGen³` has multiplicative order `5` in `F₁₆ˣ` (order 15), so `⟨β⟩` is the **proper** index-3 subgroup
and `G0pow β` is a genuinely **primitive (rank ≥ 3), small, non-degenerate** affine scheme — the real F2b
leak candidate (NOT the rank-2 `K₁₆ = G0cyc`). Field-generation holds because `5 ∤ 2^e − 1` for the proper
divisors `e ∈ {1,2}` of `4` (so `β ∉ F₂, F₄`). This DEMONSTRATES the witness hypotheses are satisfiable —
the `G0pow`/`G0pow_irreducible` machinery is non-vacuous on a real cyclotomic scheme. (For `p = 2`,
symmetry `neg ∈ G0pow β` is free: `-1 = 1 ∈ ⟨β⟩`.) -/

/-- **The Clebsch witness is irreducible** (primitive). `β = fqGen³` (order 5) field-generates `F₁₆`. -/
theorem clebschWitness_irreducible :
    G₀Irreducible (G0pow (p := 2) (d := 4) (by norm_num) ((fqGen : (GaloisField 2 4)ˣ) ^ 3)) := by
  refine G0pow_pow_irreducible (by norm_num) 3 5 ?_ ?_
  · rw [orderOf_pow, orderOf_fqGen (by norm_num)]; decide
  · intro e he hlt; interval_cases e <;> revert he <;> decide

/-- Symmetry for the Clebsch witness — `neg ∈ G0pow β` (free in characteristic 2, `-1 = 1`). -/
theorem clebschWitness_neg_mem :
    LinearEquiv.neg (ZMod 2) ∈ G0pow (p := 2) (d := 4) (by norm_num) ((fqGen : (GaloisField 2 4)ˣ) ^ 3) := by
  refine neg_mem_G0pow (by norm_num) _ ?_
  have h : (-1 : (GaloisField 2 4)ˣ) = 1 := by
    rw [eq_comm, ← Units.val_inj]; simp [CharTwo.neg_eq]
  rw [h]; exact one_mem _

/-! #### Clebsch as the test instance for the general P3-converse crux

The retracted Frobenius route (`PowAffineSeparates` / `TwinsAreFrobenius`) targeted *this* scheme with a
slice-specific, Galois-keyed separation argument — which failed because the gap `Ĝ/G` here is the amorphic
`S₃`-on-relations, not Galois. The **mechanism-agnostic** `reachesRigidOrCameron_viaPersistentTwinBlock`
(`Cascade.lean`) routes the same primitive instance through the *general* crux
(`PersistentTwinYieldsBlock` = `base-homogeneous twin ⟹ block`) with **no affine/Frobenius machinery** — the
general theorem applies to `clebschScheme` verbatim because it is just a `SchurianScheme`. This is the concrete
demonstration of the reroute (self-detection-plan §11.2): the affine-cyclic slice is *one primitive instance*
of the general P3 converse, not a special case needing its own engine.

**Probe evidence (positive, not a proof).** `clebschScheme` is primitive (`clebschWitness_irreducible`); the
affine probe (seal-handoff §G2 board (g)) measured it recovering at **flat depth 4** — consistent with "no
persistent twin," i.e. the crux's conclusion holding on this instance. Discharging the crux *in Lean* (here or
in general) is the open G2-B research; the realization tool that would prove "no twin ⟹ separates" on it is the
landed `discrete_of_kRoundRelationSeparates`. -/

/-- **The Clebsch index-3 affine scheme on `F₁₆`** — the concrete primitive (rank-≥3), small, non-abelian-residual
instance (`clebschWitness_irreducible`). The test fixture for the general P3 converse. -/
noncomputable def clebschScheme : SchurianScheme (2 ^ 4) :=
  affineScheme (G0pow (p := 2) (d := 4) (by norm_num) ((fqGen : (GaloisField 2 4)ˣ) ^ 3))
    clebschWitness_neg_mem

/-- **The general P3-converse seal capstone, instantiated at the Clebsch scheme.** A *verbatim* specialization
of `reachesRigidOrCameron_viaPersistentTwinBlock` to `clebschScheme` — no affine-specific separation engine, no
Frobenius. It demonstrates that the mechanism-agnostic crux `PersistentTwinYieldsBlock` subsumes the
affine-cyclic slice the retracted `PowAffineSeparates` targeted. Carries the same four inputs (cited `hClassify`,
genuine `hne`/`hrank`, the **open** crux `hCrux`, and `hImprim`); conditional, like its general parent. -/
theorem reachesRigidOrCameron_clebsch_viaPersistentTwinBlock
    {IsLarge : Nat → Prop} {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hne : ∀ i : Fin (clebschScheme.rank + 1), ∃ v w, clebschScheme.rel i v w = true)
    (hrank : 2 ≤ clebschScheme.rank)
    (hCrux : PersistentTwinYieldsBlock clebschScheme IsLarge bound)
    (hImprim : ¬ clebschScheme.toAssociationScheme.IsPrimitive →
        SchemeBlockRecovered (2 ^ 4) clebschScheme ∨ AbelianConsumed (2 ^ 4) clebschScheme) :
    ((SchemeBlockRecovered (2 ^ 4) clebschScheme ∨ AbelianConsumed (2 ^ 4) clebschScheme)
        ∨ SchemeRecoveredByDepth (2 ^ 4) clebschScheme bound)
      ∨ IsCameronScheme (2 ^ 4) clebschScheme :=
  reachesRigidOrCameron_viaPersistentTwinBlock hClassify clebschScheme hne hrank hCrux hImprim

end ChainDescent

