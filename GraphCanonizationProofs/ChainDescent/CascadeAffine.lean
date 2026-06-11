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

end Bridge

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
