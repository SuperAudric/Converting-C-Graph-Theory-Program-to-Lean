import ChainDescent.KernelGauss

/-!
# `C3a` tranche 2, part II — rail structure and the flip-composition lemma

The graph-side half of the kernel supply's ① stack (`KernelSupply.lean` header): the structural facts
about rails (mutual-unique twins ⟹ vertex-disjoint pairs), the emitted permutation's action on rail
endpoints, and the **product lemma** the all-or-nothing gate rides on:

> if the flips of `w` and `w'` both pass `permOf` + `IsColAut`, then
> `flipFunK (w ⊕ w') = flip w ∘ flip w'` — so it passes too.

The crux is the **satisfier bijection** (`satP_conj_flip`): a verified flip `ρ` maps the satisfier
set of `(w', v)` bijectively onto that of `(w ⊕ w', v)` — colours and non-railness are `Aut`-stable,
and `ρ` acts on rail endpoints exactly as the `w`-flip, so the flipped-adjacency conditions
transport. Uniqueness (hence `uniqueFilter`) transports with it (`uniqueMem_transport`), and the
twin-disjointness of rails forces every *touched* vertex to move under a verifying flip
(`touched_ne_of_isColAut`) — which is what rules the identity-default out of the composed table.
-/

namespace ChainDescent
namespace Kernel

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut)
open ChainDescent.Deck (uniqueFilter uniqueFilter_eq_uniqueMem)
open ChainDescent.Fold (uniqueMem uniqueMem_eq_some uniqueMem_transport)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. `uniqueFilter` specification -/

private theorem filter_eq_singleton {P : Fin n → Bool} {w : Fin n} (hw : P w = true)
    (hu : ∀ x, P x = true → x = w) : (List.finRange n).filter P = [w] := by
  have hmem : w ∈ (List.finRange n).filter P := List.mem_filter.mpr ⟨List.mem_finRange w, hw⟩
  have hall : ∀ x ∈ (List.finRange n).filter P, x = w :=
    fun x hx => hu x (List.mem_filter.mp hx).2
  have hnd : ((List.finRange n).filter P).Nodup := (List.nodup_finRange n).filter _
  cases hcase : (List.finRange n).filter P with
  | nil => rw [hcase] at hmem; cases hmem
  | cons a t =>
      have ha : a = w := hall a (by rw [hcase]; exact List.mem_cons_self ..)
      cases t with
      | nil => rw [ha]
      | cons b t' =>
          exfalso
          have hb : b = w := hall b (by
            rw [hcase]
            exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
          rw [hcase] at hnd
          exact (List.nodup_cons.mp hnd).1 ((ha.trans hb.symm) ▸ List.mem_cons_self ..)

theorem uniqueFilter_eq_some_iff {P : Fin n → Bool} {w : Fin n} :
    uniqueFilter P = some w ↔ (P w = true ∧ ∀ x, P x = true → x = w) := by
  constructor
  · intro h
    unfold Deck.uniqueFilter at h
    cases hfil : (List.finRange n).filter P with
    | nil => rw [hfil] at h; simp at h
    | cons a t =>
        cases t with
        | nil =>
            rw [hfil] at h
            have haw : a = w := Option.some.inj h
            have ha : P w = true := by
              rw [← haw]
              exact (List.mem_filter.mp (hfil ▸ List.mem_cons_self ..)).2
            refine ⟨ha, fun x hx => ?_⟩
            have hxmem : x ∈ (List.finRange n).filter P :=
              List.mem_filter.mpr ⟨List.mem_finRange x, hx⟩
            rw [hfil] at hxmem
            simpa [haw] using hxmem
        | cons b t' => rw [hfil] at h; simp at h
  · rintro ⟨hw, hu⟩
    unfold Deck.uniqueFilter
    rw [filter_eq_singleton hw hu]

/-- Transport of `uniqueFilter` along a permutation of the search space. -/
theorem uniqueFilter_transport (σ : Equiv.Perm (Fin n)) {P P' : Fin n → Bool}
    (hP : ∀ w, P' (σ w) = P w) : uniqueFilter P' = (uniqueFilter P).map σ := by
  rw [uniqueFilter_eq_uniqueMem, uniqueFilter_eq_uniqueMem]
  exact uniqueMem_transport σ hP

/-! ## 2. Rail structure — mutual-unique twins are vertex-disjoint pairs -/

theorem mem_rails_iff {adj : AdjMatrix n} {χ : Colouring n} {p : Fin n × Fin n} :
    p ∈ rails adj χ
      ↔ twin adj χ p.1 = some p.2 ∧ twin adj χ p.2 = some p.1 ∧ p.1.val < p.2.val := by
  unfold rails
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨v, -, hv⟩
    cases htw : twin adj χ v with
    | none => rw [htw] at hv; cases hv
    | some w =>
        rw [htw] at hv
        simp only [] at hv
        cases hb : (decide (v.val < w.val) && (twin adj χ w == some v))
        · rw [hb, if_neg (by simp)] at hv
          cases hv
        · rw [hb, if_pos rfl] at hv
          obtain rfl := Option.some.inj hv
          rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
          exact ⟨htw, hb.2, hb.1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.1, List.mem_finRange _, ?_⟩
    rw [h1]
    simp [h2, h3]

/-- A twin candidate is distinct, same-coloured, non-adjacent, with disjoint neighbourhoods. -/
theorem twinP_of_twin_eq_some {adj : AdjMatrix n} {χ : Colouring n} {v w : Fin n}
    (h : twin adj χ v = some w) : twinP adj χ v w = true :=
  (uniqueFilter_eq_some_iff.mp h).1

/-- Distinct rails share no endpoint. -/
theorem rails_endpoint_eq {adj : AdjMatrix n} {χ : Colouring n} {p q : Fin n × Fin n}
    (hp : p ∈ rails adj χ) (hq : q ∈ rails adj χ)
    (hshare : p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) : p = q := by
  obtain ⟨hp1, hp2, hp3⟩ := mem_rails_iff.mp hp
  obtain ⟨hq1, hq2, hq3⟩ := mem_rails_iff.mp hq
  rcases hshare with h | h | h | h
  · have h2 : some p.2 = some q.2 := by rw [← hp1, h, hq1]
    exact Prod.ext h (Option.some.inj h2)
  · exfalso
    have h2 : some p.2 = some q.1 := by rw [← hp1, h, hq2]
    have h2' : p.2 = q.1 := Option.some.inj h2
    have hv1 := congrArg Fin.val h
    have hv2 := congrArg Fin.val h2'
    omega
  · exfalso
    have h2 : some p.1 = some q.2 := by rw [← hp2, h, hq1]
    have h2' : p.1 = q.2 := Option.some.inj h2
    have hv1 := congrArg Fin.val h
    have hv2 := congrArg Fin.val h2'
    omega
  · have h2 : some p.1 = some q.1 := by rw [← hp2, h, hq2]
    exact Prod.ext (Option.some.inj h2) h

/-- A rail's endpoints are distinct. -/
theorem rails_ne {adj : AdjMatrix n} {χ : Colouring n} {p : Fin n × Fin n}
    (hp : p ∈ rails adj χ) : p.1 ≠ p.2 := by
  obtain ⟨-, -, h3⟩ := mem_rails_iff.mp hp
  intro h
  rw [h] at h3
  omega

theorem onRail_iff {rl : List (Fin n × Fin n)} {x : Fin n} :
    onRail rl x = true ↔ ∃ p ∈ rl, x = p.1 ∨ x = p.2 := by
  unfold onRail
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hval⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hval
    exact ⟨p, hp, hval.imp Eq.symm Eq.symm⟩
  · rintro ⟨p, hp, hval⟩
    refine ⟨p, hp, ?_⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact hval.imp Eq.symm Eq.symm

/-- `onRail` over the rails of `(adj, χ)`, characterized through `twin` (transport-friendly). -/
theorem onRail_rails_iff {adj : AdjMatrix n} {χ : Colouring n} {x : Fin n} :
    onRail (rails adj χ) x = true
      ↔ ∃ y, twin adj χ x = some y ∧ twin adj χ y = some x := by
  rw [onRail_iff]
  constructor
  · rintro ⟨p, hp, hval⟩
    obtain ⟨h1, h2, -⟩ := mem_rails_iff.mp hp
    rcases hval with rfl | rfl
    · exact ⟨p.2, h1, h2⟩
    · exact ⟨p.1, h2, h1⟩
  · rintro ⟨y, h1, h2⟩
    have hxy : x ≠ y := by
      intro h
      have := twinP_of_twin_eq_some h1
      unfold twinP at this
      rw [← h] at this
      simp at this
    rcases Nat.lt_or_ge x.val y.val with hlt | hge
    · exact ⟨(x, y), mem_rails_iff.mpr ⟨h1, h2, hlt⟩, Or.inl rfl⟩
    · have hlt : y.val < x.val := by
        rcases Nat.lt_or_ge y.val x.val with h | h
        · exact h
        · exact absurd (Fin.ext (by omega)) hxy
      exact ⟨(y, x), mem_rails_iff.mpr ⟨h2, h1, hlt⟩, Or.inr rfl⟩

/-! ## 3. `railImg` — the rail action, pinned down -/

theorem railImg_eq_none_iff {rl : List (Fin n × Fin n)} {w : List Bool} {x : Fin n}
    (hlen : w.length = rl.length) :
    railImg rl w x = none ↔ onRail rl x = false := by
  unfold railImg
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro h
    cases honr : onRail rl x
    · rfl
    · exfalso
      obtain ⟨p, hp, hval⟩ := onRail_iff.mp honr
      have hzip : ∃ b, (p, b) ∈ rl.zip w := by
        obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
        exact ⟨w[i]'(by omega), List.mem_iff_getElem.mpr
          ⟨i, by simp [hlen]; omega, by simp [List.getElem_zip, hpi]⟩⟩
      obtain ⟨b, hb⟩ := hzip
      have hthis := h (p, b) hb
      rcases hval with rfl | rfl
      · simp at hthis
      · rcases Decidable.eq_or_ne p.2 p.1 with heq | hne
        · simp only [] at hthis
          rw [if_pos heq] at hthis
          simp at hthis
        · simp only [] at hthis
          rw [if_neg hne] at hthis
          simp at hthis
  · intro honr pb hpb
    have hp : pb.1 ∈ rl := by
      have := List.of_mem_zip hpb
      exact this.1
    rw [if_neg, if_neg]
    · intro h
      rw [onRail_iff.mpr ⟨pb.1, hp, Or.inr h⟩] at honr
      exact Bool.noConfusion honr
    · intro h
      rw [onRail_iff.mpr ⟨pb.1, hp, Or.inl h⟩] at honr
      exact Bool.noConfusion honr

/-- The generic scan-value lemma: if the entry `(p, b)` is in the list and every entry sharing an
endpoint with `p` *is* `(p, b)`, the scan at an endpoint of `p` returns its flip value. -/
theorem findSome?_rail_lookup {zs : List ((Fin n × Fin n) × Bool)} {p : Fin n × Fin n} {b : Bool}
    (hmem : (p, b) ∈ zs)
    (huniq : ∀ qc ∈ zs, (p.1 = qc.1.1 ∨ p.1 = qc.1.2 ∨ p.2 = qc.1.1 ∨ p.2 = qc.1.2) → qc = (p, b))
    {x : Fin n} (hx : x = p.1 ∨ x = p.2) :
    (zs.findSome? fun pb =>
      if x = pb.1.1 then some (if pb.2 then pb.1.2 else pb.1.1)
      else if x = pb.1.2 then some (if pb.2 then pb.1.1 else pb.1.2)
      else none)
      = some (if x = p.1 then (if b then p.2 else p.1) else (if b then p.1 else p.2)) := by
  induction zs with
  | nil => cases hmem
  | cons qc zs ih =>
      rcases Decidable.eq_or_ne x qc.1.1 with h1 | h1
      · have hqc : qc = (p, b) := by
          refine huniq qc (List.mem_cons_self ..) ?_
          rcases hx with rfl | rfl
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl h1))
        have hx1 : x = p.1 := by rw [h1, hqc]
        rw [hqc, List.findSome?_cons_of_isSome (by simp [hx1])]
        simp [hx1]
      · rcases Decidable.eq_or_ne x qc.1.2 with h2 | h2
        · have hqc : qc = (p, b) := by
            refine huniq qc (List.mem_cons_self ..) ?_
            rcases hx with rfl | rfl
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (Or.inr h2))
          have hx2 : x = p.2 := by rw [h2, hqc]
          have hx1 : ¬ (x = p.1) := by
            rw [hqc] at h1
            simpa using h1
          have hne : ¬ (p.2 = p.1) := fun h => hx1 (hx2.trans h)
          rw [hqc, List.findSome?_cons_of_isSome (by simp [hx2, hne])]
          simp [hx2, hne]
        · rw [List.findSome?_cons_of_isNone (by simp [h1, h2])]
          have hmem' : (p, b) ∈ zs := by
            rcases List.mem_cons.mp hmem with heq | hmem'
            · exfalso
              rcases hx with rfl | rfl
              · exact h1 (by rw [← heq])
              · exact h2 (by rw [← heq])
            · exact hmem'
          exact ih hmem' (fun qc' hqc' hshare => huniq qc' (List.mem_cons_of_mem _ hqc') hshare)

/-! ## 4. Automorphism stability — rails are structural -/

theorem permOf_apply {f : Fin n → Fin n} {ρ : Equiv.Perm (Fin n)}
    (h : permOf f = some ρ) (v : Fin n) : ρ v = f v := by
  unfold Deck2.permOf at h
  split at h
  · rw [← Option.some.inj h]
    rfl
  · cases h

theorem isAdj_comm (adj : AdjMatrix n) (v w : Fin n) : isAdj adj v w = isAdj adj w v := by
  unfold isAdj
  exact Bool.or_comm _ _

theorem isAdj_aut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (haut : IsColAut adj χ ρ) (v w : Fin n) :
    isAdj adj (ρ v) (ρ w) = isAdj adj v w := by
  unfold isAdj
  rw [haut.1 v w, haut.1 w v]

theorem isAdj_eq_false_iff {adj : AdjMatrix n} {v w : Fin n} :
    isAdj adj v w = false ↔ adj.adj v w = 0 ∧ adj.adj w v = 0 := by
  unfold isAdj
  rw [Bool.or_eq_false_iff]
  simp

/-- `all` over `finRange` is invariant under precomposition with a permutation. -/
theorem all_finRange_perm (σ : Equiv.Perm (Fin n)) (p : Fin n → Bool) :
    (List.finRange n).all (fun u => p (σ u)) = (List.finRange n).all p := by
  rcases hall : (List.finRange n).all p with _ | _
  · rw [List.all_eq_false] at hall ⊢
    obtain ⟨u, -, hu⟩ := hall
    exact ⟨σ.symm u, List.mem_finRange _, by rwa [Equiv.apply_symm_apply]⟩
  · rw [List.all_eq_true] at hall ⊢
    exact fun u _ => hall (σ u) (List.mem_finRange _)

theorem twinP_aut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (haut : IsColAut adj χ ρ) (v w : Fin n) :
    twinP adj χ (ρ v) (ρ w) = twinP adj χ v w := by
  unfold twinP
  have h1 : (ρ w != ρ v) = (w != v) := by
    simp only [bne]
    congr 1
    rw [Bool.eq_iff_iff]
    simp
  have h2 : (χ (ρ w) == χ (ρ v)) = (χ w == χ v) := by rw [haut.2 v, haut.2 w]
  have h3 : isAdj adj (ρ v) (ρ w) = isAdj adj v w := isAdj_aut haut v w
  have h4 : (List.finRange n).all (fun u => !(isAdj adj (ρ v) u && isAdj adj (ρ w) u))
      = (List.finRange n).all (fun u => !(isAdj adj v u && isAdj adj w u)) := by
    rw [← all_finRange_perm ρ (fun u => !(isAdj adj (ρ v) u && isAdj adj (ρ w) u))]
    congr 1
    funext u
    rw [isAdj_aut haut v u, isAdj_aut haut w u]
  rw [h1, h2, h3, h4]

theorem twin_aut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (haut : IsColAut adj χ ρ) (v : Fin n) :
    twin adj χ (ρ v) = (twin adj χ v).map ρ := by
  unfold twin
  exact uniqueFilter_transport ρ (fun w => twinP_aut haut v w)

theorem onRail_aut {adj : AdjMatrix n} {χ : Colouring n} {ρ : Equiv.Perm (Fin n)}
    (haut : IsColAut adj χ ρ) (x : Fin n) :
    onRail (rails adj χ) (ρ x) = onRail (rails adj χ) x := by
  rcases honr : onRail (rails adj χ) x with _ | _
  · rcases honr' : onRail (rails adj χ) (ρ x) with _ | _
    · rfl
    · exfalso
      obtain ⟨y, h1, h2⟩ := onRail_rails_iff.mp honr'
      have hy : y = ρ (ρ.symm y) := (Equiv.apply_symm_apply ρ y).symm
      have h1' : twin adj χ x = some (ρ.symm y) := by
        have := twin_aut haut x
        rw [h1] at this
        cases htw : twin adj χ x with
        | none => rw [htw] at this; cases this
        | some z =>
            rw [htw] at this
            have hz : y = ρ z := Option.some.inj this
            rw [hz]
            simp
      have h2' : twin adj χ (ρ.symm y) = some x := by
        have := twin_aut haut (ρ.symm y)
        rw [← hy, h2] at this
        cases htw : twin adj χ (ρ.symm y) with
        | none => rw [htw] at this; cases this
        | some z =>
            rw [htw] at this
            have hz : ρ x = ρ z := Option.some.inj this
            rw [ρ.injective hz]
      rw [onRail_rails_iff.mpr ⟨ρ.symm y, h1', h2'⟩] at honr
      exact Bool.noConfusion honr
  · obtain ⟨y, h1, h2⟩ := onRail_rails_iff.mp honr
    refine onRail_rails_iff.mpr ⟨ρ y, ?_, ?_⟩
    · rw [twin_aut haut x, h1]
      rfl
    · rw [twin_aut haut y, h2]
      rfl

/-! ## 5. Rails are `Nodup`; zip entries are unique per pair -/

theorem rails_map_fst_nodup (adj : AdjMatrix n) (χ : Colouring n) :
    ((rails adj χ).map (·.1)).Nodup := by
  have hgen : ∀ (v x : Fin n),
      x ∈ ((match twin adj χ v with
        | some w => if v.val < w.val && twin adj χ w == some v then some (v, w) else none
        | none => none).map (fun q : Fin n × Fin n => q.1)) → x = v := by
    intro v x hx
    cases htw : twin adj χ v with
    | none => rw [htw] at hx; cases hx
    | some w =>
        rw [htw] at hx
        simp only [] at hx
        cases hb : (decide (v.val < w.val) && (twin adj χ w == some v))
        · rw [hb, if_neg (by simp)] at hx
          cases hx
        · rw [hb, if_pos rfl] at hx
          have hvx : v = x := by simpa using hx
          exact hvx.symm
  unfold rails
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ (List.nodup_finRange n)
  intro a a' b hb hb'
  exact (hgen a b hb).symm.trans (hgen a' b hb')

theorem rails_nodup (adj : AdjMatrix n) (χ : Colouring n) : (rails adj χ).Nodup :=
  (rails_map_fst_nodup adj χ).of_map

/-- Two zip entries carrying the same rail carry the same bit. -/
theorem zip_entry_unique {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    {p : Fin n × Fin n} {b₁ b₂ : Bool}
    (h₁ : (p, b₁) ∈ (rails adj χ).zip u) (h₂ : (p, b₂) ∈ (rails adj χ).zip u) : b₁ = b₂ := by
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp h₂
  have hi1 : i < (rails adj χ).length := by simp at hi; omega
  have hi2 : i < u.length := by simp at hi; omega
  have hj1 : j < (rails adj χ).length := by simp at hj; omega
  have hj2 : j < u.length := by simp at hj; omega
  rw [List.getElem_zip] at hgi hgj
  have hpi : (rails adj χ)[i] = p := congrArg Prod.fst hgi
  have hpj : (rails adj χ)[j] = p := congrArg Prod.fst hgj
  have hij : i = j := by
    have hnd : (rails adj χ).Nodup := rails_nodup adj χ
    exact (List.Nodup.getElem_inj_iff hnd).mp (hpi.trans hpj.symm)
  subst hij
  have hbi : u[i] = b₁ := congrArg Prod.snd hgi
  have hbj : u[i] = b₂ := congrArg Prod.snd hgj
  rw [← hbi, ← hbj]

/-- Any zip entry sharing an endpoint with `(p, b)`'s rail *is* `(p, b)` — the uniqueness input to
`findSome?_rail_lookup`. -/
theorem zip_huniq {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    {p : Fin n × Fin n} {b : Bool} (hpb : (p, b) ∈ (rails adj χ).zip u) :
    ∀ qc ∈ (rails adj χ).zip u,
      (p.1 = qc.1.1 ∨ p.1 = qc.1.2 ∨ p.2 = qc.1.1 ∨ p.2 = qc.1.2) → qc = (p, b) := by
  intro qc hqc hshare
  have hp : p ∈ rails adj χ := (List.of_mem_zip hpb).1
  have hq : qc.1 ∈ rails adj χ := (List.of_mem_zip hqc).1
  have hpq : p = qc.1 := rails_endpoint_eq hp hq hshare
  have hqc' : (p, qc.2) ∈ (rails adj χ).zip u := by
    have hqe : qc = (p, qc.2) := by
      rw [hpq]
    rwa [hqe] at hqc
  have hb : b = qc.2 := zip_entry_unique hpb hqc'
  rw [hpq, hb]

/-! ## 6. `flipFunK`, factored — the guard, the satisfier predicate, the emitted action -/

/-- The per-rail flipped-adjacency condition inside `flipFunK` (`x` is the candidate). -/
def condFun (adj : AdjMatrix n) (v x : Fin n) (pb : (Fin n × Fin n) × Bool) : Bool :=
  let ia := if pb.2 then pb.1.2 else pb.1.1
  let ib := if pb.2 then pb.1.1 else pb.1.2
  adj.adj x ia == adj.adj v pb.1.1 && adj.adj ia x == adj.adj pb.1.1 v &&
  adj.adj x ib == adj.adj v pb.1.2 && adj.adj ib x == adj.adj pb.1.2 v

/-- The satisfier predicate inside `flipFunK`. -/
def satP (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (w : List Bool)
    (v : Fin n) : Fin n → Bool := fun x =>
  χ x == χ v && !onRail rl x && (rl.zip w).all (condFun adj v x)

/-- The flip guard: `v` touches a `w`-flipped rail. -/
def flipGuard (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) (w : List Bool) (v : Fin n) : Bool :=
  (rl.zip w).any (fun pb => pb.2 && touches adj v pb.1)

theorem flipFunK_eq (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n))
    (w : List Bool) (v : Fin n) :
    flipFunK adj χ rl w v
      = match railImg rl w v with
        | some x => x
        | none =>
            if flipGuard adj rl w v then
              match uniqueFilter (satP adj χ rl w v) with
              | some x => x
              | none => v
            else v := rfl

/-- The emitted permutation acts on every zipped rail exactly as the flip. -/
theorem emitted_rail_action {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    {ρ : Equiv.Perm (Fin n)} (hρ : permOf (flipFunK adj χ (rails adj χ) w) = some ρ)
    {p : Fin n × Fin n} {b : Bool} (hpb : (p, b) ∈ (rails adj χ).zip w) :
    ρ p.1 = (if b then p.2 else p.1) ∧ ρ p.2 = (if b then p.1 else p.2) := by
  have hp : p ∈ rails adj χ := (List.of_mem_zip hpb).1
  have hne := rails_ne hp
  have hu := zip_huniq hpb
  constructor
  · have h1 := permOf_apply hρ p.1
    rw [flipFunK_eq] at h1
    have hri : railImg (rails adj χ) w p.1 = some (if b then p.2 else p.1) := by
      unfold railImg
      rw [findSome?_rail_lookup hpb hu (Or.inl rfl)]
      simp
    rw [hri] at h1
    exact h1
  · have h1 := permOf_apply hρ p.2
    rw [flipFunK_eq] at h1
    have hri : railImg (rails adj χ) w p.2 = some (if b then p.1 else p.2) := by
      unfold railImg
      rw [findSome?_rail_lookup hpb hu (Or.inr rfl)]
      rw [if_neg (fun h => hne h.symm)]
    rw [hri] at h1
    exact h1

/-- **Touched vertices move.** Under a *verifying* emitted flip, a vertex touching a flipped rail
cannot stay fixed — twin neighbourhood-disjointness would be violated. This is what rules the
identity-default out of every verified table. -/
theorem touched_moves {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    {ρ : Equiv.Perm (Fin n)} (hρ : permOf (flipFunK adj χ (rails adj χ) w) = some ρ)
    (haut : IsColAut adj χ ρ) {v : Fin n}
    (hg : flipGuard adj (rails adj χ) w v = true) : ρ v ≠ v := by
  obtain ⟨pb, hpb, hcond⟩ := List.any_eq_true.mp hg
  rw [Bool.and_eq_true] at hcond
  obtain ⟨hbit, htch⟩ := hcond
  have hp : pb.1 ∈ rails adj χ := (List.of_mem_zip hpb).1
  have hpb' : (pb.1, pb.2) ∈ (rails adj χ).zip w := by simpa using hpb
  have hact := emitted_rail_action hρ hpb'
  rw [hbit] at hact
  simp only [if_true] at hact
  intro hfix
  have htwinP := twinP_of_twin_eq_some (mem_rails_iff.mp hp).1
  unfold twinP at htwinP
  simp only [Bool.and_eq_true] at htwinP
  obtain ⟨⟨⟨-, -⟩, -⟩, hall⟩ := htwinP
  rw [List.all_eq_true] at hall
  have hdisj := hall v (List.mem_finRange v)
  rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hdisj
  unfold touches at htch
  rw [Bool.or_eq_true] at htch
  rcases htch with hA | hB
  · have hAB : isAdj adj v pb.1.2 = true := by
      have hh := isAdj_aut haut v pb.1.1
      rw [hfix, hact.1] at hh
      rw [hh]
      exact hA
    rcases hdisj with h | h
    · rw [isAdj_comm adj pb.1.1 v, hA] at h
      cases h
    · rw [isAdj_comm adj pb.1.2 v, hAB] at h
      cases h
  · have hBA : isAdj adj v pb.1.1 = true := by
      have hh := isAdj_aut haut v pb.1.2
      rw [hfix, hact.2] at hh
      rw [hh]
      exact hB
    rcases hdisj with h | h
    · rw [isAdj_comm adj pb.1.1 v, hBA] at h
      cases h
    · rw [isAdj_comm adj pb.1.2 v, hB] at h
      cases h

/-! ## 7. Zip-index views and per-rail congruence -/

theorem getElem_xorRow' {a b : List Bool} {i : Nat} (hia : i < a.length) (hib : i < b.length)
    (hi : i < (xorRow a b).length) :
    (xorRow a b)[i] = (a[i] != b[i]) := by
  simp [xorRow, List.getElem_zipWith]

theorem mem_zip_iff_getElem' {l₁ : List (Fin n × Fin n)} {l₂ : List Bool}
    {x : (Fin n × Fin n) × Bool} (hl : l₂.length = l₁.length) :
    x ∈ l₁.zip l₂ ↔ ∃ i, ∃ h : i < l₁.length, l₁[i] = x.1 ∧ l₂[i]'(by omega) = x.2 := by
  constructor
  · intro hx
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hx
    have hi1 : i < l₁.length := by simp at hi; omega
    rw [List.getElem_zip] at hgi
    exact ⟨i, hi1, congrArg Prod.fst hgi, congrArg Prod.snd hgi⟩
  · rintro ⟨i, hi, h1, h2⟩
    refine List.mem_iff_getElem.mpr ⟨i, by simp [hl]; omega, ?_⟩
    rw [List.getElem_zip]
    exact Prod.ext h1 h2

theorem all_zip_iff {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    (hl : u.length = (rails adj χ).length) (f : (Fin n × Fin n) × Bool → Bool) :
    ((rails adj χ).zip u).all f = true
      ↔ ∀ i (h : i < (rails adj χ).length), f ((rails adj χ)[i], u[i]'(by omega)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    exact h _ ((mem_zip_iff_getElem' hl).mpr ⟨i, hi, rfl, rfl⟩)
  · intro h pb hpb
    obtain ⟨i, hi, h1, h2⟩ := (mem_zip_iff_getElem' hl).mp hpb
    have hpbe : pb = ((rails adj χ)[i], u[i]'(by omega)) := (Prod.ext h1 h2).symm
    rw [hpbe]
    exact h i hi

theorem any_zip_iff {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    (hl : u.length = (rails adj χ).length) (f : (Fin n × Fin n) × Bool → Bool) :
    ((rails adj χ).zip u).any f = true
      ↔ ∃ i, ∃ h : i < (rails adj χ).length, f ((rails adj χ)[i], u[i]'(by omega)) = true := by
  rw [List.any_eq_true]
  constructor
  · intro ⟨pb, hpb, hf⟩
    obtain ⟨i, hi, h1, h2⟩ := (mem_zip_iff_getElem' hl).mp hpb
    have hpbe : pb = ((rails adj χ)[i], u[i]'(by omega)) := (Prod.ext h1 h2).symm
    rw [hpbe] at hf
    exact ⟨i, hi, hf⟩
  · intro ⟨i, hi, hf⟩
    exact ⟨_, (mem_zip_iff_getElem' hl).mpr ⟨i, hi, rfl, rfl⟩, hf⟩

/-- `condFun`, unfolded onto an explicit pair (definitional). -/
theorem condFun_mk (adj : AdjMatrix n) (v x : Fin n) (p : Fin n × Fin n) (b : Bool) :
    condFun adj v x (p, b)
      = (adj.adj x (if b then p.2 else p.1) == adj.adj v p.1 &&
         adj.adj (if b then p.2 else p.1) x == adj.adj p.1 v &&
         adj.adj x (if b then p.1 else p.2) == adj.adj v p.2 &&
         adj.adj (if b then p.1 else p.2) x == adj.adj p.2 v) := rfl

/-- An untouched rail's condition does not depend on its bit. -/
theorem condFun_untouched {adj : AdjMatrix n} {v : Fin n} {p : Fin n × Fin n}
    (h : touches adj v p = false) (x : Fin n) (b₁ b₂ : Bool) :
    condFun adj v x (p, b₁) = condFun adj v x (p, b₂) := by
  unfold touches at h
  rw [Bool.or_eq_false_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [isAdj_eq_false_iff] at h1 h2
  rw [condFun_mk, condFun_mk, h1.1, h1.2, h2.1, h2.2]
  have hredF : ∀ (y z : Fin n), (if false = true then y else z) = z :=
    fun _ _ => if_neg (by simp)
  have hredT' : ∀ (y z : Fin n), (if True then y else z) = y := fun _ _ => if_pos trivial
  cases b₁ <;> cases b₂ <;> simp only [hredF, hredT'] <;> try rfl
  all_goals
    generalize (adj.adj x p.1 == 0) = A
    generalize (adj.adj p.1 x == 0) = B
    generalize (adj.adj x p.2 == 0) = C
    generalize (adj.adj p.2 x == 0) = D
    cases A <;> cases B <;> cases C <;> cases D <;> rfl

/-- The point form of flip composition on a rail. -/
theorem flip_pt_comp {p : Fin n × Fin n} {ρ : Equiv.Perm (Fin n)} {bw bw' : Bool}
    (h1 : ρ p.1 = if bw then p.2 else p.1) (h2 : ρ p.2 = if bw then p.1 else p.2) :
    (if (bw != bw') then p.2 else p.1) = ρ (if bw' then p.2 else p.1)
      ∧ (if (bw != bw') then p.1 else p.2) = ρ (if bw' then p.1 else p.2) := by
  cases bw <;> cases bw' <;> simp [h1, h2]

/-- Per-rail condition transport under the emitted `w`-flip. -/
theorem condFun_conj_flip {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    {ρ : Equiv.Perm (Fin n)} (hρ : permOf (flipFunK adj χ (rails adj χ) w) = some ρ)
    (haut : IsColAut adj χ ρ) {p : Fin n × Fin n} {bw : Bool}
    (hpw : (p, bw) ∈ (rails adj χ).zip w) (v x : Fin n) (bw' : Bool) :
    condFun adj v (ρ x) (p, (bw != bw')) = condFun adj v x (p, bw') := by
  have hact := emitted_rail_action hρ hpw
  obtain ⟨e1, e2⟩ := flip_pt_comp (bw' := bw') hact.1 hact.2
  rw [condFun_mk, condFun_mk, e1, e2]
  simp only [haut.1]

/-! ## 8. Guard and satisfier congruence / transport -/

theorem flipGuard_congr {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : List Bool} {v : Fin n}
    (hl₁ : u₁.length = (rails adj χ).length) (hl₂ : u₂.length = (rails adj χ).length)
    (hbits : ∀ i (h : i < (rails adj χ).length),
      touches adj v ((rails adj χ)[i]) = true → u₁[i]'(by omega) = u₂[i]'(by omega)) :
    flipGuard adj (rails adj χ) u₁ v = flipGuard adj (rails adj χ) u₂ v := by
  unfold flipGuard
  rw [Bool.eq_iff_iff, any_zip_iff hl₁, any_zip_iff hl₂]
  constructor
  · rintro ⟨i, hi, hf⟩
    simp only [] at hf
    rw [Bool.and_eq_true] at hf
    refine ⟨i, hi, ?_⟩
    simp only []
    rw [Bool.and_eq_true]
    exact ⟨(hbits i hi hf.2) ▸ hf.1, hf.2⟩
  · rintro ⟨i, hi, hf⟩
    simp only [] at hf
    rw [Bool.and_eq_true] at hf
    refine ⟨i, hi, ?_⟩
    simp only []
    rw [Bool.and_eq_true]
    exact ⟨(hbits i hi hf.2).symm ▸ hf.1, hf.2⟩

theorem satP_congr_touch {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : List Bool} {v : Fin n}
    (hl₁ : u₁.length = (rails adj χ).length) (hl₂ : u₂.length = (rails adj χ).length)
    (hbits : ∀ i (h : i < (rails adj χ).length),
      touches adj v ((rails adj χ)[i]) = true → u₁[i]'(by omega) = u₂[i]'(by omega))
    (x : Fin n) :
    satP adj χ (rails adj χ) u₁ v x = satP adj χ (rails adj χ) u₂ v x := by
  unfold satP
  congr 1
  rw [Bool.eq_iff_iff, all_zip_iff hl₁, all_zip_iff hl₂]
  constructor
  · intro h i hi
    rcases htch : touches adj v ((rails adj χ)[i]) with _ | _
    · rw [← condFun_untouched htch x (u₁[i]'(by omega)) (u₂[i]'(by omega))]
      exact h i hi
    · rw [← hbits i hi htch]
      exact h i hi
  · intro h i hi
    rcases htch : touches adj v ((rails adj χ)[i]) with _ | _
    · rw [condFun_untouched htch x (u₁[i]'(by omega)) (u₂[i]'(by omega))]
      exact h i hi
    · rw [hbits i hi htch]
      exact h i hi

/-- **★ THE SATISFIER TRANSPORT.** The verified `w`-flip carries the satisfier predicate of `w'` to
that of `w ⊕ w'` — the bijection the composed table's `uniqueFilter` rides on. -/
theorem satP_conj_flip {adj : AdjMatrix n} {χ : Colouring n} {w w' : List Bool}
    (hlw : w.length = (rails adj χ).length) (hlw' : w'.length = (rails adj χ).length)
    {ρ : Equiv.Perm (Fin n)} (hρ : permOf (flipFunK adj χ (rails adj χ) w) = some ρ)
    (haut : IsColAut adj χ ρ) (v x : Fin n) :
    satP adj χ (rails adj χ) (xorRow w w') v (ρ x) = satP adj χ (rails adj χ) w' v x := by
  have hlx : (xorRow w w').length = (rails adj χ).length := by
    rw [length_xorRow, hlw, hlw']
    omega
  unfold satP
  have hcol : (χ (ρ x) == χ v) = (χ x == χ v) := by rw [haut.2 x]
  have honr : onRail (rails adj χ) (ρ x) = onRail (rails adj χ) x := onRail_aut haut x
  rw [hcol, honr]
  congr 1
  rw [Bool.eq_iff_iff, all_zip_iff hlx, all_zip_iff hlw']
  have hkey : ∀ i (h : i < (rails adj χ).length),
      condFun adj v (ρ x) ((rails adj χ)[i], (xorRow w w')[i]'(by omega))
        = condFun adj v x ((rails adj χ)[i], w'[i]'(by omega)) := by
    intro i hi
    have hwm : ((rails adj χ)[i], w[i]'(by omega)) ∈ (rails adj χ).zip w :=
      (mem_zip_iff_getElem' hlw).mpr ⟨i, hi, rfl, rfl⟩
    have hxi : (xorRow w w')[i]'(by omega) = (w[i]'(by omega) != w'[i]'(by omega)) :=
      getElem_xorRow' (by omega) (by omega) (by omega)
    rw [hxi]
    exact condFun_conj_flip hρ haut hwm v x _
  constructor
  · intro h i hi
    rw [← hkey i hi]
    exact h i hi
  · intro h i hi
    rw [hkey i hi]
    exact h i hi

/-- A vertex untouched by every flipped rail satisfies its own predicate. -/
theorem satP_self_of_guard_false {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    (hl : u.length = (rails adj χ).length) {v : Fin n}
    (honr : onRail (rails adj χ) v = false)
    (hg : flipGuard adj (rails adj χ) u v = false) :
    satP adj χ (rails adj χ) u v v = true := by
  unfold satP
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp, by rw [honr]; rfl⟩, ?_⟩
  rw [all_zip_iff hl]
  intro i hi
  have hng : ¬ (u[i]'(by omega) = true ∧ touches adj v ((rails adj χ)[i]) = true) := by
    intro ⟨hb, ht⟩
    have hgt : flipGuard adj (rails adj χ) u v = true := by
      unfold flipGuard
      rw [any_zip_iff hl]
      refine ⟨i, hi, ?_⟩
      simp only []
      rw [Bool.and_eq_true]
      exact ⟨hb, ht⟩
    rw [hg] at hgt
    cases hgt
  rcases hcaseb : u[i]'(by omega) with _ | _
  · rw [condFun_mk]
    simp
  · have ht : touches adj v ((rails adj χ)[i]) = false := by
      rcases hcaset : touches adj v ((rails adj χ)[i]) with _ | _
      · rfl
      · exact absurd ⟨hcaseb, hcaset⟩ hng
    unfold touches at ht
    rw [Bool.or_eq_false_iff] at ht
    obtain ⟨h1, h2⟩ := ht
    rw [isAdj_eq_false_iff] at h1 h2
    rw [condFun_mk]
    simp [h1.1, h1.2, h2.1, h2.2]

/-! ## 9. ★★★ THE FLIP-COMPOSITION (PRODUCT) LEMMA -/

/-- **★★★ Verified flips compose.** If the flips of `w` and `w'` both pass `permOf` + `IsColAut`,
the table of the XOR word is exactly their composite — so it passes both gates too. This is the
theorem behind the all-or-nothing gate: "the whole basis verifies" propagates to every word of the
span, and the emitted GROUP is the flip-realization of the canonical subspace. -/
theorem flipFunK_xor {adj : AdjMatrix n} {χ : Colouring n} {w w' : List Bool}
    (hlw : w.length = (rails adj χ).length) (hlw' : w'.length = (rails adj χ).length)
    {ρ ρ' : Equiv.Perm (Fin n)}
    (hρ : permOf (flipFunK adj χ (rails adj χ) w) = some ρ) (haut : IsColAut adj χ ρ)
    (hρ' : permOf (flipFunK adj χ (rails adj χ) w') = some ρ') (haut' : IsColAut adj χ ρ')
    (v : Fin n) :
    flipFunK adj χ (rails adj χ) (xorRow w w') v = ρ (ρ' v) := by
  have hlx : (xorRow w w').length = (rails adj χ).length := by
    rw [length_xorRow, hlw, hlw']
    omega
  rcases honr : onRail (rails adj χ) v with _ | _
  · -- non-rail vertex
    rw [flipFunK_eq, (railImg_eq_none_iff hlx).mpr honr]
    simp only []
    have hρ'v := permOf_apply hρ' v
    rw [flipFunK_eq, (railImg_eq_none_iff hlw').mpr honr] at hρ'v
    simp only [] at hρ'v
    rcases hg' : flipGuard adj (rails adj χ) w' v with _ | _
    · -- w'-guard false: ρ' fixes v; the xor word agrees with w on everything v touches
      rw [hg'] at hρ'v
      rw [if_neg (by simp)] at hρ'v
      rw [hρ'v]
      have hρv := permOf_apply hρ v
      rw [flipFunK_eq, (railImg_eq_none_iff hlw).mpr honr] at hρv
      simp only [] at hρv
      rw [hρv]
      have hbits : ∀ j (hj : j < (rails adj χ).length),
          touches adj v ((rails adj χ)[j]) = true →
          (xorRow w w')[j]'(by omega) = w[j]'(by omega) := by
        intro j hj htch
        have hw'j : w'[j]'(by omega) = false := by
          rcases hcase : w'[j]'(by omega) with _ | _
          · rfl
          · exfalso
            have hgt : flipGuard adj (rails adj χ) w' v = true := by
              unfold flipGuard
              rw [any_zip_iff hlw']
              refine ⟨j, hj, ?_⟩
              simp only []
              rw [Bool.and_eq_true]
              exact ⟨hcase, htch⟩
            rw [hg'] at hgt
            cases hgt
        rw [getElem_xorRow' (by omega) (by omega) (by omega), hw'j]
        simp
      rw [flipGuard_congr hlx hlw hbits,
        funext (satP_congr_touch hlx hlw hbits)]
    · -- w'-guard true: the satisfier transport composes the tables
      rw [hg'] at hρ'v
      rw [if_pos rfl] at hρ'v
      cases hufw' : uniqueFilter (satP adj χ (rails adj χ) w' v) with
      | none =>
          rw [hufw'] at hρ'v
          simp only [] at hρ'v
          exact absurd hρ'v (touched_moves hρ' haut' hg')
      | some u =>
          rw [hufw'] at hρ'v
          simp only [] at hρ'v
          have hufx : uniqueFilter (satP adj χ (rails adj χ) (xorRow w w') v)
              = some (ρ u) := by
            have htr := uniqueFilter_transport ρ
              (P := satP adj χ (rails adj χ) w' v)
              (P' := satP adj χ (rails adj χ) (xorRow w w') v)
              (fun z => satP_conj_flip hlw hlw' hρ haut v z)
            rw [htr, hufw']
            rfl
          rcases hgx : flipGuard adj (rails adj χ) (xorRow w w') v with _ | _
          · rw [if_neg (by simp)]
            have hself : satP adj χ (rails adj χ) (xorRow w w') v v = true :=
              satP_self_of_guard_false hlx honr hgx
            have hvu : v = ρ u := (uniqueFilter_eq_some_iff.mp hufx).2 v hself
            rw [hρ'v, ← hvu]
          · rw [if_pos rfl, hufx]
            simp only []
            rw [hρ'v]
  · -- rail endpoint
    obtain ⟨p, hp, hval⟩ := onRail_iff.mp honr
    obtain ⟨i, hilen, hpi⟩ := List.mem_iff_getElem.mp hp
    have hwm : (p, w[i]'(by omega)) ∈ (rails adj χ).zip w :=
      (mem_zip_iff_getElem' hlw).mpr ⟨i, hilen, hpi, rfl⟩
    have hw'm : (p, w'[i]'(by omega)) ∈ (rails adj χ).zip w' :=
      (mem_zip_iff_getElem' hlw').mpr ⟨i, hilen, hpi, rfl⟩
    have hxm : (p, (w[i]'(by omega) != w'[i]'(by omega))) ∈ (rails adj χ).zip (xorRow w w') :=
      (mem_zip_iff_getElem' hlx).mpr
        ⟨i, hilen, hpi, getElem_xorRow' (by omega) (by omega) (by omega)⟩
    have hact := emitted_rail_action hρ hwm
    have hact' := emitted_rail_action hρ' hw'm
    have hu := zip_huniq hxm
    have hne := rails_ne hp
    rw [flipFunK_eq]
    rcases hval with rfl | rfl
    · have hri : railImg (rails adj χ) (xorRow w w') p.1
          = some (if (w[i]'(by omega) != w'[i]'(by omega)) then p.2 else p.1) := by
        unfold railImg
        rw [findSome?_rail_lookup hxm hu (Or.inl rfl)]
        simp
      rw [hri]
      simp only []
      rw [hact'.1]
      exact (flip_pt_comp hact.1 hact.2).1
    · have hri : railImg (rails adj χ) (xorRow w w') p.2
          = some (if (w[i]'(by omega) != w'[i]'(by omega)) then p.1 else p.2) := by
        unfold railImg
        rw [findSome?_rail_lookup hxm hu (Or.inr rfl)]
        rw [if_neg (fun h => hne h.symm)]
      rw [hri]
      simp only []
      rw [hact'.2]
      exact (flip_pt_comp hact.1 hact.2).2
