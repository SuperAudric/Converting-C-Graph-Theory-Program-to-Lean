import ChainDescent.KernelRef

/-!
# `C3a` — tranche 2 part IV: σ-equivariance of the kernel reference supply

`KernelRef.lean` reduced ①/②/③ for `kernelSupply` to the *set-level reference* `kernelRefSupply`
(`OrbitPrune.SameOrbits`). What remains is the reference's own transport obligation:
`SupplyTransport.GensEquivariant kernelRefSupply`. This file discharges it.

The chain, and why each link is shaped the way it is:

* **§1 the σ-conjugation stack.** Every structural predicate of the pipeline (`isAdj`, `twinP`,
  `twin`, `rails`, `onRail`, `touches`) is a function of `(adj, χ)`, so it transports. Rails
  transport *up to endpoint order*: the rail list stores each pair at its lower index, an internal
  labelling that `σ` need not respect — hence `sPair`/`railMap` and a **membership-level**
  correspondence rather than a pointwise one.
* **§2 word transport.** A word is indexed by rail *position*, and `σ` permutes positions
  arbitrarily. `transportWord` re-reads each bit by endpoint lookup, and the central lemma
  `mem_zip_transport` says the labelled word `rails.zip w` transports *as a set of labelled bits*.
  Everything downstream (`dotB`, the guards, the satisfier conditions) is then a membership or
  parity statement over that zip, so it transports too.
* **§3 emission transport** (`flipFunK_conj`), then `Deck2.permOf_conj` moves the gate.
* **§4 the `inL` bridge.** `localRows` is *pivot-dependent* and does not transport pointwise. So
  `L` is first re-characterized basis-free (`Lc`: `w` is killed by every wire-supported functional
  that kills the local patterns) — a statement quantifying over all functionals, hence transportable
  memberwise. Part I (`nullBasis` sound *and* complete) is exactly what bridges the two.
* **§5** assembles `GensEquivariant kernelRefSupply`.
-/

namespace ChainDescent
namespace Kernel

open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut)
open ChainDescent.Deck (uniqueFilter)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. The σ-conjugation stack

`IsoTo σ adj χ adj' χ'` is "σ is an isomorphism `(adj, χ) → (adj', χ')`". Stating the stack against
this rather than against `relabelAdj`/`transportColouring` directly keeps the proofs identical in
shape to the `IsColAut`-specialized versions of `KernelFlip` §4 (which are the case `adj' = adj`,
`χ' = χ`) and lets `σ.symm` be used in the same breath as `σ`. -/

/-- `σ` carries `(adj, χ)` to `(adj', χ')`. -/
structure IsoTo (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (adj' : AdjMatrix n) (χ' : Colouring n) : Prop where
  adjEq : ∀ v w : Fin n, adj'.adj (σ v) (σ w) = adj.adj v w
  colEq : ∀ v : Fin n, χ' (σ v) = χ v

/-- The instance the equivariance obligation is stated at. -/
theorem isoTo_relabel (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    IsoTo σ adj χ (relabelAdj σ adj) (transportColouring σ χ) where
  adjEq v w := by simp [relabelAdj]
  colEq v := by simp [transportColouring]

/-- The inverse isomorphism. -/
theorem IsoTo.symm {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') :
    IsoTo σ.symm adj' χ' adj χ where
  adjEq v w := by
    have hh := h.adjEq (σ.symm v) (σ.symm w)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
    exact hh.symm
  colEq v := by
    have hh := h.colEq (σ.symm v)
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm

theorem isAdj_iso {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v w : Fin n) :
    isAdj adj' (σ v) (σ w) = isAdj adj v w := by
  unfold isAdj
  rw [h.adjEq v w, h.adjEq w v]

theorem twinP_iso {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v w : Fin n) :
    twinP adj' χ' (σ v) (σ w) = twinP adj χ v w := by
  unfold twinP
  have h1 : (σ w != σ v) = (w != v) := by
    simp only [bne]
    congr 1
    rw [Bool.eq_iff_iff]
    simp
  have h2 : (χ' (σ w) == χ' (σ v)) = (χ w == χ v) := by rw [h.colEq v, h.colEq w]
  have h3 : isAdj adj' (σ v) (σ w) = isAdj adj v w := isAdj_iso h v w
  have h4 : (List.finRange n).all (fun u => !(isAdj adj' (σ v) u && isAdj adj' (σ w) u))
      = (List.finRange n).all (fun u => !(isAdj adj v u && isAdj adj w u)) := by
    rw [← all_finRange_perm σ (fun u => !(isAdj adj' (σ v) u && isAdj adj' (σ w) u))]
    congr 1
    funext u
    rw [isAdj_iso h v u, isAdj_iso h w u]
  rw [h1, h2, h3, h4]

theorem twin_iso {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v : Fin n) :
    twin adj' χ' (σ v) = (twin adj χ v).map σ := by
  unfold twin
  exact uniqueFilter_transport σ (fun w => twinP_iso h v w)

/-- The pair `{a, b}` listed at its lower index — the rail list's internal convention. -/
def sPair (a b : Fin n) : Fin n × Fin n := if a.val < b.val then (a, b) else (b, a)

theorem sPair_cases (a b : Fin n) : sPair a b = (a, b) ∨ sPair a b = (b, a) := by
  unfold sPair; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sPair_lt {a b : Fin n} (hab : a ≠ b) : (sPair a b).1.val < (sPair a b).2.val := by
  unfold sPair
  rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
  · rw [if_pos hlt]; exact hlt
  · exact absurd (Fin.ext heq) hab
  · rw [if_neg (by omega)]; exact hgt

theorem sPair_comm {a b : Fin n} (hab : a ≠ b) : sPair a b = sPair b a := by
  unfold sPair
  rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (by omega)]
  · exact absurd (Fin.ext heq) hab
  · rw [if_neg (by omega), if_pos hgt]

theorem sPair_self {p : Fin n × Fin n} (h : p.1.val < p.2.val) : sPair p.1 p.2 = p := by
  unfold sPair; rw [if_pos h]

/-- The rail correspondence map: transport the endpoints, then re-normalize the endpoint order. -/
def railMap (σ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) : Fin n × Fin n := sPair (σ p.1) (σ p.2)

theorem mem_rails_sPair {adj : AdjMatrix n} {χ : Colouring n} {a b : Fin n} (hab : a ≠ b)
    (h1 : twin adj χ a = some b) (h2 : twin adj χ b = some a) : sPair a b ∈ rails adj χ := by
  rcases sPair_cases a b with hs | hs
  · rw [hs]
    exact mem_rails_iff.mpr ⟨h1, h2, by have := sPair_lt hab; rwa [hs] at this⟩
  · rw [hs]
    exact mem_rails_iff.mpr ⟨h2, h1, by have := sPair_lt hab; rwa [hs] at this⟩

/-- **Rails transport, memberwise.** The rail *list order* is an internal labelling; what is
canonical is the rail *set*, and `σ` carries it onto the relabelled graph's rail set. -/
theorem mem_rails_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {q : Fin n × Fin n} :
    q ∈ rails adj' χ' ↔ ∃ p ∈ rails adj χ, q = railMap σ p := by
  constructor
  · intro hq
    obtain ⟨hq1, hq2, hlt⟩ := mem_rails_iff.mp hq
    have hqa : σ (σ.symm q.1) = q.1 := Equiv.apply_symm_apply σ q.1
    have hqb : σ (σ.symm q.2) = q.2 := Equiv.apply_symm_apply σ q.2
    have h1 : twin adj χ (σ.symm q.1) = some (σ.symm q.2) := by
      have hh := twin_iso h (σ.symm q.1)
      rw [hqa, hq1] at hh
      cases htw : twin adj χ (σ.symm q.1) with
      | none => rw [htw] at hh; cases hh
      | some z =>
          rw [htw] at hh
          have hz : q.2 = σ z := Option.some.inj hh
          rw [hz, Equiv.symm_apply_apply]
    have h2 : twin adj χ (σ.symm q.2) = some (σ.symm q.1) := by
      have hh := twin_iso h (σ.symm q.2)
      rw [hqb, hq2] at hh
      cases htw : twin adj χ (σ.symm q.2) with
      | none => rw [htw] at hh; cases hh
      | some z =>
          rw [htw] at hh
          have hz : q.1 = σ z := Option.some.inj hh
          rw [hz, Equiv.symm_apply_apply]
    have hne : σ.symm q.1 ≠ σ.symm q.2 := by
      intro hcon
      have hqq : q.1 = q.2 := by rw [← hqa, ← hqb, hcon]
      rw [hqq] at hlt
      omega
    have hneq : q.2 ≠ q.1 := by
      intro hc
      rw [hc] at hlt
      omega
    refine ⟨sPair (σ.symm q.1) (σ.symm q.2), mem_rails_sPair hne h1 h2, ?_⟩
    unfold railMap
    rcases sPair_cases (σ.symm q.1) (σ.symm q.2) with hs | hs
    · rw [hs]
      simp only []
      rw [hqa, hqb, sPair_self hlt]
    · rw [hs]
      simp only []
      rw [hqa, hqb, sPair_comm hneq, sPair_self hlt]
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2, hlt⟩ := mem_rails_iff.mp hp
    have hne : σ p.1 ≠ σ p.2 := fun hc => by
      rw [σ.injective hc] at hlt; omega
    refine mem_rails_sPair hne ?_ ?_
    · rw [twin_iso h p.1, hp1]; rfl
    · rw [twin_iso h p.2, hp2]; rfl

theorem railMap_injOn {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {p q : Fin n × Fin n} (hp : p ∈ rails adj χ) (hq : q ∈ rails adj χ)
    (heq : railMap σ p = railMap σ q) : p = q := by
  have hpl := (mem_rails_iff.mp hp).2.2
  have hql := (mem_rails_iff.mp hq).2.2
  unfold railMap at heq
  rcases sPair_cases (σ p.1) (σ p.2) with hsp | hsp <;>
    rcases sPair_cases (σ q.1) (σ q.2) with hsq | hsq <;>
    · rw [hsp, hsq] at heq
      have e1 := congrArg Prod.fst heq
      have e2 := congrArg Prod.snd heq
      simp only [] at e1 e2
      first
      | exact Prod.ext_iff.mpr ⟨σ.injective e1, σ.injective e2⟩
      | exact Prod.ext_iff.mpr ⟨σ.injective e2, σ.injective e1⟩
      | (exfalso
         have f1 := congrArg Fin.val (σ.injective e1)
         have f2 := congrArg Fin.val (σ.injective e2)
         omega)

/-- **The rail lists are permutations of each other along `railMap σ`.** This is the strongest
statement available: not an equality of lists (the order is an internal labelling), but a `Perm`,
which is exactly what every parity/count argument downstream needs. -/
theorem rails_perm_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') :
    List.Perm (rails adj' χ') ((rails adj χ).map (railMap σ)) := by
  refine (List.perm_ext_iff_of_nodup (rails_nodup adj' χ') ?_).mpr ?_
  · refine List.Nodup.map_on ?_ (rails_nodup adj χ)
    intro p hp q hq hpq
    exact railMap_injOn hp hq hpq
  · intro q
    rw [List.mem_map]
    constructor
    · intro hq
      obtain ⟨p, hp, hqp⟩ := (mem_rails_conj h).mp hq
      exact ⟨p, hp, hqp.symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact (mem_rails_conj h).mpr ⟨p, hp, rfl⟩

/-- The rail lists have equal length. -/
theorem rails_length_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') :
    (rails adj' χ').length = (rails adj χ).length := by
  rw [(rails_perm_conj h).length_eq, List.length_map]

theorem onRail_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (x : Fin n) :
    onRail (rails adj' χ') (σ x) = onRail (rails adj χ) x := by
  rcases honr : onRail (rails adj χ) x with _ | _
  · rcases honr' : onRail (rails adj' χ') (σ x) with _ | _
    · rfl
    · exfalso
      obtain ⟨y, h1, h2⟩ := onRail_rails_iff.mp honr'
      have h1' : twin adj χ x = some (σ.symm y) := by
        have := twin_iso h x
        rw [h1] at this
        cases htw : twin adj χ x with
        | none => rw [htw] at this; cases this
        | some z =>
            rw [htw] at this
            have hz : y = σ z := Option.some.inj this
            rw [hz, Equiv.symm_apply_apply]
      have h2' : twin adj χ (σ.symm y) = some x := by
        have := twin_iso h (σ.symm y)
        rw [Equiv.apply_symm_apply, h2] at this
        cases htw : twin adj χ (σ.symm y) with
        | none => rw [htw] at this; cases this
        | some z =>
            rw [htw] at this
            have hz : σ x = σ z := Option.some.inj this
            rw [σ.injective hz]
      rw [onRail_rails_iff.mpr ⟨σ.symm y, h1', h2'⟩] at honr
      exact Bool.noConfusion honr
  · obtain ⟨y, h1, h2⟩ := onRail_rails_iff.mp honr
    refine onRail_rails_iff.mpr ⟨σ y, ?_, ?_⟩
    · rw [twin_iso h x, h1]; rfl
    · rw [twin_iso h y, h2]; rfl

/-- `touches` is endpoint-order invariant, so it survives `sPair` normalization. -/
theorem touches_swap (adj : AdjMatrix n) (v : Fin n) (a b : Fin n) :
    touches adj v (a, b) = touches adj v (b, a) := by
  unfold touches
  exact Bool.or_comm _ _

theorem touches_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ')
    (v : Fin n) (p : Fin n × Fin n) :
    touches adj' (σ v) (railMap σ p) = touches adj v p := by
  have hbase : touches adj' (σ v) (σ p.1, σ p.2) = touches adj v p := by
    unfold touches
    rw [isAdj_iso h v p.1, isAdj_iso h v p.2]
  unfold railMap
  rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
  · rw [hs]; exact hbase
  · rw [hs, ← touches_swap adj' (σ v) (σ p.1) (σ p.2)]; exact hbase

/-! ## 2. Word transport

A word is a list of bits indexed by *rail position*, and `σ` permutes positions arbitrarily. So a
word is transported by re-reading each bit by **endpoint lookup**: the bit of the target rail `q` is
whatever bit the source word gave the rail through `σ.symm q.1`. Everything the pipeline does with a
word is a statement about the labelled list `rails.zip w` — membership (`all`/`any` over the zip) or
parity (`dotB`) — so `mem_zip_transport` and `transport_perm` are between them the whole story. -/

/-- The bit that `u` assigns to the rail with endpoint `x` (`false` off the rails). -/
def lookupBit (rl : List (Fin n × Fin n)) (u : List Bool) (x : Fin n) : Bool :=
  ((rl.zip u).findSome? fun pb => if x = pb.1.1 ∨ x = pb.1.2 then some pb.2 else none).getD false

/-- Transport a word from the rail list `rl` to the rail list `rl'` along `σ`. -/
def transportWordR (σ : Equiv.Perm (Fin n)) (rl rl' : List (Fin n × Fin n)) (u : List Bool) :
    List Bool :=
  rl'.map (fun q => lookupBit rl u (σ.symm q.1))

/-- The scan-value lemma for the bit lookup (the `railImg` analogue is `findSome?_rail_lookup`). -/
theorem findSome?_bit_lookup {zs : List ((Fin n × Fin n) × Bool)} {p : Fin n × Fin n} {b : Bool}
    (hmem : (p, b) ∈ zs)
    (huniq : ∀ qc ∈ zs, (p.1 = qc.1.1 ∨ p.1 = qc.1.2 ∨ p.2 = qc.1.1 ∨ p.2 = qc.1.2) → qc = (p, b))
    {x : Fin n} (hx : x = p.1 ∨ x = p.2) :
    (zs.findSome? fun pb => if x = pb.1.1 ∨ x = pb.1.2 then some pb.2 else none) = some b := by
  induction zs with
  | nil => cases hmem
  | cons qc zs ih =>
      by_cases hc : x = qc.1.1 ∨ x = qc.1.2
      · have hqc : qc = (p, b) := by
          refine huniq qc (List.mem_cons_self ..) ?_
          rcases hx with rfl | rfl <;> rcases hc with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr h'))
        rw [hqc, List.findSome?_cons_of_isSome (by rw [if_pos hx]; rfl)]
        rw [if_pos hx]
      · rw [List.findSome?_cons_of_isNone (by rw [if_neg hc]; rfl)]
        refine ih ?_ (fun qc' hqc' hshare => huniq qc' (List.mem_cons_of_mem _ hqc') hshare)
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact absurd (by rw [← heq]; exact hx) hc
        · exact hmem'

theorem zip_getElem_mem {rl : List (Fin n × Fin n)} {u : List Bool} (hu : u.length = rl.length)
    {i : Nat} (hi : i < rl.length) : (rl[i], u[i]'(by omega)) ∈ rl.zip u := by
  refine List.mem_iff_getElem.mpr ⟨i, by simp [hu]; omega, ?_⟩
  rw [List.getElem_zip]

theorem exists_zip_bit {rl : List (Fin n × Fin n)} {u : List Bool} (hu : u.length = rl.length)
    {p : Fin n × Fin n} (hp : p ∈ rl) : ∃ b, (p, b) ∈ rl.zip u := by
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine ⟨u[i]'(by omega), ?_⟩
  have := zip_getElem_mem hu hi
  rwa [hpi] at this

/-- The lookup returns the paired bit. -/
theorem lookupBit_eq {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    {p : Fin n × Fin n} {b : Bool} (hpb : (p, b) ∈ (rails adj χ).zip u)
    {x : Fin n} (hx : x = p.1 ∨ x = p.2) : lookupBit (rails adj χ) u x = b := by
  unfold lookupBit
  rw [findSome?_bit_lookup hpb (zip_huniq hpb) hx]
  rfl

theorem lookupBit_off {rl : List (Fin n × Fin n)} {u : List Bool} {x : Fin n}
    (h : onRail rl x = false) : lookupBit rl u x = false := by
  unfold lookupBit
  have hnone : ((rl.zip u).findSome? fun pb =>
      if x = pb.1.1 ∨ x = pb.1.2 then some pb.2 else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro pb hpb
    have hp : pb.1 ∈ rl := (List.of_mem_zip hpb).1
    refine if_neg ?_
    rintro (hc | hc)
    · rw [onRail_iff.mpr ⟨pb.1, hp, Or.inl hc⟩] at h; exact Bool.noConfusion h
    · rw [onRail_iff.mpr ⟨pb.1, hp, Or.inr hc⟩] at h; exact Bool.noConfusion h
  rw [hnone]
  rfl

theorem map_lookupBit_self {adj : AdjMatrix n} {χ : Colouring n} {u : List Bool}
    (hu : u.length = (rails adj χ).length) :
    (rails adj χ).map (fun p => lookupBit (rails adj χ) u p.1) = u := by
  refine List.ext_getElem (by simp [hu]) ?_
  intro i h1 h2
  rw [List.getElem_map]
  have hi : i < (rails adj χ).length := by simpa using h1
  exact lookupBit_eq (zip_getElem_mem hu hi) (Or.inl rfl)

/-- Transport permutes the bits: it is a reindexing along the rail bijection. -/
theorem transport_perm {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {u : List Bool}
    (hu : u.length = (rails adj χ).length) :
    List.Perm (transportWordR σ (rails adj χ) (rails adj' χ') u) u := by
  unfold transportWordR
  have h1 : List.Perm ((rails adj' χ').map (fun q => lookupBit (rails adj χ) u (σ.symm q.1)))
      (((rails adj χ).map (railMap σ)).map (fun q => lookupBit (rails adj χ) u (σ.symm q.1))) :=
    (rails_perm_conj h).map _
  refine h1.trans ?_
  rw [List.map_map]
  have h2 : (rails adj χ).map ((fun q => lookupBit (rails adj χ) u (σ.symm q.1)) ∘ railMap σ)
      = (rails adj χ).map (fun p => lookupBit (rails adj χ) u p.1) := by
    refine List.map_congr_left ?_
    intro p hp
    obtain ⟨b, hb⟩ := exists_zip_bit hu hp
    show lookupBit (rails adj χ) u (σ.symm (railMap σ p).1) = lookupBit (rails adj χ) u p.1
    rw [lookupBit_eq hb (Or.inl rfl)]
    refine lookupBit_eq hb ?_
    unfold railMap
    rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
    · rw [hs]; exact Or.inl (by simp)
    · rw [hs]; exact Or.inr (by simp)
  rw [h2, map_lookupBit_self hu]

/-- **The labelled word transports as a set of labelled bits.** Every `all`/`any` over the zip in
`flipFunK`'s guard and satisfier conditions is a statement at exactly this level. -/
theorem mem_zip_transport {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {u : List Bool}
    (hu : u.length = (rails adj χ).length) {q : Fin n × Fin n} {b : Bool} :
    (q, b) ∈ (rails adj' χ').zip (transportWordR σ (rails adj χ) (rails adj' χ') u)
      ↔ ∃ p, (p, b) ∈ (rails adj χ).zip u ∧ q = railMap σ p := by
  have hzip : ∀ (l : List (Fin n × Fin n)) (f : Fin n × Fin n → Bool),
      l.zip (l.map f) = l.map (fun a => (a, f a)) := by
    intro l f
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.zip_cons_cons, ih, List.map_cons]
  unfold transportWordR
  rw [hzip, List.mem_map]
  constructor
  · rintro ⟨q', hq', heq⟩
    have hq1 : q' = q := congrArg Prod.fst heq
    have hb : lookupBit (rails adj χ) u (σ.symm q'.1) = b := congrArg Prod.snd heq
    subst hq1
    obtain ⟨p, hp, rfl⟩ := (mem_rails_conj h).mp hq'
    obtain ⟨b', hb'⟩ := exists_zip_bit hu hp
    refine ⟨p, ?_, rfl⟩
    have : lookupBit (rails adj χ) u (σ.symm (railMap σ p).1) = b' := by
      refine lookupBit_eq hb' ?_
      unfold railMap
      rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
      · rw [hs]; exact Or.inl (by simp)
      · rw [hs]; exact Or.inr (by simp)
    rw [this] at hb
    rwa [← hb]
  · rintro ⟨p, hpb, rfl⟩
    have hp : p ∈ rails adj χ := (List.of_mem_zip hpb).1
    refine ⟨railMap σ p, (mem_rails_conj h).mpr ⟨p, hp, rfl⟩, ?_⟩
    have : lookupBit (rails adj χ) u (σ.symm (railMap σ p).1) = b := by
      refine lookupBit_eq hpb ?_
      unfold railMap
      rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
      · rw [hs]; exact Or.inl (by simp)
      · rw [hs]; exact Or.inr (by simp)
    rw [this]

theorem transportWordR_length (σ : Equiv.Perm (Fin n)) (rl rl' : List (Fin n × Fin n))
    (u : List Bool) : (transportWordR σ rl rl' u).length = rl'.length := by
  unfold transportWordR; rw [List.length_map]

/-- The lookup is multiplicative in the word — the step that lets `dotB` transport. -/
theorem lookupBit_and {adj : AdjMatrix n} {χ : Colouring n} {Y w : List Bool}
    (hY : Y.length = (rails adj χ).length) (hw : w.length = (rails adj χ).length) (x : Fin n) :
    lookupBit (rails adj χ) (Y.zipWith (· && ·) w) x
      = (lookupBit (rails adj χ) Y x && lookupBit (rails adj χ) w x) := by
  rcases honr : onRail (rails adj χ) x with _ | _
  · rw [lookupBit_off honr, lookupBit_off honr, lookupBit_off honr]; rfl
  · obtain ⟨p, hp, hx⟩ := onRail_iff.mp honr
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    have hz : (Y.zipWith (· && ·) w).length = (rails adj χ).length := by
      rw [List.length_zipWith, hY, hw]; simp
    have hmY := zip_getElem_mem hY hi
    have hmw := zip_getElem_mem hw hi
    have hmz := zip_getElem_mem hz hi
    rw [hpi] at hmY hmw hmz
    rw [lookupBit_eq hmY hx, lookupBit_eq hmw hx, lookupBit_eq hmz hx]
    rw [List.getElem_zipWith]

/-- **`dotB` is transport-invariant.** Both arguments are re-read along the same rail bijection, so
the parity of the coincidence count is unchanged. -/
theorem dotB_transport {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {Y w : List Bool}
    (hY : Y.length = (rails adj χ).length) (hw : w.length = (rails adj χ).length) :
    dotB (transportWordR σ (rails adj χ) (rails adj' χ') Y)
        (transportWordR σ (rails adj χ) (rails adj' χ') w) = dotB Y w := by
  have hz : (Y.zipWith (· && ·) w).length = (rails adj χ).length := by
    rw [List.length_zipWith, hY, hw]; simp
  have hsplit : transportWordR σ (rails adj χ) (rails adj' χ') (Y.zipWith (· && ·) w)
      = (transportWordR σ (rails adj χ) (rails adj' χ') Y).zipWith (· && ·)
        (transportWordR σ (rails adj χ) (rails adj' χ') w) := by
    refine List.ext_getElem (by simp [transportWordR]) ?_
    intro i h1 h2
    unfold transportWordR
    rw [List.getElem_map, List.getElem_zipWith, List.getElem_map, List.getElem_map]
    exact lookupBit_and hY hw _
  unfold dotB
  rw [← hsplit, xorList_eq_count, xorList_eq_count,
    ((transport_perm h hz).count_eq true)]

/-! ## 3. Emission transport — `flipFunK_conj`

`flipFunK` is `railImg` on the rails, and off them a guard plus a `uniqueFilter` over the satisfier
predicate. Each of the three transports: the first by the endpoint-value lemma, the other two because
they are `any`/`all` over the labelled word, which §2 moved memberwise. -/

theorem railImg_endpoint {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    {p : Fin n × Fin n} {b : Bool} (hpb : (p, b) ∈ (rails adj χ).zip w) :
    railImg (rails adj χ) w p.1 = some (if b then p.2 else p.1) ∧
    railImg (rails adj χ) w p.2 = some (if b then p.1 else p.2) := by
  have hp : p ∈ rails adj χ := (List.of_mem_zip hpb).1
  have hne := rails_ne hp
  have hu := zip_huniq hpb
  refine ⟨?_, ?_⟩
  · unfold railImg
    rw [findSome?_rail_lookup hpb hu (Or.inl rfl)]
    simp
  · unfold railImg
    rw [findSome?_rail_lookup hpb hu (Or.inr rfl)]
    rw [if_neg (fun hc => hne hc.symm)]

theorem railImg_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) (v : Fin n) :
    railImg (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ v)
      = (railImg (rails adj χ) w v).map σ := by
  have hTw : (transportWordR σ (rails adj χ) (rails adj' χ') w).length = (rails adj' χ').length :=
    transportWordR_length ..
  rcases honr : onRail (rails adj χ) v with _ | _
  · rw [(railImg_eq_none_iff hw).mpr honr,
      (railImg_eq_none_iff hTw).mpr (by rw [onRail_conj h v, honr])]
    rfl
  · obtain ⟨p, hp, hv⟩ := onRail_iff.mp honr
    obtain ⟨b, hpb⟩ := exists_zip_bit hw hp
    have hq : (railMap σ p, b) ∈ (rails adj' χ').zip
        (transportWordR σ (rails adj χ) (rails adj' χ') w) :=
      (mem_zip_transport h hw).mpr ⟨p, hpb, rfl⟩
    have hs := railImg_endpoint hpb
    have key : railImg (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ p.1)
          = some (if b then σ p.2 else σ p.1) ∧
        railImg (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ p.2)
          = some (if b then σ p.1 else σ p.2) := by
      have ht := railImg_endpoint hq
      rcases sPair_cases (σ p.1) (σ p.2) with hor | hor
      · rw [show railMap σ p = (σ p.1, σ p.2) from hor] at ht; exact ht
      · rw [show railMap σ p = (σ p.2, σ p.1) from hor] at ht; exact ⟨ht.2, ht.1⟩
    rcases hv with rfl | rfl
    · rw [key.1, hs.1]; cases b <;> simp
    · rw [key.2, hs.2]; cases b <;> simp

/-- `condFun` is endpoint-order invariant (it constrains both endpoints symmetrically). -/
theorem condFun_swap (adj : AdjMatrix n) (v x : Fin n) (a c : Fin n) (bit : Bool) :
    condFun adj v x ((a, c), bit) = condFun adj v x ((c, a), bit) := by
  unfold condFun
  cases bit <;>
    · rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, beq_iff_eq]
      tauto

theorem condFun_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v x : Fin n)
    (p : Fin n × Fin n) (b : Bool) :
    condFun adj' (σ v) (σ x) (railMap σ p, b) = condFun adj v x (p, b) := by
  have hbase : condFun adj' (σ v) (σ x) ((σ p.1, σ p.2), b) = condFun adj v x (p, b) := by
    unfold condFun
    have e1 : (if b then σ p.2 else σ p.1) = σ (if b then p.2 else p.1) := by cases b <;> rfl
    have e2 : (if b then σ p.1 else σ p.2) = σ (if b then p.1 else p.2) := by cases b <;> rfl
    simp only []
    rw [e1, e2, h.adjEq x (if b then p.2 else p.1), h.adjEq (if b then p.2 else p.1) x,
      h.adjEq x (if b then p.1 else p.2), h.adjEq (if b then p.1 else p.2) x,
      h.adjEq v p.1, h.adjEq p.1 v, h.adjEq v p.2, h.adjEq p.2 v]
  unfold railMap
  rcases sPair_cases (σ p.1) (σ p.2) with hor | hor
  · rw [hor]; exact hbase
  · rw [hor, condFun_swap]; exact hbase

theorem flipGuard_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) (v : Fin n) :
    flipGuard adj' (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ v)
      = flipGuard adj (rails adj χ) w v := by
  unfold flipGuard
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨qc, hqc, hval⟩
    obtain ⟨p, hpb, hq⟩ := (mem_zip_transport h hw).mp hqc
    refine ⟨(p, qc.2), hpb, ?_⟩
    rw [Bool.and_eq_true] at hval ⊢
    refine ⟨hval.1, ?_⟩
    rw [← touches_conj h v p, ← hq]
    exact hval.2
  · rintro ⟨pb, hpb, hval⟩
    refine ⟨(railMap σ pb.1, pb.2), (mem_zip_transport h hw).mpr ⟨pb.1, hpb, rfl⟩, ?_⟩
    rw [Bool.and_eq_true] at hval ⊢
    exact ⟨hval.1, by rw [touches_conj h v pb.1]; exact hval.2⟩

theorem satP_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) (v x : Fin n) :
    satP adj' χ' (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ v) (σ x)
      = satP adj χ (rails adj χ) w v x := by
  unfold satP
  have hcol : (χ' (σ x) == χ' (σ v)) = (χ x == χ v) := by rw [h.colEq x, h.colEq v]
  have hall : ((rails adj' χ').zip (transportWordR σ (rails adj χ) (rails adj' χ') w)).all
        (condFun adj' (σ v) (σ x))
      = ((rails adj χ).zip w).all (condFun adj v x) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro hA pb hpb
      have := hA (railMap σ pb.1, pb.2) ((mem_zip_transport h hw).mpr ⟨pb.1, hpb, rfl⟩)
      rwa [condFun_conj h v x pb.1 pb.2] at this
    · intro hA qc hqc
      obtain ⟨p, hpb, hq⟩ := (mem_zip_transport h hw).mp hqc
      have := hA (p, qc.2) hpb
      rw [← condFun_conj h v x p qc.2] at this
      rwa [← hq] at this
  rw [hcol, onRail_conj h x, hall]

/-- **★ Emission transports.** The candidate table on the relabelled graph, at the transported word,
is the `σ`-conjugate of the table here. -/
theorem flipFunK_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) (v : Fin n) :
    flipFunK adj' χ' (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) (σ v)
      = σ (flipFunK adj χ (rails adj χ) w v) := by
  rw [flipFunK_eq, flipFunK_eq, railImg_conj h hw v]
  cases hri : railImg (rails adj χ) w v with
  | some x => rfl
  | none =>
      simp only [Option.map_none]
      rw [flipGuard_conj h hw v]
      cases hg : flipGuard adj (rails adj χ) w v
      · rfl
      · rw [uniqueFilter_transport σ (fun x => satP_conj h hw v x)]
        cases huf : uniqueFilter (satP adj χ (rails adj χ) w v) with
        | none => rfl
        | some y => rfl

/-! ## 4a. The embed/restrict adjunction

`localRows` computes inside a vertex's *wire support* and re-embeds. The adjunction
`dotB (embedCols m cols y) u = dotB y (restrictCols cols u)` is what lets the local system and the
global one talk to each other; it is a counting lemma (the embedded word is zero off `cols`, and
`cols` is `Nodup` with entries `< m`, so the two supports are in bijection). -/

theorem getD_gen {α : Type} {l : List α} {j : Nat} (d : α) (h : j < l.length) : l.getD j d = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_range_map {m : Nat} (g : Nat → Bool) {j : Nat} (hj : j < m) :
    ((List.range m).map g).getD j false = g j := by
  have h1 : j < ((List.range m).map g).length := by simp [hj]
  rw [getD_in h1, List.getElem_map, List.getElem_range]

theorem getD_embedCols {m : Nat} {cols : List Nat} {y : List Bool} {j : Nat} (hj : j < m) :
    (embedCols m cols y).getD j false
      = (match cols.findIdx? (· == j) with | some k => y.getD k false | none => false) := by
  unfold embedCols
  exact getD_range_map _ hj

theorem findIdx?_nodup_self {cols : List Nat} (hnd : cols.Nodup) {k : Nat} (hk : k < cols.length) :
    cols.findIdx? (· == cols[k]) = some k := by
  refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hk, by simp, ?_⟩
  intro j hjk hc
  have hj : cols[j] = cols[k] := by simpa using hc
  have : j = k := (List.Nodup.getElem_inj_iff hnd).mp hj
  omega

theorem getD_restrictCols {cols : List Nat} {u : List Bool} {k : Nat} (hk : k < cols.length) :
    (restrictCols cols u).getD k false = u.getD (cols[k]) false := by
  unfold restrictCols
  have h1 : k < (cols.map (fun c => u.getD c false)).length := by simp [hk]
  rw [getD_in h1, List.getElem_map]

theorem embedCols_support {m : Nat} {cols : List Nat} {y : List Bool} {j : Nat} (hj : j < m)
    (h : (embedCols m cols y).getD j false = true) : j ∈ cols := by
  rw [getD_embedCols hj] at h
  cases hf : cols.findIdx? (· == j) with
  | none => rw [hf] at h; cases h
  | some k =>
      obtain ⟨hk1, hk2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      have hcj : cols[k] = j := by simpa using hk2
      rw [← hcj]
      exact List.getElem_mem hk1

theorem embed_restrict {m : Nat} {cols : List Nat} {Y : List Bool} (hY : Y.length = m)
    (hsupp : ∀ j, j < m → Y.getD j false = true → j ∈ cols) :
    embedCols m cols (restrictCols cols Y) = Y := by
  refine List.ext_getElem (by simp [hY]) ?_
  intro j h1 h2
  have hj : j < m := by simpa using h1
  rw [← getD_in h1, getD_embedCols hj, ← getD_in h2]
  cases hf : cols.findIdx? (· == j) with
  | none =>
      show false = Y.getD j false
      cases hyj : Y.getD j false
      · rfl
      · exfalso
        have hjc := hsupp j hj hyj
        rw [List.findIdx?_eq_none_iff] at hf
        exact absurd (hf j hjc) (by simp)
  | some k =>
      obtain ⟨hk1, hk2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      have hcj : cols[k] = j := by simpa using hk2
      simp only []
      rw [getD_restrictCols hk1, hcj]

theorem map_getD_range_self (cols : List Nat) :
    (List.range cols.length).map (fun k => cols.getD k 0) = cols := by
  refine List.ext_getElem (by simp) ?_
  intro k h1 h2
  rw [List.getElem_map, List.getElem_range]
  exact getD_gen 0 h2

theorem countP_range_eq_countP {m : Nat} {cols : List Nat} (hnd : cols.Nodup)
    (hlt : ∀ c ∈ cols, c < m) {P : Nat → Bool} (hsupp : ∀ j, j < m → P j = true → j ∈ cols) :
    (List.range m).countP P = cols.countP P := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hperm : List.Perm ((List.range m).filter P) (cols.filter P) := by
    refine (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (List.Nodup.filter _ hnd)).mpr ?_
    intro j
    rw [List.mem_filter, List.mem_filter]
    constructor
    · rintro ⟨hj, hp⟩
      exact ⟨hsupp j (List.mem_range.mp hj) hp, hp⟩
    · rintro ⟨hj, hp⟩
      exact ⟨List.mem_range.mpr (hlt j hj), hp⟩
  rw [hperm.length_eq]

/-- **★ The adjunction.** -/
theorem dotB_embed {m : Nat} {cols : List Nat} (hnd : cols.Nodup) (hlt : ∀ c ∈ cols, c < m)
    {y u : List Bool} (hy : y.length = cols.length) (hu : u.length = m) :
    dotB (embedCols m cols y) u = dotB y (restrictCols cols u) := by
  have hel : (embedCols m cols y).length = m := length_embedCols ..
  have hrl : (restrictCols cols u).length = cols.length := by simp [restrictCols]
  rw [dotB_eq_dotOn hel hu, dotB_eq_dotOn hy hrl, dotOn_eq_countP, dotOn_eq_countP]
  have hstep1 : (List.range m).countP
        (fun j => (embedCols m cols y).getD j false && u.getD j false)
      = cols.countP (fun j => (embedCols m cols y).getD j false && u.getD j false) := by
    refine countP_range_eq_countP hnd hlt ?_
    intro j hj hp
    rw [Bool.and_eq_true] at hp
    exact embedCols_support hj hp.1
  have hstep2 : ∀ F : Nat → Bool,
      cols.countP F = (List.range cols.length).countP (fun k => F (cols.getD k 0)) := by
    intro F
    conv_lhs => rw [← map_getD_range_self cols]
    rw [List.countP_map]
    rfl
  have hstep3 : (List.range cols.length).countP
        (fun k => (embedCols m cols y).getD (cols.getD k 0) false && u.getD (cols.getD k 0) false)
      = (List.range cols.length).countP
          (fun k => y.getD k false && (restrictCols cols u).getD k false) := by
    refine List.countP_congr ?_
    intro k hk
    have hk' : k < cols.length := List.mem_range.mp hk
    have hck : cols.getD k 0 = cols[k] := getD_gen 0 hk'
    simp only [hck]
    rw [getD_embedCols (hlt _ (List.getElem_mem hk')), findIdx?_nodup_self hnd hk',
      getD_restrictCols hk']
  rw [hstep1, hstep2 _, hstep3]

/-! ## 4b. `L`, basis-free

`inL` is stated against `localRows`, which is *pivot-dependent*: it is a `nullBasis` of the local
pattern system, and a Gaussian basis is a choice. `Lc` says the same thing without ever naming a
basis — `w` is killed by **every** wire-supported functional that kills the local patterns — and that
form transports memberwise. The two are equivalent precisely because `nullBasis` is both sound
(`dotB_nullBasis`) and complete (`spans_nullBasis`): part I is the bridge. -/

theorem mem_wiresOf_iff {adj : AdjMatrix n} {rl : List (Fin n × Fin n)} {v : Fin n} {j : Nat} :
    j ∈ wiresOf adj rl v ↔ ∃ h : j < rl.length, touches adj v (rl[j]) = true := by
  unfold wiresOf
  rw [List.mem_filter]
  constructor
  · rintro ⟨hj, hval⟩
    have hjl : j < rl.length := List.mem_range.mp hj
    refine ⟨hjl, ?_⟩
    rwa [List.getElem?_eq_getElem hjl] at hval
  · rintro ⟨hjl, htch⟩
    refine ⟨List.mem_range.mpr hjl, ?_⟩
    rwa [List.getElem?_eq_getElem hjl]

theorem wiresOf_nodup (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) (v : Fin n) :
    (wiresOf adj rl v).Nodup := List.Nodup.filter _ List.nodup_range

theorem wiresOf_lt {adj : AdjMatrix n} {rl : List (Fin n × Fin n)} {v : Fin n} {c : Nat}
    (hc : c ∈ wiresOf adj rl v) : c < rl.length := (mem_wiresOf_iff.mp hc).1

theorem length_mem_pats {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {v : Fin n} {π : List Bool} (h : π ∈ pats adj χ rl v) : π.length = rl.length := by
  obtain ⟨u, -, hu⟩ := List.mem_filterMap.mp h
  unfold patOf at hu
  split at hu
  · rw [← Option.some.inj hu]; simp
  · cases hu

theorem mem_localRows {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {v : Fin n} {r : List Bool} (h : r ∈ localRows adj χ rl v) :
    onRail rl v = false ∧ ∃ b ∈ nullBasis (wiresOf adj rl v).length
      ((pats adj χ rl v).map (restrictCols (wiresOf adj rl v))),
      r = embedCols rl.length (wiresOf adj rl v) b := by
  unfold localRows at h
  cases honr : onRail rl v
  · rw [honr, if_neg (by simp)] at h
    obtain ⟨b, hb, hrb⟩ := List.mem_map.mp h
    exact ⟨rfl, b, hb, hrb.symm⟩
  · rw [honr, if_pos rfl] at h
    cases h

theorem mem_localRows_mpr {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {v : Fin n} (honr : onRail rl v = false) {b : List Bool}
    (hb : b ∈ nullBasis (wiresOf adj rl v).length
      ((pats adj χ rl v).map (restrictCols (wiresOf adj rl v)))) :
    embedCols rl.length (wiresOf adj rl v) b ∈ localRows adj χ rl v := by
  unfold localRows
  rw [honr, if_neg (by simp)]
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

theorem mem_sysRows_iff {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {r : List Bool} : r ∈ sysRows adj χ rl ↔ ∃ v : Fin n, r ∈ localRows adj χ rl v := by
  unfold sysRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨v, -, hv⟩; exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩; exact ⟨v, List.mem_finRange v, hv⟩

/-- `Y` is supported in `v`'s wire set. -/
def SuppAt (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) (v : Fin n) (Y : List Bool) : Prop :=
  ∀ p b, (p, b) ∈ rl.zip Y → b = true → touches adj v p = true

theorem suppAt_iff_index {adj : AdjMatrix n} {rl : List (Fin n × Fin n)} {v : Fin n} {Y : List Bool}
    (hY : Y.length = rl.length) :
    SuppAt adj rl v Y ↔ ∀ j, j < rl.length → Y.getD j false = true → j ∈ wiresOf adj rl v := by
  constructor
  · intro hS j hj hbit
    refine mem_wiresOf_iff.mpr ⟨hj, ?_⟩
    refine hS rl[j] (Y[j]'(by omega)) ?_ ?_
    · exact zip_getElem_mem hY hj
    · rwa [← getD_in (show j < Y.length by omega)]
  · intro hI p b hpb hb
    obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hpb
    have hjl : j < rl.length := by simp at hj; omega
    rw [List.getElem_zip] at hgj
    have hp : rl[j] = p := congrArg Prod.fst hgj
    have hbv : Y[j]'(by omega) = b := congrArg Prod.snd hgj
    have hmem := hI j hjl (by rw [getD_in (show j < Y.length by omega), hbv]; exact hb)
    have := (mem_wiresOf_iff.mp hmem).2
    rwa [hp] at this

/-- **`L`, basis-free.** -/
def Lc (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (w : List Bool) : Prop :=
  ∀ v : Fin n, onRail rl v = false →
    ∀ Y : List Bool, Y.length = rl.length → SuppAt adj rl v Y →
      (∀ π ∈ pats adj χ rl v, dotB Y π = false) → dotB Y w = false

/-- **★ The bridge.** The executable, pivot-dependent `inL` and the basis-free `Lc` agree. -/
theorem inL_iff_Lc {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {w : List Bool} (hw : w.length = rl.length) :
    inL adj χ rl w = true ↔ Lc adj χ rl w := by
  constructor
  · intro hin v honr Y hY hsupp hperp
    rw [inL, List.all_eq_true] at hin
    set ws := wiresOf adj rl v with hws
    have hnd : ws.Nodup := wiresOf_nodup adj rl v
    have hlt : ∀ c ∈ ws, c < rl.length := fun c hc => wiresOf_lt hc
    have hrows : ∀ r ∈ (pats adj χ rl v).map (restrictCols ws), r.length = ws.length := by
      intro r hr
      obtain ⟨π, -, rfl⟩ := List.mem_map.mp hr
      simp [restrictCols]
    set y := restrictCols ws Y with hy
    have hylen : y.length = ws.length := by simp [hy, restrictCols]
    have hembed : embedCols rl.length ws y = Y :=
      embed_restrict hY ((suppAt_iff_index hY).mp hsupp)
    have hnull : ∀ r ∈ (pats adj χ rl v).map (restrictCols ws), dotB r y = false := by
      intro r hr
      obtain ⟨π, hπ, rfl⟩ := List.mem_map.mp hr
      rw [dotB_comm, ← dotB_embed hnd hlt hylen (length_mem_pats hπ), hembed]
      exact hperp π hπ
    have hspans := spans_nullBasis hrows hylen hnull
    have hbasis_len : ∀ b ∈ nullBasis ws.length ((pats adj χ rl v).map (restrictCols ws)),
        b.length = ws.length := fun b hb => length_mem_nullBasis hb
    have hkey : dotB (restrictCols ws w) y = false := by
      refine dotB_eq_false_of_spans hbasis_len hspans ?_
      intro b hb
      rw [dotB_comm, ← dotB_embed hnd hlt (hbasis_len b hb) hw]
      have hmem : embedCols rl.length ws b ∈ sysRows adj χ rl :=
        mem_sysRows_iff.mpr ⟨v, mem_localRows_mpr honr hb⟩
      have := hin _ hmem
      simpa using this
    rw [← hembed, dotB_embed hnd hlt hylen hw, dotB_comm]
    exact hkey
  · intro hLc
    rw [inL, List.all_eq_true]
    intro r hr
    obtain ⟨v, hv⟩ := mem_sysRows_iff.mp hr
    obtain ⟨honr, b, hb, rfl⟩ := mem_localRows hv
    set ws := wiresOf adj rl v with hws
    have hnd : ws.Nodup := wiresOf_nodup adj rl v
    have hlt : ∀ c ∈ ws, c < rl.length := fun c hc => wiresOf_lt hc
    have hblen : b.length = ws.length := length_mem_nullBasis hb
    have hrows : ∀ r ∈ (pats adj χ rl v).map (restrictCols ws), r.length = ws.length := by
      intro r hr
      obtain ⟨π, -, rfl⟩ := List.mem_map.mp hr
      simp [restrictCols]
    have hYlen : (embedCols rl.length ws b).length = rl.length := length_embedCols ..
    have hsupp : SuppAt adj rl v (embedCols rl.length ws b) := by
      refine (suppAt_iff_index hYlen).mpr ?_
      intro j hj hbit
      exact embedCols_support hj hbit
    have hperp : ∀ π ∈ pats adj χ rl v, dotB (embedCols rl.length ws b) π = false := by
      intro π hπ
      rw [dotB_embed hnd hlt hblen (length_mem_pats hπ)]
      rw [dotB_comm]
      exact dotB_nullBasis hrows (List.mem_map.mpr ⟨π, hπ, rfl⟩) hb
    have := hLc v honr _ hYlen hsupp hperp
    simp [this]

/-! ## 4c. `Lc` transports

The local patterns are the last structural ingredient. `patOf`'s emitted bit reads the rail's *first*
endpoint, which `sPair` may swap — but under `patOf`'s own shape condition (single-sided touch on
both sides, matching touch support) the bit is endpoint-order invariant, so the pattern transports as
a word. -/

/-- The per-rail shape condition inside `patOf`. -/
def shapeP (adj : AdjMatrix n) (v u : Fin n) (p : Fin n × Fin n) : Bool :=
  let va := isAdj adj v p.1; let vb := isAdj adj v p.2
  let wa := isAdj adj u p.1; let wb := isAdj adj u p.2
  !(va && vb) && !(wa && wb) && ((va || vb) == (wa || wb))

/-- The pattern bit `patOf` emits per rail. -/
def patBit (adj : AdjMatrix n) (v u : Fin n) (p : Fin n × Fin n) : Bool :=
  (isAdj adj v p.1 || isAdj adj v p.2) && (isAdj adj v p.1 != isAdj adj u p.1)

theorem patOf_eq (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (v u : Fin n) :
    patOf adj χ rl v u =
      if χ u == χ v && !onRail rl v && !onRail rl u && rl.all (shapeP adj v u) then
        some (rl.map (patBit adj v u))
      else none := rfl

theorem shapeP_swap (adj : AdjMatrix n) (v u a c : Fin n) :
    shapeP adj v u (a, c) = shapeP adj v u (c, a) := by
  unfold shapeP
  rcases isAdj adj v a <;> rcases isAdj adj v c <;> rcases isAdj adj u a <;>
    rcases isAdj adj u c <;> rfl

theorem patBit_swap_of_shape {adj : AdjMatrix n} {v u a c : Fin n}
    (hs : shapeP adj v u (a, c) = true) : patBit adj v u (a, c) = patBit adj v u (c, a) := by
  unfold shapeP at hs
  unfold patBit
  rcases hva : isAdj adj v a <;> rcases hvc : isAdj adj v c <;> rcases hua : isAdj adj u a <;>
    rcases huc : isAdj adj u c <;> simp_all

theorem shapeP_base {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v u : Fin n)
    (p : Fin n × Fin n) : shapeP adj' (σ v) (σ u) (σ p.1, σ p.2) = shapeP adj v u p := by
  unfold shapeP
  simp only []
  rw [isAdj_iso h v p.1, isAdj_iso h v p.2, isAdj_iso h u p.1, isAdj_iso h u p.2]

theorem patBit_base {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v u : Fin n)
    (p : Fin n × Fin n) : patBit adj' (σ v) (σ u) (σ p.1, σ p.2) = patBit adj v u p := by
  unfold patBit
  simp only []
  rw [isAdj_iso h v p.1, isAdj_iso h v p.2, isAdj_iso h u p.1]

theorem shapeP_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v u : Fin n)
    (p : Fin n × Fin n) : shapeP adj' (σ v) (σ u) (railMap σ p) = shapeP adj v u p := by
  unfold railMap
  rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
  · rw [hs]; exact shapeP_base h v u p
  · rw [hs, ← shapeP_swap]; exact shapeP_base h v u p

theorem patBit_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {v u : Fin n}
    {p : Fin n × Fin n} (hshape : shapeP adj v u p = true) :
    patBit adj' (σ v) (σ u) (railMap σ p) = patBit adj v u p := by
  have hs' : shapeP adj' (σ v) (σ u) (σ p.1, σ p.2) = true := by
    rw [shapeP_base h v u p]; exact hshape
  unfold railMap
  rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
  · rw [hs]; exact patBit_base h v u p
  · rw [hs, ← patBit_swap_of_shape hs']; exact patBit_base h v u p

theorem patOf_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v u : Fin n) :
    patOf adj' χ' (rails adj' χ') (σ v) (σ u)
      = (patOf adj χ (rails adj χ) v u).map
          (transportWordR σ (rails adj χ) (rails adj' χ')) := by
  rw [patOf_eq, patOf_eq]
  have hall : (rails adj' χ').all (shapeP adj' (σ v) (σ u))
      = (rails adj χ).all (shapeP adj v u) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro hA p hp
      have := hA (railMap σ p) ((mem_rails_conj h).mpr ⟨p, hp, rfl⟩)
      rwa [shapeP_conj h v u p] at this
    · intro hA q hq
      obtain ⟨p, hp, rfl⟩ := (mem_rails_conj h).mp hq
      rw [shapeP_conj h v u p]
      exact hA p hp
  rw [h.colEq u, h.colEq v, onRail_conj h v, onRail_conj h u, hall]
  cases hc : (χ u == χ v && !onRail (rails adj χ) v && !onRail (rails adj χ) u
      && (rails adj χ).all (shapeP adj v u))
  · rw [if_neg (by simp), if_neg (by simp)]
    rfl
  · rw [if_pos rfl, if_pos rfl]
    have hsh : ∀ p ∈ rails adj χ, shapeP adj v u p = true := by
      rw [Bool.and_eq_true] at hc
      exact List.all_eq_true.mp hc.2
    have hzip : (rails adj χ).zip ((rails adj χ).map (patBit adj v u))
        = (rails adj χ).map (fun p => (p, patBit adj v u p)) := by
      induction (rails adj χ) with
      | nil => rfl
      | cons a l ih => rw [List.map_cons, List.zip_cons_cons, ih, List.map_cons]
    refine congrArg some ?_
    unfold transportWordR
    refine List.map_congr_left ?_
    intro q hq
    obtain ⟨p, hp, rfl⟩ := (mem_rails_conj h).mp hq
    rw [patBit_conj h (hsh p hp)]
    have hmem : (p, patBit adj v u p)
        ∈ (rails adj χ).zip ((rails adj χ).map (patBit adj v u)) := by
      rw [hzip]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hend : σ.symm (railMap σ p).1 = p.1 ∨ σ.symm (railMap σ p).1 = p.2 := by
      unfold railMap
      rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
      · rw [hs]; exact Or.inl (by simp)
      · rw [hs]; exact Or.inr (by simp)
    exact (lookupBit_eq hmem hend).symm

theorem mem_pats_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') (v : Fin n)
    {π : List Bool} (hπ : π ∈ pats adj χ (rails adj χ) v) :
    transportWordR σ (rails adj χ) (rails adj' χ') π ∈ pats adj' χ' (rails adj' χ') (σ v) := by
  obtain ⟨u, -, hu⟩ := List.mem_filterMap.mp hπ
  refine List.mem_filterMap.mpr ⟨σ u, List.mem_finRange _, ?_⟩
  rw [patOf_conj h v u, hu]
  rfl

/-- Transport is invertible: `σ.symm` undoes it. -/
theorem transportWordR_roundtrip {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {u : List Bool}
    (hu : u.length = (rails adj χ).length) :
    transportWordR σ.symm (rails adj' χ') (rails adj χ)
        (transportWordR σ (rails adj χ) (rails adj' χ') u) = u := by
  unfold transportWordR
  rw [Equiv.symm_symm]
  rw [show (rails adj χ).map
      (fun p => lookupBit (rails adj' χ')
        ((rails adj' χ').map (fun q => lookupBit (rails adj χ) u (σ.symm q.1))) (σ p.1))
      = (rails adj χ).map (fun p => lookupBit (rails adj χ) u p.1) from ?_]
  · exact map_lookupBit_self hu
  · refine List.map_congr_left ?_
    intro p hp
    obtain ⟨b, hb⟩ := exists_zip_bit hu hp
    have hq : (railMap σ p, b) ∈ (rails adj' χ').zip
        (transportWordR σ (rails adj χ) (rails adj' χ') u) :=
      (mem_zip_transport h hu).mpr ⟨p, hb, rfl⟩
    have hend : σ p.1 = (railMap σ p).1 ∨ σ p.1 = (railMap σ p).2 := by
      unfold railMap
      rcases sPair_cases (σ p.1) (σ p.2) with hs | hs
      · rw [hs]; exact Or.inl rfl
      · rw [hs]; exact Or.inr rfl
    rw [lookupBit_eq hb (Or.inl rfl)]
    exact lookupBit_eq hq hend

/-- **★ `Lc` transports.** -/
theorem Lc_transport {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) (hLc : Lc adj χ (rails adj χ) w) :
    Lc adj' χ' (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w) := by
  intro v' honr' Y' hY' hsupp' hperp'
  have hlen' : (rails adj' χ').length = (rails adj χ).length := rails_length_conj h
  set v := σ.symm v' with hv
  have hσv : σ v = v' := Equiv.apply_symm_apply σ v'
  set Y := transportWordR σ.symm (rails adj' χ') (rails adj χ) Y' with hY
  have hYlen : Y.length = (rails adj χ).length := transportWordR_length ..
  have hTY : transportWordR σ (rails adj χ) (rails adj' χ') Y = Y' := by
    have := transportWordR_roundtrip h.symm (u := Y') (by rw [hY', hlen'])
    rwa [Equiv.symm_symm] at this
  have honr : onRail (rails adj χ) v = false := by
    rw [← onRail_conj h v, hσv]; exact honr'
  have hsupp : SuppAt adj (rails adj χ) v Y := by
    intro p b hpb hb
    have hq : (railMap σ p, b) ∈ (rails adj' χ').zip Y' := by
      rw [← hTY]
      exact (mem_zip_transport h hYlen).mpr ⟨p, hpb, rfl⟩
    have := hsupp' (railMap σ p) b hq hb
    rw [← hσv, touches_conj h v p] at this
    exact this
  have hperp : ∀ π ∈ pats adj χ (rails adj χ) v, dotB Y π = false := by
    intro π hπ
    have hπ' := mem_pats_conj h v hπ
    rw [hσv] at hπ'
    have := hperp' _ hπ'
    rw [← hTY, dotB_transport h hYlen (length_mem_pats hπ)] at this
    exact this
  have hres := hLc v honr Y hYlen hsupp hperp
  rw [← hTY, dotB_transport h hYlen hw]
  exact hres

/-! ## 5. `GensEquivariant kernelRefSupply`

The reference supply is `L`'s flips under the all-or-nothing gate. `L` transports (§4), emission
transports (§3), and the gate is a statement about `L`'s flips — so all three move together, and the
generator *set* on the relabelled graph is exactly the set of `σ`-conjugates. -/

theorem inL_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) :
    inL adj' χ' (rails adj' χ') (transportWordR σ (rails adj χ) (rails adj' χ') w)
      = inL adj χ (rails adj χ) w := by
  rw [Bool.eq_iff_iff,
    inL_iff_Lc (transportWordR_length ..), inL_iff_Lc hw]
  constructor
  · intro hL'
    have := Lc_transport h.symm (w := transportWordR σ (rails adj χ) (rails adj' χ') w)
      (transportWordR_length ..) hL'
    rwa [transportWordR_roundtrip h hw] at this
  · exact Lc_transport h hw

theorem mem_kernelWords_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w' : List Bool} :
    w' ∈ kernelWords adj' χ' ↔
      ∃ w ∈ kernelWords adj χ, w' = transportWordR σ (rails adj χ) (rails adj' χ') w := by
  unfold kernelWords
  constructor
  · intro hw'
    obtain ⟨hmem, hin⟩ := List.mem_filter.mp hw'
    have hlen' : w'.length = (rails adj' χ').length := mem_allWords_iff.mp hmem
    have hback : transportWordR σ.symm (rails adj' χ') (rails adj χ) w' ∈
        (allWords (rails adj χ).length) :=
      mem_allWords_iff.mpr (transportWordR_length ..)
    have hround : transportWordR σ (rails adj χ) (rails adj' χ')
        (transportWordR σ.symm (rails adj' χ') (rails adj χ) w') = w' := by
      have := transportWordR_roundtrip h.symm (u := w') hlen'
      rwa [Equiv.symm_symm] at this
    refine ⟨transportWordR σ.symm (rails adj' χ') (rails adj χ) w',
      List.mem_filter.mpr ⟨hback, ?_⟩, hround.symm⟩
    rw [← inL_conj h (transportWordR_length ..), hround]
    exact hin
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hmem, hin⟩ := List.mem_filter.mp hw
    have hlen : w.length = (rails adj χ).length := mem_allWords_iff.mp hmem
    exact List.mem_filter.mpr
      ⟨mem_allWords_iff.mpr (transportWordR_length ..), by rw [inL_conj h hlen]; exact hin⟩

theorem length_mem_kernelWords {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    (hw : w ∈ kernelWords adj χ) : w.length = (rails adj χ).length :=
  mem_allWords_iff.mp (List.mem_filter.mp hw).1

/-- Emission plus gate, conjugated. -/
theorem permOf_flipFunK_conj {σ : Equiv.Perm (Fin n)} {adj : AdjMatrix n} {χ : Colouring n}
    {adj' : AdjMatrix n} {χ' : Colouring n} (h : IsoTo σ adj χ adj' χ') {w : List Bool}
    (hw : w.length = (rails adj χ).length) :
    permOf (flipFunK adj' χ' (rails adj' χ')
        (transportWordR σ (rails adj χ) (rails adj' χ') w))
      = (permOf (flipFunK adj χ (rails adj χ) w)).map (fun t => σ * t * σ⁻¹) := by
  have hfun : flipFunK adj' χ' (rails adj' χ')
        (transportWordR σ (rails adj χ) (rails adj' χ') w)
      = fun x => σ (flipFunK adj χ (rails adj χ) w (σ.symm x)) := by
    funext x
    have := flipFunK_conj h hw (σ.symm x)
    rwa [Equiv.apply_symm_apply] at this
  rw [hfun, Deck2.permOf_conj]

theorem refGate_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    RefGate (relabelAdj σ adj) (transportColouring σ χ) ↔ RefGate adj χ := by
  have h : IsoTo σ adj χ (relabelAdj σ adj) (transportColouring σ χ) := isoTo_relabel σ adj χ
  constructor
  · intro hG w hw
    have hlen := length_mem_kernelWords hw
    obtain ⟨ρ', hρ', haut'⟩ := hG _ ((mem_kernelWords_conj h).mpr ⟨w, hw, rfl⟩)
    rw [permOf_flipFunK_conj h hlen] at hρ'
    cases hρ : permOf (flipFunK adj χ (rails adj χ) w) with
    | none => rw [hρ] at hρ'; cases hρ'
    | some ρ =>
        refine ⟨ρ, rfl, ?_⟩
        rw [hρ] at hρ'
        have hval : ρ' = σ * ρ * σ⁻¹ := (Option.some.inj hρ').symm
        rw [hval] at haut'
        exact (Consume.isColAut_conj_iff σ).mp haut'
  · intro hG w' hw'
    obtain ⟨w, hw, rfl⟩ := (mem_kernelWords_conj h).mp hw'
    obtain ⟨ρ, hρ, haut⟩ := hG w hw
    refine ⟨σ * ρ * σ⁻¹, ?_, (Consume.isColAut_conj_iff σ).mpr haut⟩
    rw [permOf_flipFunK_conj h (length_mem_kernelWords hw), hρ]
    rfl

/-- **★★★ The reference supply is equivariant.** -/
theorem gensEquivariant_kernelRefSupply :
    SupplyTransport.GensEquivariant (kernelRefSupply (n := n)) := by
  intro σ adj χ g
  rw [gens_kernelRefSupply, gens_kernelRefSupply]
  have h : IsoTo σ adj χ (relabelAdj σ adj) (transportColouring σ χ) := isoTo_relabel σ adj χ
  by_cases hg : RefGate adj χ
  · rw [refGens_pos hg, refGens_pos ((refGate_conj σ adj χ).mpr hg)]
    constructor
    · intro hmem
      obtain ⟨w', hw', hval⟩ := List.mem_filterMap.mp hmem
      obtain ⟨w, hw, rfl⟩ := (mem_kernelWords_conj h).mp hw'
      rw [permOf_flipFunK_conj h (length_mem_kernelWords hw)] at hval
      cases hρ : permOf (flipFunK adj χ (rails adj χ) w) with
      | none => rw [hρ] at hval; cases hval
      | some ρ =>
          rw [hρ] at hval
          exact ⟨ρ, List.mem_filterMap.mpr ⟨w, hw, hρ⟩, (Option.some.inj hval).symm⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨w, hw, hval⟩ := List.mem_filterMap.mp hk
      refine List.mem_filterMap.mpr
        ⟨transportWordR σ (rails adj χ) (rails (relabelAdj σ adj) (transportColouring σ χ)) w,
          (mem_kernelWords_conj h).mpr ⟨w, hw, rfl⟩, ?_⟩
      rw [permOf_flipFunK_conj h (length_mem_kernelWords hw), hval]
      rfl
  · rw [refGens_neg hg, refGens_neg (fun hc => hg ((refGate_conj σ adj χ).mp hc))]
    simp

theorem supplyEquivariant_kernelRefSupply :
    SupplyTransport.SupplyEquivariant (kernelRefSupply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_kernelRefSupply

/-! ## 6. ★★★ THE CAPSTONES — `kernelSupply` enters the record

`kernelSupply` itself is **not** `GensEquivariant` (its Gaussian basis is pivot-order dependent — a
genuine trap-#7 choice, and the basis lists differ pointwise under relabelling). What is canonical is
the *group* it generates, and that is exactly what `OrbitPrune.SameOrbits` asks for: §5 gives the
equivariant reference, `KernelRef` gives the orbit equality, and the two together discharge ① for the
kernel supply with **no** equivariance obligation on the executable object. -/

/-- **★★★ The guarded (blind) mixed canonizer over the kernel supply.** -/
theorem kernelSupply_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (kernelSupply (n := n))))) :=
  OrbitPrune.guarded_mixed_canonizer_of_sameOrbits Force.keyEquivariant_lookahead
    supplyEquivariant_kernelRefSupply sameOrbits_kernelRef

/-- **★★★ The FUSED (resolver-aware) canonizer over the kernel supply.** -/
theorem kernelSupply_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (kernelSupply (n := n)))) :=
  Select.selNode_canonizer_of_sameOrbits Force.keyEquivariant_lookahead
    supplyEquivariant_kernelRefSupply sameOrbits_kernelRef

/-- The kernel-extended record's **reference** composite (equivariant, proof-side only). -/
abbrev recordRefSupply : Supply n :=
  Deck.appendSupply (Fold.foldSupply (n := n))
    (Deck.appendSupply (Deck.deckSupply (n := n))
      (Deck.appendSupply (Deck2.deck2Supply (n := n)) (kernelRefSupply (n := n))))

/-- The kernel-extended **record** consume-side supply. -/
abbrev recordSupply : Supply n :=
  Deck.appendSupply (Fold.foldSupply (n := n))
    (Deck.appendSupply (Deck.deckSupply (n := n))
      (Deck.appendSupply (Deck2.deck2Supply (n := n)) (kernelSupply (n := n))))

theorem supplyEquivariant_recordRefSupply :
    SupplyTransport.SupplyEquivariant (recordRefSupply (n := n)) :=
  Deck.supplyEquivariant_appendSupply Fold.gensEquivariant_foldSupply
    (Deck.gensEquivariant_appendSupply Deck.gensEquivariant_deckSupply
      (Deck.gensEquivariant_appendSupply Deck2.gensEquivariant_deck2Supply
        gensEquivariant_kernelRefSupply))

theorem sameOrbits_recordSupply :
    OrbitPrune.SameOrbits (recordRefSupply (n := n)) (recordSupply (n := n)) :=
  sameOrbits_appendSupply (sameOrbits_appendSupply (sameOrbits_appendSupply sameOrbits_kernelRef))

/-- **★★★ THE C3a CANONIZER OF RECORD**: force = the holonomy key, consume =
`foldSupply ++ deckSupply ++ deck2Supply ++ kernelSupply`. The F₂ kernel supply is now inside the
record object, with ① discharged through the `SameOrbits` reduction rather than by an (impossible)
pointwise equivariance of the Gaussian basis. -/
theorem holKey_foldDeck2Kernel_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (recordSupply (n := n)))) :=
  Select.selNode_canonizer_of_sameOrbits Hol.keyEquivariant_holKeyFast
    supplyEquivariant_recordRefSupply sameOrbits_recordSupply

/-- The all-fast form of the extended record (`foldSupplyFast` for the F2a component) — the form the
measurements run. -/
theorem holKey_foldDeck2KernelFast_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (Deck.appendSupply (Fold.foldSupplyFast (n := n))
            (Deck.appendSupply (Deck.deckSupply (n := n))
              (Deck.appendSupply (Deck2.deck2Supply (n := n)) (kernelSupply (n := n))))))) := by
  rw [Fold.foldSupplyFast_eq]
  exact holKey_foldDeck2Kernel_selNode_canonizer

/-- **③ transfers too**: the residue predicate is read off the same narrowing, so a `HandledS`
certificate for the reference composite is one for the record. -/
theorem handledS_recordSupply {key : Force.Key n} {adj : AdjMatrix n}
    (h : Select.HandledS key (recordRefSupply (n := n)) adj) :
    Select.HandledS key (recordSupply (n := n)) adj :=
  Select.handledS_of_sameOrbits sameOrbits_recordSupply h

end Kernel
end ChainDescent
