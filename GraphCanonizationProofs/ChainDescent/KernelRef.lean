import ChainDescent.KernelFlip
import ChainDescent.TreePrune

/-!
# `C3a` tranche 2, part III — the set-level reference supply and `SameOrbits`

The ① reduction target for `kernelSupply` (`KernelSupply.lean` header): the executable supply emits
a pivot-order-dependent *basis*, so `GensEquivariant` is false pointwise — but the all-or-nothing
gate makes the emitted **group** canonical. This file builds the set-level reference
`kernelRefSupply` — the flips of **every** word of the recovered space `L` (enumerated; proof-only,
never run) under the *same* all-or-nothing gate — and proves

> **`SameOrbits kernelRefSupply kernelSupply`** (`sameOrbits_kernelRef`)

by the gate-transfer argument: the gates are *equivalent* (`refGate_of_kernelGate` /
`kernelGate_of_refGate`), because a verified basis propagates to every word of `L` through the
Gaussian span (`spans_nullBasis`) and the flip-composition product lemma (`flipFunK_xor`), while the
basis itself lies in `L` (`dotB_nullBasis`). When both gates pass, every reference generator is a
*product* of kernel generators (the `TreePrune.Reaches` license) and every kernel generator is a
reference generator; when both fail, both verified sets are empty. Either way the orbit relations
coincide, and `OrbitPrune`'s reduction will hand `①` to the kernel supply from the reference's
equivariance with no equivariance proof on the pivot-dependent basis.

`sameOrbits_appendSupply` extends the license through `appendSupply`, so the swap happens inside the
record composite `fold ++ deck ++ deck2 ++ kernel`.

The reference's own equivariance is **`KernelTransport.lean`** (part IV, LANDED 2026-07-19:
`gensEquivariant_kernelRefSupply`), which also carries the capstones — so the reduction promised
above is closed and `kernelSupply` is in the record object.
-/

namespace ChainDescent
namespace Kernel

open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach)
open ChainDescent.Deck2 (permOf)
open ChainDescent.TreePrune (Reaches wordReach_of_reaches)

variable {n : Nat}

/-! ## 1. Word enumeration and the system rows -/

/-- All Bool words of length `m` (proof-side enumeration; `2^m`, never executed by the canonizer). -/
def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allWords m).flatMap (fun w => [false :: w, true :: w])

theorem mem_allWords_iff {m : Nat} {w : List Bool} : w ∈ allWords m ↔ w.length = m := by
  induction m generalizing w with
  | zero =>
      cases w <;> simp [allWords]
  | succ m ih =>
      simp only [allWords, List.mem_flatMap]
      constructor
      · rintro ⟨w', hw', hmem⟩
        have hcase : w = false :: w' ∨ w = true :: w' := by simpa using hmem
        rcases hcase with rfl | rfl <;> simp [ih.mp hw']
      · intro hlen
        cases w with
        | nil => simp at hlen
        | cons b w' =>
            refine ⟨w', ih.mpr (by simpa using hlen), ?_⟩
            cases b <;> simp

/-- The global constraint system (the rows `kernelBasis` eliminates). -/
def sysRows (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) :
    List (List Bool) :=
  (List.finRange n).flatMap (localRows adj χ rl)

theorem kernelBasis_eq (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) :
    kernelBasis adj χ rl = nullBasis rl.length (sysRows adj χ rl) := rfl

@[simp] theorem length_embedCols (m : Nat) (cols : List Nat) (r : List Bool) :
    (embedCols m cols r).length = m := by simp [embedCols]

theorem mem_sysRows_length {adj : AdjMatrix n} {χ : Colouring n} {rl : List (Fin n × Fin n)}
    {r : List Bool} (hr : r ∈ sysRows adj χ rl) : r.length = rl.length := by
  obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hr
  unfold localRows at hv
  cases honr : onRail rl v
  · rw [honr] at hv
    rw [if_neg (by simp)] at hv
    obtain ⟨r', -, rfl⟩ := List.mem_map.mp hv
    exact length_embedCols ..
  · rw [honr] at hv
    rw [if_pos rfl] at hv
    cases hv

/-! ## 2. `L`-membership and the reference supply -/

/-- Decidable membership in the gauge space `L` (null against every system row). -/
def inL (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (w : List Bool) :
    Bool :=
  (sysRows adj χ rl).all (fun r => !dotB r w)

/-- Every word of `L` (full-length null words) — the canonical SET the reference flips. -/
def kernelWords (adj : AdjMatrix n) (χ : Colouring n) : List (List Bool) :=
  (allWords (rails adj χ).length).filter (inL adj χ (rails adj χ))

/-- The set-level reference generators: flips of every `L`-word, same all-or-nothing gate. -/
def kernelRefGens (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  let rl := rails adj χ
  let words := kernelWords adj χ
  let cands := words.filterMap (fun w => permOf (flipFunK adj χ rl w))
  if cands.length == words.length &&
     cands.all (fun ρ => decide (IsColAut adj χ ρ)) then cands else []

/-- **The reference supply** — proof-side only (exponential enumeration; cost never billed because
it never enters the record object; it exists to carry equivariance). -/
def kernelRefSupply : Supply n := fun adj χ => (kernelRefGens adj χ, 0)

theorem gens_kernelSupply (adj : AdjMatrix n) (χ : Colouring n) :
    gens (kernelSupply (n := n)) adj χ = kernelGens adj χ := rfl

theorem gens_kernelRefSupply (adj : AdjMatrix n) (χ : Colouring n) :
    gens (kernelRefSupply (n := n)) adj χ = kernelRefGens adj χ := rfl

/-! ## 3. The gate, characterized -/

private theorem filterMap_length_eq_iff {α β : Type} {f : α → Option β} {l : List α} :
    (l.filterMap f).length = l.length ↔ ∀ a ∈ l, (f a).isSome = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.filterMap_cons]
      cases hf : f a with
      | none =>
          simp only []
          constructor
          · intro h
            exfalso
            have hle := List.length_filterMap_le f l
            rw [List.length_cons] at h
            omega
          · intro h
            have hsome := h a (List.mem_cons_self ..)
            rw [hf] at hsome
            cases hsome
      | some b =>
          simp only [List.length_cons]
          constructor
          · intro h x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · rw [hf]; rfl
            · exact ih.mp (by omega) x hx
          · intro h
            have hres := ih.mpr (fun x hx => h x (List.mem_cons_of_mem _ hx))
            omega

/-- The all-or-nothing gate over a word list is exactly "every word emits and verifies". -/
theorem gate_true_iff (adj : AdjMatrix n) (χ : Colouring n) (W : List (List Bool)) :
    (((W.filterMap (fun w => permOf (flipFunK adj χ (rails adj χ) w))).length == W.length)
      && (W.filterMap (fun w => permOf (flipFunK adj χ (rails adj χ) w))).all
           (fun ρ => decide (IsColAut adj χ ρ))) = true
    ↔ ∀ w ∈ W, ∃ ρ, permOf (flipFunK adj χ (rails adj χ) w) = some ρ ∧ IsColAut adj χ ρ := by
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨hlen, hall⟩ w hw
    cases hρ : permOf (flipFunK adj χ (rails adj χ) w) with
    | none =>
        exfalso
        have hsome := filterMap_length_eq_iff.mp hlen w hw
        rw [hρ] at hsome
        cases hsome
    | some ρ =>
        refine ⟨ρ, rfl, ?_⟩
        have hmem : ρ ∈ W.filterMap (fun w => permOf (flipFunK adj χ (rails adj χ) w)) :=
          List.mem_filterMap.mpr ⟨w, hw, hρ⟩
        simpa using hall ρ hmem
  · intro h
    constructor
    · refine filterMap_length_eq_iff.mpr (fun w hw => ?_)
      obtain ⟨ρ, hρ, -⟩ := h w hw
      rw [hρ]
      rfl
    · intro ρ hρ
      obtain ⟨w, hw, hs⟩ := List.mem_filterMap.mp hρ
      obtain ⟨ρ', hρ', haut⟩ := h w hw
      rw [hρ'] at hs
      obtain rfl := Option.some.inj hs
      simpa using haut

/-- The kernel gate, in `Prop` form: every basis word emits and verifies. -/
def KernelGate (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ b ∈ kernelBasis adj χ (rails adj χ),
    ∃ ρ, permOf (flipFunK adj χ (rails adj χ) b) = some ρ ∧ IsColAut adj χ ρ

/-- The reference gate: every `L`-word emits and verifies. -/
def RefGate (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ w ∈ kernelWords adj χ,
    ∃ ρ, permOf (flipFunK adj χ (rails adj χ) w) = some ρ ∧ IsColAut adj χ ρ

theorem kernelGens_pos {adj : AdjMatrix n} {χ : Colouring n} (h : KernelGate adj χ) :
    kernelGens adj χ = (kernelBasis adj χ (rails adj χ)).filterMap
      (fun w => permOf (flipFunK adj χ (rails adj χ) w)) := by
  unfold kernelGens
  rw [if_pos ((gate_true_iff adj χ _).mpr h)]

theorem kernelGens_neg {adj : AdjMatrix n} {χ : Colouring n} (h : ¬ KernelGate adj χ) :
    kernelGens adj χ = [] := by
  unfold kernelGens
  rw [if_neg (fun hc => h ((gate_true_iff adj χ _).mp hc))]

theorem refGens_pos {adj : AdjMatrix n} {χ : Colouring n} (h : RefGate adj χ) :
    kernelRefGens adj χ = (kernelWords adj χ).filterMap
      (fun w => permOf (flipFunK adj χ (rails adj χ) w)) := by
  unfold kernelRefGens
  rw [if_pos ((gate_true_iff adj χ _).mpr h)]

theorem refGens_neg {adj : AdjMatrix n} {χ : Colouring n} (h : ¬ RefGate adj χ) :
    kernelRefGens adj χ = [] := by
  unfold kernelRefGens
  rw [if_neg (fun hc => h ((gate_true_iff adj χ _).mp hc))]

/-! ## 4. Gate transfer — the two gates are equivalent -/

/-- The zero word's flip is the identity table. -/
theorem flipFunK_zeroW (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    flipFunK adj χ (rails adj χ) (zeroW (rails adj χ).length) v = v := by
  have hlz : (zeroW (rails adj χ).length).length = (rails adj χ).length := by simp
  rw [flipFunK_eq]
  rcases honr : onRail (rails adj χ) v with _ | _
  · rw [(railImg_eq_none_iff hlz).mpr honr]
    simp only []
    have hg : flipGuard adj (rails adj χ) (zeroW (rails adj χ).length) v = false := by
      rcases hcase : flipGuard adj (rails adj χ) (zeroW (rails adj χ).length) v with _ | _
      · rfl
      · exfalso
        unfold flipGuard at hcase
        obtain ⟨i, hi, hf⟩ := (any_zip_iff hlz _).mp hcase
        simp at hf
    rw [hg]
    rw [if_neg (by simp)]
  · obtain ⟨p, hp, hval⟩ := onRail_iff.mp honr
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    have hne := rails_ne hp
    have hzm : (p, false) ∈ (rails adj χ).zip (zeroW (rails adj χ).length) :=
      (mem_zip_iff_getElem' hlz).mpr ⟨i, hi, hpi, by simp⟩
    have hu := zip_huniq hzm
    rcases hval with rfl | rfl
    · have hri : railImg (rails adj χ) (zeroW (rails adj χ).length) p.1 = some p.1 := by
        unfold railImg
        rw [findSome?_rail_lookup hzm hu (Or.inl rfl)]
        simp
      rw [hri]
    · have hri : railImg (rails adj χ) (zeroW (rails adj χ).length) p.2 = some p.2 := by
        have hne' : ¬ (p.2 = p.1) := fun h => hne h.symm
        unfold railImg
        rw [findSome?_rail_lookup hzm hu (Or.inr rfl)]
        simp [hne']
      rw [hri]

/-- **★★ THE SPAN INDUCTION.** Under a verified basis, every spanned word's flip emits, verifies,
and lies in the group the kernel supply generates (`Reaches` — the P3b product license). -/
theorem flip_emits_of_spans {adj : AdjMatrix n} {χ : Colouring n}
    (hbasis : ∀ b ∈ kernelBasis adj χ (rails adj χ),
      ∃ ρ, permOf (flipFunK adj χ (rails adj χ) b) = some ρ ∧ IsColAut adj χ ρ ∧
        ρ ∈ verified (kernelSupply (n := n)) adj χ)
    {w : List Bool}
    (hw : Spans (rails adj χ).length (kernelBasis adj χ (rails adj χ)) w) :
    ∃ ρ, permOf (flipFunK adj χ (rails adj χ) w) = some ρ ∧ IsColAut adj χ ρ ∧
      Reaches (verified (kernelSupply (n := n)) adj χ) ρ := by
  have hblen : ∀ b ∈ kernelBasis adj χ (rails adj χ), b.length = (rails adj χ).length := by
    intro b hb
    rw [kernelBasis_eq] at hb
    exact length_mem_nullBasis hb
  induction hw with
  | zero =>
      refine ⟨1, ?_, Consume.IsColAut.one adj χ, TreePrune.Reaches.one _⟩
      refine Deck2.permOf_eq_some_of_eq (fun v => ?_)
      rw [flipFunK_zeroW]
      rfl
  | step hb hwS ih =>
      obtain ⟨ρb, hρb, hautb, hmemb⟩ := hbasis _ hb
      obtain ⟨ρw, hρw, hautw, hreachw⟩ := ih
      refine ⟨ρb * ρw, ?_, Consume.IsColAut.comp hautb hautw,
        TreePrune.Reaches.mul (TreePrune.Reaches.gen hmemb) hreachw⟩
      refine Deck2.permOf_eq_some_of_eq (fun v => ?_)
      rw [flipFunK_xor (hblen _ hb) (hwS.length hblen) hρb hautb hρw hautw v]
      rfl

/-- A basis word is an `L`-word. -/
theorem basis_mem_kernelWords {adj : AdjMatrix n} {χ : Colouring n} {b : List Bool}
    (hb : b ∈ kernelBasis adj χ (rails adj χ)) : b ∈ kernelWords adj χ := by
  rw [kernelBasis_eq] at hb
  refine List.mem_filter.mpr ⟨mem_allWords_iff.mpr (length_mem_nullBasis hb), ?_⟩
  unfold inL
  rw [List.all_eq_true]
  intro r hr
  rw [dotB_nullBasis (fun r hr => mem_sysRows_length hr) hr hb]
  rfl

/-- An `L`-word is spanned by the basis (Gaussian completeness, re-based). -/
theorem spans_of_mem_kernelWords {adj : AdjMatrix n} {χ : Colouring n} {w : List Bool}
    (hw : w ∈ kernelWords adj χ) :
    Spans (rails adj χ).length (kernelBasis adj χ (rails adj χ)) w := by
  obtain ⟨hwmem, hwin⟩ := List.mem_filter.mp hw
  have hnull : ∀ r ∈ sysRows adj χ (rails adj χ), dotB r w = false := by
    intro r hr
    have hval := List.all_eq_true.mp hwin r hr
    rw [Bool.not_eq_true'] at hval
    exact hval
  have hspan := spans_nullBasis (fun r hr => mem_sysRows_length hr)
    (mem_allWords_iff.mp hwmem) hnull
  rw [← kernelBasis_eq] at hspan
  exact hspan

/-- The strengthened basis hypothesis available whenever the kernel gate passes. -/
theorem basis_emits_of_kernelGate {adj : AdjMatrix n} {χ : Colouring n}
    (h : KernelGate adj χ) :
    ∀ b ∈ kernelBasis adj χ (rails adj χ),
      ∃ ρ, permOf (flipFunK adj χ (rails adj χ) b) = some ρ ∧ IsColAut adj χ ρ ∧
        ρ ∈ verified (kernelSupply (n := n)) adj χ := by
  intro b hb
  obtain ⟨ρ, hρ, haut⟩ := h b hb
  refine ⟨ρ, hρ, haut, ?_⟩
  refine List.mem_filter.mpr ⟨?_, by simpa using haut⟩
  rw [gens_kernelSupply, kernelGens_pos h]
  exact List.mem_filterMap.mpr ⟨b, hb, hρ⟩

/-- **★ The kernel gate implies the reference gate** — "the whole basis verifies" propagates to
every word of `L` (span + product lemma). This is the canonicity content of all-or-nothing. -/
theorem refGate_of_kernelGate {adj : AdjMatrix n} {χ : Colouring n} (h : KernelGate adj χ) :
    RefGate adj χ := by
  intro w hw
  obtain ⟨ρ, hρ, haut, -⟩ :=
    flip_emits_of_spans (basis_emits_of_kernelGate h) (spans_of_mem_kernelWords hw)
  exact ⟨ρ, hρ, haut⟩

/-- The reference gate implies the kernel gate (the basis is a subset of `L`). -/
theorem kernelGate_of_refGate {adj : AdjMatrix n} {χ : Colouring n} (h : RefGate adj χ) :
    KernelGate adj χ :=
  fun b hb => h b (basis_mem_kernelWords hb)

/-! ## 5. ★★★ `SameOrbits` — the reference and the kernel prove the same orbits -/

theorem sameOrbits_kernelRef :
    OrbitPrune.SameOrbits (kernelRefSupply (n := n)) (kernelSupply (n := n)) := by
  intro adj χ u v
  by_cases hK : KernelGate adj χ
  · have hR : RefGate adj χ := refGate_of_kernelGate hK
    constructor
    · refine wordReach_of_reaches (fun g hg => ?_)
      have hgens := (List.mem_filter.mp hg).1
      rw [gens_kernelRefSupply, refGens_pos hR] at hgens
      obtain ⟨w, hw, hs⟩ := List.mem_filterMap.mp hgens
      obtain ⟨ρ, hρ, -, hreach⟩ :=
        flip_emits_of_spans (basis_emits_of_kernelGate hK) (spans_of_mem_kernelWords hw)
      rw [hρ] at hs
      obtain rfl := Option.some.inj hs
      exact hreach
    · refine wordReach_of_reaches (fun g hg => ?_)
      refine TreePrune.Reaches.gen ?_
      obtain ⟨hgmem, hgaut⟩ := List.mem_filter.mp hg
      rw [gens_kernelSupply, kernelGens_pos hK] at hgmem
      obtain ⟨b, hb, hs⟩ := List.mem_filterMap.mp hgmem
      refine List.mem_filter.mpr ⟨?_, hgaut⟩
      rw [gens_kernelRefSupply, refGens_pos hR]
      exact List.mem_filterMap.mpr ⟨b, basis_mem_kernelWords hb, hs⟩
  · have hR : ¬ RefGate adj χ := fun hR => hK (kernelGate_of_refGate hR)
    have h1 : verified (kernelRefSupply (n := n)) adj χ = [] := by
      unfold Consume.verified
      rw [gens_kernelRefSupply, refGens_neg hR]
      rfl
    have h2 : verified (kernelSupply (n := n)) adj χ = [] := by
      unfold Consume.verified
      rw [gens_kernelSupply, kernelGens_neg hK]
      rfl
    rw [h1, h2]

/-! ## 6. `SameOrbits` passes through `appendSupply` — the record-composite license -/

theorem verified_appendSupply_mem {T S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ verified (Deck.appendSupply T S) adj χ
      ↔ g ∈ verified T adj χ ∨ g ∈ verified S adj χ := by
  unfold Consume.verified
  constructor
  · intro h
    obtain ⟨hg, ha⟩ := List.mem_filter.mp h
    rcases Deck.mem_gens_appendSupply_iff.mp hg with h' | h'
    · exact Or.inl (List.mem_filter.mpr ⟨h', ha⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨h', ha⟩)
  · intro h
    rcases h with h | h <;> obtain ⟨hg, ha⟩ := List.mem_filter.mp h
    · exact List.mem_filter.mpr ⟨Deck.mem_gens_appendSupply_iff.mpr (Or.inl hg), ha⟩
    · exact List.mem_filter.mpr ⟨Deck.mem_gens_appendSupply_iff.mpr (Or.inr hg), ha⟩

/-- **★★ Orbit-equality is a congruence for supply concatenation** — any future supply swap
licensed by `SameOrbits` stays licensed inside a composite record. -/
theorem sameOrbits_appendSupply {T S₁ S₂ : Supply n}
    (h : OrbitPrune.SameOrbits S₁ S₂) :
    OrbitPrune.SameOrbits (Deck.appendSupply T S₁) (Deck.appendSupply T S₂) := by
  have half : ∀ (A B : Supply n),
      (∀ (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n),
        WordReach (verified A adj χ) u w → WordReach (verified B adj χ) u w) →
      ∀ (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n),
        WordReach (verified (Deck.appendSupply T A) adj χ) u w →
        WordReach (verified (Deck.appendSupply T B) adj χ) u w := by
    intro A B hAB adj χ u w
    refine wordReach_of_reaches (fun g hg => ?_)
    rcases verified_appendSupply_mem.mp hg with h' | h'
    · exact TreePrune.Reaches.gen (verified_appendSupply_mem.mpr (Or.inl h'))
    · intro x
      have hstep : WordReach (verified A adj χ) x (g x) :=
        (Consume.WordReach.refl x).step h'
      have h2 : WordReach (verified B adj χ) x (g x) := hAB adj χ x (g x) hstep
      exact wordReach_of_reaches
        (fun g' hg' => TreePrune.Reaches.gen (verified_appendSupply_mem.mpr (Or.inr hg'))) h2
  intro adj χ u w
  exact ⟨half S₁ S₂ (fun adj χ u w => (h adj χ u w).mp) adj χ u w,
    half S₂ S₁ (fun adj χ u w => (h adj χ u w).mpr) adj χ u w⟩

end Kernel
end ChainDescent
