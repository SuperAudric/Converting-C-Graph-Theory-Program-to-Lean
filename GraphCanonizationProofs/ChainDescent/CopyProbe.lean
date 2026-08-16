import ChainDescent.CopyRestrict

/-!
# (P1) and (P2) — a refinement-discrete copy is a **ruler**

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d.1 and §6e.4g **item 3**.)

## What this file is for

`RulerLemma.ruler` (§6e.4g item 1) needs exactly two things of one chosen member `ω₀`:

* **(i)** its tag isolates its orbit, and
* **(ii)** its reading of the shared slots is injective.

At the ensemble those are the doc's `(P1)` and `(P2)`, and the doc derives both from `(LB)` —
machine-checked in `CopyRestrict.lb` — applied to a copy whose *own* refinement is discrete. This file
carries out that derivation, so all three of §6e.4g's (A)-side items are now theorems.

| | |
|---|---|
| **§1** | ★★★ `transfer` — a discrete copy is a **coordinate system**: if a pair colour at one payload vertex of the copy agrees for two outside vertices, it agrees at *every* payload vertex of the copy. This is the mechanism, and everything else is an application |
| **§2** | **(P2)** `profile_injective` — the slot profile of a payload vertex of a discrete copy separates typed slots |
| **§3** | **(P1)** `tag_isolates` — the diagonal colour of a payload vertex of a discrete copy determines the whole marked copy, up to a relabelling that matches the mark |

## ⚠⚠ What this does and does **not** settle

It discharges the last of the three (A)-side items in §6e.4g. It does **not** by itself prove (A):
the doc's §6e.4d.3 chain also needs the coherence steps (*"the pair colour pins the fibre, so the
`Align` channel is available"*), which are bookkeeping at the level of `Φ` and are **not** in Lean.
⛔ And nothing here says a discrete copy **exists** in a given `E(L)` — that is the counting statement
of §6e.4d.2 (measured: 5760/32768 at `L = 6`), which is a Babai–Erdős–Selkow fact about the payload
family and is not formalized. Both hypotheses are carried in the open, as `hd` and as the caller's
choice of `c`.

⚠ **Discreteness is a hypothesis, never an assumption about the ensemble.** `hd :
Function.Injective (eCopy L c)` is *implied* by (LB) plus discreteness of the copy's own 2-WL
(`CopyRestrict.eCopy_injective_of_discrete`), which is a property of one `L`-vertex graph — computable,
and true of almost all of them. That is what keeps the argument non-circular: the ensemble is never
assumed to separate the copies the disjunction is about.

## ⚠ Modelling note inherited from `Ensemble`

Slots are **ordered**, so `f(k,t)` and `f(swap k, t)` are twins and no invariant can separate them.
(P2) therefore concludes *"same type and same unordered slot"*, which is the faithful statement; (P1)
needs `SymCopy` on the copy being compared against, for the same reason.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace CopyProbe

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.Ensemble
open ChainDescent.CopyRestrict

/-! ## 0. The mirrored singleton filter, and the mirrored type readout -/

section Mirror

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem fmc {α β : Type*} (f : α → β) (P : β → Prop) [DecidablePred P] (m : Multiset α) :
    Multiset.filter P (m.map f) = (m.filter (fun a => P (f a))).map f := by
  refine Multiset.induction_on m (by simp) (fun a m ih => ?_)
  by_cases h : P (f a) <;> simp [h, ih]

/-- `CopyRestrict.sig_singleton`, filtering on the **second** half-colour. -/
theorem sig_singleton_snd (s : Col (V × V)) (P : Nat → Bool) (u v : V) (z₀ : V)
    (hP : ∀ z : V, (P (s (z, v)) = true) ↔ z = z₀) :
    Multiset.filter (fun t => P t.2 = true) (pairSigG s (u, v)) = {(s (u, z₀), s (z₀, v))} := by
  have h1 : Multiset.filter (fun t => P t.2 = true) (pairSigG s (u, v))
      = (((Finset.univ : Finset V).filter (fun z => P (s (z, v)) = true)).val).map
          (fun z => (s (u, z), s (z, v))) := by
    rw [pairSigG, fmc, Finset.filter_val]
  have hset : (Finset.univ : Finset V).filter (fun z => P (s (z, v)) = true) = {z₀} := by
    ext z; simpa using hP z
  rw [h1, hset]
  rfl

end Mirror

variable {L : Nat}

/-- first sort, from an `eInit` value -/
def dSort1 (n : Nat) : Nat := (Nat.unpair (Nat.unpair n).1).1

@[simp] theorem dSort1_eInit (p : EVert L × EVert L) : dSort1 (eInit L p) = esort p.1 := by
  simp [dSort1, eInit]

/-- `CopyRestrict.frame_type_eq` with the frame vertex on the right. -/
theorem frame_type_eq' {u u' : EVert L} {k k' : ESlot L} {t t' : Bool}
    (h : eRoot L (u, efrm k t) = eRoot L (u', efrm k' t')) : t = t' := by
  have h1 := (centre_readout h).2
  have h2 := eAdj_eq_of_eRoot_eq h1
  simp only [eAdj, ebase] at h2
  cases t <;> cases t' <;> simp_all

/-- ★ **The frame partner is colour-definable.** `f(k,¬t)` is the only frame vertex adjacent to
`f(k,t)`, so a pair colour at `f(k,t)` carries one at `f(k,¬t)`. This is what lets (P2) reach the
corners whose type the copy does **not** carry. -/
theorem frame_partner {u u' : EVert L} {k k' : ESlot L} {t t' : Bool}
    (h : eRoot L (u, efrm k t) = eRoot L (u', efrm k' t')) :
    eRoot L (u, efrm k (!t)) = eRoot L (u', efrm k' (!t')) := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  set P : Nat → Bool := fun n => decide (dSort1 (g n) = 1 ∧ dAdj (g n) = 1) with hPdef
  have hP : ∀ (kk : ESlot L) (tt : Bool) (z : EVert L),
      (P (eRoot L (z, efrm kk tt)) = true) ↔ z = efrm kk (!tt) := by
    intro kk tt z
    have hval : P (eRoot L (z, efrm kk tt))
        = decide (esort z = 1 ∧ (if eAdj z (efrm kk tt) then 1 else 0) = 1) := by
      rw [hPdef]; simp only [hg (z, efrm kk tt), dSort1_eInit, dAdj_eInit]
    rw [hval, decide_eq_true_iff]
    constructor
    · rintro ⟨hs, ha⟩
      obtain ⟨k₂, t₂, rfl⟩ := (esort_eq_one_iff z).mp hs
      have ha' : eAdj (efrm k₂ t₂) (efrm kk tt) = true := by
        by_cases hb : eAdj (efrm k₂ t₂) (efrm kk tt) = true
        · exact hb
        · rw [Bool.eq_false_iff.mpr hb] at ha; simp at ha
      simp only [eAdj, decide_eq_true_iff] at ha'
      obtain ⟨rfl, hne⟩ := ha'
      cases t₂ <;> cases tt <;> simp_all
    · rintro rfl
      refine ⟨rfl, ?_⟩
      have : eAdj (efrm kk (!tt)) (efrm kk tt) = true := by
        cases tt <;> simp [eAdj]
      simp [this]
  have h1 := sig_singleton_snd (eRoot L) P u (efrm k t) (efrm k (!t)) (hP k t)
  have h2 := sig_singleton_snd (eRoot L) P u' (efrm k' t') (efrm k' (!t')) (hP k' t')
  have hsig : Multiset.filter (fun t => P t.2 = true) (pairSigG (eRoot L) (u, efrm k t))
      = Multiset.filter (fun t => P t.2 = true) (pairSigG (eRoot L) (u', efrm k' t')) :=
    congrArg _ (stable_iff_sig.mp eRoot_stable _ _ h)
  rw [h1, h2] at hsig
  exact congrArg Prod.fst (Multiset.singleton_inj.mp hsig)

/-! ## 1. ★★★ The transfer — a discrete copy is a coordinate system -/

/-- ### ★★★ THE MECHANISM.
If the ensemble's restriction to the copy `c` is **injective**, then a pair colour taken at *one*
payload vertex of `c` already fixes the pair colour at *every* payload vertex of `c`.

★ This is the ruler in operation at the real object: the copy's own colours are pairwise distinct, so
they *name* its vertices, and the WL sum against that naming is a function rather than a multiset.
⚠ It uses only `(LB)`-grade input — `eCopy_stable` (stability restricts, from the atoms) plus the
hypothesis `hd`. -/
theorem transfer {c : EColr L} (hd : Function.Injective (eCopy L c)) {i : Fin L} {z z' : EVert L}
    (h : eRoot L (epay c i, z) = eRoot L (epay c i, z')) (y : Fin L) :
    eRoot L (epay c y, z) = eRoot L (epay c y, z') := by
  obtain ⟨P, hP⟩ := exists_copy_pred L
  have hs := restrict_sig_eq eRoot_stable P (epay_injective c) (epay_injective c)
    (u := epay c i) (v := z) (u' := epay c i) (v' := z') (hP c i) (hP c i) h
  have hmem : (eRoot L (epay c i, epay c y), eRoot L (epay c y, z))
      ∈ (Finset.univ : Finset (Fin L)).val.map
          (fun w => (eRoot L (epay c i, epay c w), eRoot L (epay c w, z))) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ y)
  rw [hs] at hmem
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hmem
  have hwy : w = y := congrArg Prod.snd (@hd (i, w) (i, y) (congrArg Prod.fst hw))
  subst hwy
  exact (congrArg Prod.snd hw).symm

/-! ## 2. (P2) — the slot profile of a discrete copy is injective -/

/-- The case where the copy carries the corner's type on both sides. -/
theorem slot_eq_of_own {c : EColr L} (hd : Function.Injective (eCopy L c)) {i : Fin L}
    {k k' : ESlot L} {t : Bool} (hk : k.1 ≠ k.2) (hk' : k'.1 ≠ k'.2) (hck : c k = t)
    (h : eRoot L (epay c i, efrm k t) = eRoot L (epay c i, efrm k' t)) :
    k = k' ∨ k = (k'.2, k'.1) := by
  have hadj : ∀ y : Fin L, eAdj (epay c y) (efrm k t) = eAdj (epay c y) (efrm k' t) := fun y =>
    eAdj_eq_of_eRoot_eq (p := (epay c y, efrm k t)) (q := (epay c y, efrm k' t)) (transfer hd h y)
  have hkc' : c k' = t := by
    have hone : eAdj (epay c k.1) (efrm k t) = true := by simp [eAdj, inSlot, hk, hck]
    have h2 : eAdj (epay c k.1) (efrm k' t) = true := by rw [← hadj k.1]; exact hone
    simp only [eAdj, Bool.and_eq_true, decide_eq_true_iff] at h2
    exact h2.2
  have hins : ∀ y : Fin L, inSlot k y = inSlot k' y := by
    intro y
    have := hadj y
    simpa [eAdj, hck, hkc'] using this
  have m1 : k.1 = k'.1 ∨ k.1 = k'.2 := by
    have h1 : inSlot k' k.1 = true := by rw [← hins k.1]; simp [inSlot, hk]
    simpa [inSlot, hk'] using h1
  have m2 : k.2 = k'.1 ∨ k.2 = k'.2 := by
    have h1 : inSlot k' k.2 = true := by rw [← hins k.2]; simp [inSlot, hk]
    simpa [inSlot, hk'] using h1
  rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2
  · exact absurd (m1.trans m2.symm) hk
  · exact Or.inl (Prod.ext m1 m2)
  · exact Or.inr (Prod.ext m1 m2)
  · exact absurd (m1.trans m2.symm) hk

/-- ### ★★ (P2), §6e.4g item 3, half one.
The **slot profile** of a payload vertex of a discrete copy separates typed slots: two typed slots
with the same profile entry carry the same type and the same *unordered* slot.

⚠ *Unordered* is forced by the model, not a weakness of the argument — `f(k,t)` and `f(swap k, t)`
are genuine twins of the ensemble (`Ensemble`'s note 1) and no invariant can tell them apart. -/
theorem profile_injective {c : EColr L} (hd : Function.Injective (eCopy L c)) {i : Fin L}
    {k k' : ESlot L} {t t' : Bool} (hk : k.1 ≠ k.2) (hk' : k'.1 ≠ k'.2)
    (h : eRoot L (epay c i, efrm k t) = eRoot L (epay c i, efrm k' t')) :
    t = t' ∧ (k = k' ∨ k = (k'.2, k'.1)) := by
  have ht : t = t' := frame_type_eq' h
  subst ht
  refine ⟨rfl, ?_⟩
  by_cases hck : c k = t
  · exact slot_eq_of_own hd hk hk' hck h
  · -- the copy does not carry this corner's type; go through the frame partner
    have hck' : c k = !t := by cases hb : c k <;> cases t <;> simp_all
    exact slot_eq_of_own hd hk hk' hck' (frame_partner h)

/-! ## 3. (P1) — a discrete copy is named by its colour -/

/-- ### ★★★ (P1), §6e.4g item 3, half two.
The diagonal colour of a payload vertex of a **discrete** copy determines the entire marked copy: any
payload vertex sharing that colour sits in a copy isomorphic to it, by a relabelling carrying the mark
to the mark.

★ This is the Ruler Lemma's hypothesis (i) at the object — *"nothing outside `ω₀`'s orbit carries
`ω₀`'s tag"* — and the proof is the classical *individualize-and-refine* argument, run on the
coordinate system §1 supplies. ⚠ It assumes discreteness of **one** copy only; the copy on the right
is arbitrary. -/
theorem tag_isolates {c c' : EColr L} (hsym' : SymCopy c')
    (hd : Function.Injective (eCopy L c)) {i i' : Fin L}
    (h : eRoot L (epay c i, epay c i) = eRoot L (epay c' i', epay c' i')) :
    ∃ π : Equiv.Perm (Fin L), π i = i' ∧ ∀ a b : Fin L, a ≠ b → c (a, b) = c' (π a, π b) := by
  obtain ⟨P, hP⟩ := exists_copy_pred L
  have hs := restrict_sig_eq eRoot_stable P (epay_injective c) (epay_injective c')
    (u := epay c i) (v := epay c i) (u' := epay c' i') (v' := epay c' i') (hP c i) (hP c' i') h
  have hex : ∀ y : Fin L, ∃ y' : Fin L,
      eRoot L (epay c' i', epay c' y') = eRoot L (epay c i, epay c y) := by
    intro y
    have hmem : (eRoot L (epay c i, epay c y), eRoot L (epay c y, epay c i))
        ∈ (Finset.univ : Finset (Fin L)).val.map
            (fun w => (eRoot L (epay c i, epay c w), eRoot L (epay c w, epay c i))) :=
      Multiset.mem_map_of_mem _ (Finset.mem_univ y)
    rw [hs] at hmem
    obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hmem
    exact ⟨w, congrArg Prod.fst hw⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro a b hab
    have hc : eRoot L (epay c i, epay c a) = eRoot L (epay c i, epay c b) := by
      rw [← hf a, ← hf b, hab]
    exact congrArg Prod.snd (@hd (i, a) (i, b) hc)
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.1 hfinj
  -- the mark goes to the mark
  have hii : f i = i' := by
    have h2 := diag_eq_of_eRoot_eq
      (p := (epay c' i', epay c' (f i))) (q := (epay c i, epay c i)) (hf i)
    exact (congrArg Prod.snd (Sum.inl.inj (h2.mpr rfl))).symm
  -- the right-hand copy's colours against `i'` are injective too, because `f` is onto
  have hd' : ∀ a b : Fin L,
      eRoot L (epay c' i', epay c' a) = eRoot L (epay c' i', epay c' b) → a = b := by
    intro a b hab
    obtain ⟨y₁, rfl⟩ := hfbij.2 a
    obtain ⟨y₂, rfl⟩ := hfbij.2 b
    rw [hf y₁, hf y₂] at hab
    exact congrArg f (congrArg Prod.snd (@hd (i, y₁) (i, y₂) hab))
  -- the correspondence extends from `i`'s row to every pair
  have hpair : ∀ x y : Fin L,
      eRoot L (epay c x, epay c y) = eRoot L (epay c' (f x), epay c' (f y)) := by
    intro x y
    have hs2 := restrict_sig_eq eRoot_stable P (epay_injective c) (epay_injective c')
      (u := epay c i) (v := epay c y) (u' := epay c' i') (v' := epay c' (f y))
      (hP c i) (hP c' i') (hf y).symm
    have hmem : (eRoot L (epay c i, epay c x), eRoot L (epay c x, epay c y))
        ∈ (Finset.univ : Finset (Fin L)).val.map
            (fun w => (eRoot L (epay c i, epay c w), eRoot L (epay c w, epay c y))) :=
      Multiset.mem_map_of_mem _ (Finset.mem_univ x)
    rw [hs2] at hmem
    obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hmem
    have hwfx : w = f x := hd' w (f x) ((congrArg Prod.fst hw).trans (hf x).symm)
    subst hwfx
    exact (congrArg Prod.snd hw).symm
  refine ⟨Equiv.ofBijective f hfbij, hii, fun a b hab => ?_⟩
  exact encoded_edge_eq hsym' hab (fun hh => hab (hfinj hh)) (hpair a b)

/-! ## 4. ▶ The corollary at `Ensemble.MixedCell`

(P1) says *"same colour ⟹ isomorphic marked copies"*. Turning that into *"same label orbit"* costs one
bookkeeping step: the relabelling `π` it produces has to **be** the ensemble's label action on the
copy, which it is once degenerate slots are pinned. -/

/-- A copy assigns `false` to the degenerate slots `(a,a)`. They carry no payload edge (`inSlot`
requires two distinct labels), so this is a normalisation, not a restriction on the construction —
but it is needed, because the label action moves `(a,a)` to `(πa,πa)` and the encoded-edge readout
says nothing there. -/
def Proper (c : EColr L) : Prop := ∀ a : Fin L, c (a, a) = false

theorem sact_symm (σ : Equiv.Perm (Fin L)) (k : ESlot L) :
    (sact σ).symm k = (σ.symm k.1, σ.symm k.2) := rfl

theorem cact_eq_of_relabel {c c' : EColr L} (hpc : Proper c) (hpc' : Proper c')
    {π : Equiv.Perm (Fin L)} (hπ : ∀ a b : Fin L, a ≠ b → c (a, b) = c' (π a, π b)) :
    cact π c = c' := by
  funext k
  obtain ⟨a, b⟩ := k
  rw [cact_apply, sact_symm]
  by_cases hab : a = b
  · subst hab
    rw [hpc (π.symm a), hpc' a]
  · have hne : π.symm a ≠ π.symm b := fun hh => hab (by simpa using congrArg π hh)
    simpa using hπ (π.symm a) (π.symm b) hne

/-- ### ⛔★ **NO MIXED CELL CAN TOUCH A REFINEMENT-DISCRETE COPY.**
If the copy `c` is proper and its ensemble restriction is injective, then *any* payload vertex sharing
`p(c,i)`'s closure colour is in `p(c,i)`'s **label orbit**. So `Ensemble.MixedCell` — the refutation
shape Construction C needs — can never be witnessed with a discrete copy on the left.

⚠⚠ **This is not (A).** (A) claims the same conclusion for the *non*-discrete copies, which are the
CFI-like ones the whole disjunction is about, and getting there is exactly what
`RulerLemma.ruler`'s `Align` channel is for — plus the coherence chain of §6e.4d.3, which is **not**
formalized. What is now machine-checked is that the ruler *itself* is isolated, at the real object,
at every `L`. ⛔ Do not quote this as *"Construction C is dead"*. -/
theorem sameLabelOrbit_of_tag {c c' : EColr L} (hsym' : SymCopy c')
    (hpc : Proper c) (hpc' : Proper c') (hd : Function.Injective (eCopy L c)) {i i' : Fin L}
    (h : eRoot L (epay c i, epay c i) = eRoot L (epay c' i', epay c' i')) :
    SameLabelOrbit (epay c i) (epay c' i') := by
  obtain ⟨π, hπi, hπ⟩ := tag_isolates hsym' hd h
  exact ⟨π, by rw [eact_pay, cact_eq_of_relabel hpc hpc' hπ, hπi]⟩

end CopyProbe
end ChainDescent
