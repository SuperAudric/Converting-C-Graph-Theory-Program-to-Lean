import ChainDescent.CopyProbe
import ChainDescent.RulerLemma

/-!
# The coherence chain — `Φ_E` is a function of the diagonal colour

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d.3 and §6e.4g **item 4a**.)

## What this closes

§6e.4g items 1–3 are theorems (`RulerLemma`, `CopyRestrict`, `CopyProbe`), and what stood between
them and (A) was the *instantiation*. This file does the first half of it — the two arrows the doc
writes as bookkeeping:

```
 col_E(p(c,i))  ==> {{ ( y(c',l), col_E(p(c,i), p(c',l)) ) : (c',l) }}      [payload filter]
                ==> {{ ( y(c',l), Align(a(c,i), a(c',l)) ) }} = Phi_E(c,i)  [frame filter]
```

**`phi_determined`** is that chain as one theorem: *two payload vertices with the same closure
diagonal colour have the same `RulerLemma.Phi`*, at the real object `Ensemble.eRoot`, at every `L`.
The observable the Ruler Lemma consumes is therefore genuinely available to 2-WL here — it is not an
idealisation.

## What it takes, and the one thing that was not bookkeeping

Both arrows are `CopyRestrict.sig_restrict` at a colour-definable sub-carrier (payload vertices;
frame vertices), so they cost almost nothing. Two supporting facts did have to be proved:

* **§1 `exists_factor'`** — *"the colour determines `d`"* upgraded to an actual function, at an
  arbitrary codomain. `PartitionClosure.exists_factor` only does `Nat`, and `Align` is a multiset.
* **§2 `Transposable`** — ⚠ **`eRoot` is not a symmetric function**: `eInit` records the two sorts in
  order, so `col(u,v)` and `col(v,u)` are different colours. What is true, and needed, is that each
  *determines* the other; that is `Transposable`, and it is preserved by the round. Without it the
  frame filter delivers `{{(col(u,z), col(z,v))}}` while `Align` wants `{{(col(u,z), col(v,z))}}`, and
  the chain does not close.

## ✅ What happened next (item 4b), and what is still missing for (A)

When this file landed, `RulerLemma.ruler`'s hypothesis (ii) *"`b ω₀` injective"* failed at the model —
`Ensemble.EColr` was then **all** slot colourings, so it carried directed copies and self-loop slots
that §3's construction does not have. **Both were fixed:** (ii) was weakened to *"`b ω₀` refines the
reading being decoded"* (`RulerLemma.ruler'`), and `EColr` became a **graph** (symmetric, irreflexive).
⟹ `RulerAtEnsemble.rulerRefines_of_discrete` **(R)** and `tagIsolates_of_discrete` **(i)** are now
theorems, and `readings_translate_of_wl2G_discrete` is (A) at the object given one discrete copy.

⛔ **Two inputs still stand between that and *"no mixed cell"*, and this file supplies neither:**
§6e.4g **4b3** (§6e.4a's *"`a` determines `c`"* — translate **readings** vs same-orbit **vertices**)
and **4c** (a refinement-discrete copy exists, which is also the headline theorem's non-vacuity).

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace Coherence

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.Ensemble
open ChainDescent.CopyRestrict
open ChainDescent.CopyProbe

/-! ## 1. Factoring through a colouring, at an arbitrary codomain -/

/-- `PartitionClosure.exists_factor` with the target allowed to be any nonempty type. *"`c`
determines `d`"* becomes an actual function `Nat → β`. -/
theorem exists_factor' {V β : Type*} [Nonempty β] {c : V → Nat} {d : V → β}
    (h : ∀ p q : V, c p = c q → d p = d q) : ∃ g : Nat → β, ∀ p, g (c p) = d p := by
  classical
  have hchoice : ∀ n : Nat, ∃ b : β, ∀ p : V, c p = n → d p = b := by
    intro n
    by_cases hn : ∃ p : V, c p = n
    · obtain ⟨p₀, hp₀⟩ := hn
      exact ⟨d p₀, fun p hp => h p p₀ (hp.trans hp₀.symm)⟩
    · exact ⟨Classical.arbitrary β, fun p hp => absurd ⟨p, hp⟩ hn⟩
  choose g hgspec using hchoice
  exact ⟨g, fun p => (hgspec (c p) p rfl).symm⟩

/-! ## 2. ⚠ The transpose — `col(u,v)` and `col(v,u)` are different colours that determine each other -/

section Transpose

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colouring determines its own transpose. -/
def Transposable (c : Col (V × V)) : Prop :=
  ∀ p q : V × V, c p = c q → c (p.2, p.1) = c (q.2, q.1)

omit [DecidableEq V] in
theorem pairSigG_transpose {c : Col (V × V)} {g : Nat → Nat}
    (hg : ∀ p : V × V, g (c p) = c (p.2, p.1)) (p : V × V) :
    pairSigG c (p.2, p.1) = (pairSigG c p).map (fun t => (g t.2, g t.1)) := by
  unfold pairSigG
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp only [Function.comp_apply]
  rw [hg (x, p.2), hg (p.1, x)]

theorem transposable_roundG {c : Col (V × V)} (h : Transposable c) :
    Transposable (roundG c) := by
  obtain ⟨g, hg⟩ := exists_factor (d := fun p : V × V => c (p.2, p.1)) h
  intro p q hpq
  obtain ⟨hc, hs⟩ := (roundG_eq_iff c p q).mp hpq
  refine (roundG_eq_iff c _ _).mpr ⟨h p q hc, ?_⟩
  rw [pairSigG_transpose hg p, pairSigG_transpose hg q, hs]

theorem transposable_iterate : ∀ (k : Nat) {c : Col (V × V)}, Transposable c →
    Transposable ((roundG (V := V))^[k] c)
  | 0, _, h => h
  | k + 1, c, h => by
      rw [Function.iterate_succ_apply']
      exact transposable_roundG (transposable_iterate k h)

/-- **★ The closure inherits it.** -/
theorem transposable_wl2G {c : Col (V × V)} (h : Transposable c) : Transposable (wl2G c) :=
  transposable_iterate _ h

end Transpose

variable {L : Nat}

/-- The ensemble's adjacency is symmetric. -/
theorem eAdj_comm (x y : EVert L) : eAdj x y = eAdj y x := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rcases y with ⟨c', j⟩ | ⟨k', t'⟩ | g' <;>
    simp only [eAdj, decide_eq_decide, ne_eq] <;>
    first
      | rfl
      | (constructor <;> (rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun hh => h2 hh.symm⟩))

theorem transposable_eInit : Transposable (eInit L) := by
  intro p q h
  simp only [eInit, Nat.pair_eq_pair] at h ⊢
  obtain ⟨⟨hs1, hs2⟩, hd, ha⟩ := h
  have hiff : (p.1 = p.2) ↔ (q.1 = q.2) := by
    constructor
    · intro hp; by_contra hq; rw [if_pos hp, if_neg hq] at hd; exact absurd hd (by decide)
    · intro hq; by_contra hp; rw [if_neg hp, if_pos hq] at hd; exact absurd hd (by decide)
  refine ⟨⟨hs2, hs1⟩, ?_, ?_⟩
  · by_cases hp : p.1 = p.2
    · rw [if_pos hp.symm, if_pos (hiff.mp hp).symm]
    · rw [if_neg (fun hh => hp hh.symm), if_neg (fun hh => hp (hiff.mpr hh.symm))]
  · rw [eAdj_comm p.2 p.1, eAdj_comm q.2 q.1]; exact ha

/-- **★ `eRoot` determines its own transpose.** -/
theorem eRoot_transposable : Transposable (eRoot L) :=
  transposable_wl2G transposable_eInit

/-! ## 3. The two filters -/

/-- The typed-slot index — the shared frame, which is the Ruler Lemma's slot set `X`. -/
abbrev SlotIdx (L : Nat) : Type := ESlot L × Bool

/-- The frame vertex of a typed slot. -/
abbrev efrmI (s : SlotIdx L) : EVert L := efrm s.1 s.2

/-- The payload index — the Ruler Lemma's `Ω`. -/
abbrev PayIdx (L : Nat) : Type := EColr L × Fin L

/-- The payload vertex of an index. -/
abbrev epayI (w : PayIdx L) : EVert L := epay w.1 w.2

theorem efrmI_injective : Function.Injective (efrmI (L := L)) := by
  rintro ⟨k, t⟩ ⟨k', t'⟩ h
  simpa [efrmI, efrm, Prod.mk.injEq] using h

theorem epayI_injective : Function.Injective (epayI (L := L)) := by
  rintro ⟨c, i⟩ ⟨c', j⟩ h
  simpa [epayI, epay, Prod.mk.injEq] using h

theorem esort_eq_zero_iff (z : EVert L) : esort z = 0 ↔ ∃ w : PayIdx L, epayI w = z := by
  rcases z with ⟨c, i⟩ | ⟨k, t⟩ | g
  · exact ⟨fun _ => ⟨(c, i), rfl⟩, fun _ => rfl⟩
  · simp [esort]
  · by_cases hg : g = ebase L <;> simp [esort, hg]

/-- ★ **The diagonal readout.** A pair colour determines its first endpoint's own diagonal colour:
the diagonal flag is atomic, so *"`z` is `u`"* is colour-definable and the filter is a singleton. -/
theorem diag_readout {u v u' v' : EVert L} (h : eRoot L (u, v) = eRoot L (u', v')) :
    eRoot L (u, u) = eRoot L (u', u') := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  set P : Nat → Bool := fun n => decide (dEq (g n) = 1) with hPdef
  have hP : ∀ (w : EVert L) (z : EVert L), (P (eRoot L (w, z)) = true) ↔ z = w := by
    intro w z
    have hval : P (eRoot L (w, z)) = decide ((if w = z then 1 else 0) = 1) := by
      rw [hPdef]; simp only [hg (w, z), dEq_eInit]
    rw [hval, decide_eq_true_iff]
    by_cases hh : w = z <;> simp [hh, eq_comm]
  have h1 := sig_singleton (eRoot L) P u v u (hP u)
  have h2 := sig_singleton (eRoot L) P u' v' u' (hP u')
  have hsig : Multiset.filter (fun t => P t.1 = true) (pairSigG (eRoot L) (u, v))
      = Multiset.filter (fun t => P t.1 = true) (pairSigG (eRoot L) (u', v')) :=
    congrArg _ (stable_iff_sig.mp eRoot_stable _ _ h)
  rw [h1, h2] at hsig
  exact congrArg Prod.fst (Multiset.singleton_inj.mp hsig)

/-- ★ **The frame filter.** A pair colour determines the multiset, over typed slots, of the two
half-colours against that slot's frame vertex — which is the `Align` of the two slot profiles, read
with the second one transposed. -/
theorem align_readout {u v u' v' : EVert L} (h : eRoot L (u, v) = eRoot L (u', v')) :
    (Finset.univ : Finset (SlotIdx L)).val.map
        (fun s => (eRoot L (u, efrmI s), eRoot L (efrmI s, v)))
      = (Finset.univ : Finset (SlotIdx L)).val.map
        (fun s => (eRoot L (u', efrmI s), eRoot L (efrmI s, v'))) := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  set P : Nat → Bool := fun n => decide (dSort2 (g n) = 1) with hPdef
  have hP : ∀ (w : EVert L) (z : EVert L),
      (P (eRoot L (w, z)) = true) ↔ ∃ s : SlotIdx L, efrmI s = z := by
    intro w z
    have hval : P (eRoot L (w, z)) = decide (esort z = 1) := by
      rw [hPdef]; simp only [hg (w, z), dSort2_eInit]
    rw [hval, decide_eq_true_iff]
    constructor
    · intro hs
      obtain ⟨k, t, rfl⟩ := (esort_eq_one_iff z).mp hs
      exact ⟨(k, t), rfl⟩
    · rintro ⟨⟨k, t⟩, rfl⟩; rfl
  exact restrict_sig_eq eRoot_stable P efrmI_injective efrmI_injective (hP u) (hP u') h

/-- ★ **The payload filter.** A diagonal colour determines the multiset, over *all* payload vertices
of the whole ensemble, of the two half-colours against them. -/
theorem payload_readout {u v u' v' : EVert L} (h : eRoot L (u, v) = eRoot L (u', v')) :
    (Finset.univ : Finset (PayIdx L)).val.map
        (fun w => (eRoot L (u, epayI w), eRoot L (epayI w, v)))
      = (Finset.univ : Finset (PayIdx L)).val.map
        (fun w => (eRoot L (u', epayI w), eRoot L (epayI w, v'))) := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  set P : Nat → Bool := fun n => decide (dSort2 (g n) = 0) with hPdef
  have hP : ∀ (w : EVert L) (z : EVert L),
      (P (eRoot L (w, z)) = true) ↔ ∃ x : PayIdx L, epayI x = z := by
    intro w z
    have hval : P (eRoot L (w, z)) = decide (esort z = 0) := by
      rw [hPdef]; simp only [hg (w, z), dSort2_eInit]
    rw [hval, decide_eq_true_iff]
    exact esort_eq_zero_iff z
  exact restrict_sig_eq eRoot_stable P epayI_injective epayI_injective (hP u) (hP u') h

/-! ## 4. ★★★ `Φ_E` is determined by the diagonal colour -/

/-- The **slot profile** of a vertex: how it reads each typed slot of the shared frame. This is the
Ruler Lemma's `b`. -/
def bE (L : Nat) (w : PayIdx L) : SlotIdx L → Nat := fun s => eRoot L (epayI w, efrmI s)

/-- The **tag**: the payload vertex's own diagonal colour. This is the Ruler Lemma's `y`. -/
def yE (L : Nat) (w : PayIdx L) : Nat := eRoot L (epayI w, epayI w)

/-- ### ★★★ THE COHERENCE CHAIN, §6e.4g item 4a.
Two payload vertices of the ensemble with the same closure **diagonal** colour have the same
`RulerLemma.Phi`. So the observable the Ruler Lemma consumes really is delivered by 2-WL at this
object — the doc's §6e.4d.3 arrows 1 and 2, discharged.

⚠ This says nothing about whether `Φ` in turn determines the orbit; that is `RulerLemma.ruler`, and
applying it needs item 4b's hypotheses at a model with unordered slots. -/
theorem phi_determined {w w' : PayIdx L} (h : yE L w = yE L w') :
    RulerLemma.Phi (bE L) (yE L) w = RulerLemma.Phi (bE L) (yE L) w' := by
  classical
  -- the three extracted functions
  obtain ⟨gT, hgT⟩ := exists_factor (d := fun p : EVert L × EVert L => eRoot L (p.2, p.1))
    eRoot_transposable
  obtain ⟨gD, hgD⟩ := exists_factor (c := fun p : EVert L × EVert L => eRoot L p)
    (d := fun p : EVert L × EVert L => eRoot L (p.1, p.1))
    (fun p q hpq => diag_readout (u := p.1) (v := p.2) (u' := q.1) (v' := q.2) hpq)
  obtain ⟨gA, hgA⟩ := exists_factor' (c := fun p : EVert L × EVert L => eRoot L p)
    (d := fun p : EVert L × EVert L => (Finset.univ : Finset (SlotIdx L)).val.map
      (fun s => (eRoot L (p.1, efrmI s), eRoot L (efrmI s, p.2))))
    (fun p q hpq => align_readout hpq)
  set F : Nat × Nat → Nat × Multiset (Nat × Nat) :=
    fun t => (gD t.2, Multiset.map (fun r => (r.1, gT r.2)) (gA t.1)) with hF
  have key : ∀ x : PayIdx L, RulerLemma.Phi (bE L) (yE L) x
      = Multiset.map F ((Finset.univ : Finset (PayIdx L)).val.map
          (fun z => (eRoot L (epayI x, epayI z), eRoot L (epayI z, epayI x)))) := by
    intro x
    have hphi : RulerLemma.Phi (bE L) (yE L) x
        = (Finset.univ : Finset (PayIdx L)).val.map
            (fun z => (yE L z, RulerLemma.Align (bE L x) (bE L z))) := rfl
    rw [hphi, Multiset.map_map]
    refine Multiset.map_congr rfl (fun z _ => ?_)
    simp only [Function.comp_apply, hF]
    refine Prod.ext ?_ ?_
    · exact (hgD (epayI z, epayI x)).symm
    · have halign : RulerLemma.Align (bE L x) (bE L z)
          = (Finset.univ : Finset (SlotIdx L)).val.map (fun s => (bE L x s, bE L z s)) := rfl
      rw [halign, hgA (epayI x, epayI z), Multiset.map_map]
      refine Multiset.map_congr rfl (fun s _ => ?_)
      simp only [Function.comp_apply]
      exact Prod.ext rfl (hgT (efrmI s, epayI z)).symm
  rw [key w, key w', payload_readout (u := epayI w) (v := epayI w) (u' := epayI w') (v' := epayI w') h]

end Coherence
end ChainDescent
