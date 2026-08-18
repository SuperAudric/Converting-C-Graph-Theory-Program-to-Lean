import ChainDescent.Coherence

/-!
# The Ruler Lemma **at the ensemble** — what is unconditional, and the two hypotheses that are left

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4g **item 4b**.)

## The state of (A), after this file

| | |
|---|---|
| the engine | ✅ `RulerLemma.ruler'` — a theorem |
| `(LB)`, `(P1)`, `(P2)` | ✅ `CopyRestrict.lb`, `CopyProbe.tag_isolates`, `CopyProbe.profile_injective` |
| `Φ_E` is 2-WL-available | ✅ `Coherence.phi_determined` |
| **the ensemble is an instance of the abstract setup** | ✅ **this file**: `bE_equivariant`, `yE_invariant` — unconditional, straight off `Ensemble.invG_eRoot` |
| ⛔ **(i) the tag isolates a ruler's orbit** | **hypothesis.** `CopyProbe.sameLabelOrbit_of_tag` discharges it *pairwise*, but only against copies that are `SymCopy` and `Proper` — and `Ensemble`'s copy set is **all** slot-colourings, so it is not discharged as stated |
| ⛔ **(R) the ruler's view refines every reading** | **hypothesis**, and it is new. `CopyProbe.transfer` gives it *within the ruler's own copy*; across copies it is open |

`readings_translate` is (A) reduced to exactly those two. ⚠⚠ Read it as a **reduction**, not as (A): it
is a conditional whose hypotheses are not known to hold at this object, and per §7's standing filter a
conditional on an unchecked hypothesis can be vacuous. What is *not* conditional is everything in the
rows above it.

## ★ Why this is progress even though (A) is still open

(B) is the claim that the cross-copy channel adds nothing. After this file, (B) has to deny **(R)** —
*"two frame vertices that the ruler's payload vertex cannot tell apart are told apart by some other
payload vertex"*. That is a concrete, finite, **measurable** statement about a small ensemble, not an
argument about washout. ⟹ the disagreement is now something `L = 4,5` can be pointed at.

## ⚠ The two things (A) still needs beyond (i) and (R)

1. **`Ensemble`'s copies are all slot-colourings**, including non-symmetric and non-proper ones; the
   doc's construction uses graphs, i.e. proper symmetric colourings. Cutting the model down is what
   would let `sameLabelOrbit_of_tag` discharge (i) uniformly.
2. **"the reading determines the copy"** (§6e.4a's *"`a` determines `c`"*, argued + measured, **not**
   proved). `readings_translate` concludes that two readings are `S_L`-translates; turning that into
   *"the two payload vertices are in one label orbit"* — which is what `Ensemble.MixedCell` is about —
   needs that step. ⛔ The doc lists it under *"pinned, inherited"*; it is a third open input, and the
   item list in §6e.4g did not name it.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace RulerAtEnsemble

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.Ensemble
open ChainDescent.CopyRestrict
open ChainDescent.CopyProbe
open ChainDescent.Coherence

variable {L : Nat}

/-! ## 1. The label group acts on the two index sets -/

instance : SMul (Equiv.Perm (Fin L)) (SlotIdx L) :=
  ⟨fun σ s => ((σ s.1.1, σ s.1.2), s.2)⟩

instance : MulAction (Equiv.Perm (Fin L)) (SlotIdx L) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : SMul (Equiv.Perm (Fin L)) (PayIdx L) := ⟨fun σ w => (cact σ w.1, σ w.2)⟩

instance : MulAction (Equiv.Perm (Fin L)) (PayIdx L) where
  one_smul _ := Prod.ext (Subtype.ext (funext fun _ => rfl)) rfl
  mul_smul _ _ _ := Prod.ext (Subtype.ext (funext fun _ => rfl)) rfl

/-- The slot action agrees with the ensemble's vertex action. -/
@[simp] theorem efrmI_smul (σ : Equiv.Perm (Fin L)) (s : SlotIdx L) :
    efrmI (σ • s) = eact σ (efrmI s) := rfl

/-- The payload action agrees with the ensemble's vertex action. -/
@[simp] theorem epayI_smul (σ : Equiv.Perm (Fin L)) (w : PayIdx L) :
    epayI (σ • w) = eact σ (epayI w) := rfl

/-! ## 2. ✅ The ensemble **is** an instance of the abstract setup -/

/-- ★ **The slot profiles are equivariant.** Straight off `Ensemble.invG_eRoot`. -/
theorem bE_equivariant : RulerLemma.Equivariant (Equiv.Perm (Fin L)) (bE L) := by
  intro σ w s
  show eRoot L (epayI (σ • w), efrmI s) = eRoot L (epayI w, efrmI (σ⁻¹ • s))
  rw [epayI_smul, ← invG_eRoot (L := L) σ (epayI w, efrmI (σ⁻¹ • s)), ← efrmI_smul, smul_inv_smul]

/-- ★ **The tag is invariant.** -/
theorem yE_invariant : RulerLemma.Invariant (Equiv.Perm (Fin L)) (yE L) := by
  intro σ w
  show eRoot L (epayI (σ • w), epayI (σ • w)) = eRoot L (epayI w, epayI w)
  rw [epayI_smul]
  exact invG_eRoot σ (epayI w, epayI w)

/-- The `Φ` of `Coherence` is literally `RulerLemma.Phi` at these data — recorded so the seam cannot
drift. ★ §7's standing filter: *check the two sides of a seam are the same object*. -/
theorem phi_seam (w : PayIdx L) :
    RulerLemma.Phi (bE L) (yE L) w
      = (Finset.univ : Finset (PayIdx L)).val.map
          (fun z => (yE L z, RulerLemma.Align (bE L w) (bE L z))) := rfl

/-! ## 3. ★★★ THE TWO FRAME SYMMETRIES A GRAPH COPY CANNOT SEE

Both are automorphisms of the ensemble **because a copy is a graph** — the first uses symmetry, the
second irreflexivity. They are what makes the ruler's fibres exactly the forced ones, i.e. `(R)`. -/

/-- The slot transposition. -/
def swapSlot (k : ESlot L) : ESlot L := (k.2, k.1)

theorem swapSlot_involutive : Function.Involutive (swapSlot (L := L)) := fun _ => rfl

@[simp] theorem swapSlot_swapSlot (k : ESlot L) : swapSlot (swapSlot k) = k := rfl

theorem inSlot_swapSlot (k : ESlot L) (i : Fin L) : inSlot (swapSlot k) i = inSlot k i := by
  simp only [inSlot, swapSlot, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun hh => h1 hh.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun hh => h1 hh.symm, h2.symm⟩

theorem colr_swapSlot (c : EColr L) (k : ESlot L) : c.val (swapSlot k) = c.val k :=
  EColr.symm c k.2 k.1

/-- The twin swap: exchange the two frame vertices of each unordered slot, fix everything else.
★ An automorphism **because every copy is symmetric**. -/
def tswapFun : EVert L → EVert L
  | Sum.inr (Sum.inl (k, t)) => Sum.inr (Sum.inl (swapSlot k, t))
  | x => x

theorem tswapFun_involutive : Function.Involutive (tswapFun (L := L)) := by
  rintro (⟨c, i⟩ | ⟨k, t⟩ | g) <;> rfl

def tswap : EVert L ≃ EVert L := Function.Involutive.toPerm _ (tswapFun_involutive (L := L))

@[simp] theorem tswap_apply (x : EVert L) : tswap x = tswapFun x := rfl

@[simp] theorem tswap_epay (c : EColr L) (i : Fin L) : tswap (epay c i) = epay c i := rfl

theorem esort_tswap (x : EVert L) : esort (tswap x) = esort x := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rfl

theorem eAdj_tswap (x y : EVert L) : eAdj (tswap x) (tswap y) = eAdj x y := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rcases y with ⟨c', j⟩ | ⟨k', t'⟩ | g' <;>
    simp only [tswap_apply, tswapFun, eAdj, inSlot_swapSlot, colr_swapSlot,
      swapSlot_involutive.injective.eq_iff]

theorem invG_tswap : InvG (tswap (L := L)) (eRoot L) :=
  invG_wl2G (by intro p; simp only [eInit, esort_tswap, eAdj_tswap, Equiv.apply_eq_iff_eq])

/-- ★★ **Nobody can see the twins.** -/
theorem twin_blind (c : EColr L) (i : Fin L) (k : ESlot L) (t : Bool) :
    eRoot L (epay c i, efrm k t) = eRoot L (epay c i, efrm (swapSlot k) t) :=
  (invG_tswap (L := L) (epay c i, efrm k t)).symm

/-- The degenerate-slot swap: exchange the frame vertices of the self-loop slots `(a,a)` and `(b,b)`.
★ An automorphism **because every copy is irreflexive** — no copy attaches to either, and every gauge
assigns both the same type. -/
def degSlot (a b : Fin L) (k : ESlot L) : ESlot L :=
  if k = (a, a) then (b, b) else if k = (b, b) then (a, a) else k

theorem degSlot_involutive (a b : Fin L) : Function.Involutive (degSlot a b) := by
  intro k
  by_cases h1 : k = (a, a)
  · by_cases hab : (b, b) = ((a, a) : ESlot L)
    · simp [degSlot, h1, hab]
    · simp [degSlot, h1, hab]
  · by_cases h2 : k = (b, b)
    · simp [degSlot, h1, h2]
    · simp [degSlot, h1, h2]

theorem degSlot_fix (a b : Fin L) (k : ESlot L) (hk : k.1 ≠ k.2) : degSlot a b k = k := by
  have h1 : k ≠ (a, a) := fun hh => hk (by rw [hh])
  have h2 : k ≠ (b, b) := fun hh => hk (by rw [hh])
  simp [degSlot, h1, h2]

theorem degSlot_deg (a b : Fin L) (k : ESlot L) (hk : k.1 = k.2) :
    (degSlot a b k).1 = (degSlot a b k).2 := by
  unfold degSlot
  split
  · rfl
  · split
    · rfl
    · exact hk

/-- A copy gives every self-loop slot type `false` — it is irreflexive. -/
theorem colr_diag (g : EColr L) (k : ESlot L) (hk : k.1 = k.2) : g.val k = false := by
  rw [show k = (k.1, k.1) from Prod.ext rfl hk.symm]
  exact EColr.irrefl g k.1

def degFun (a b : Fin L) : EVert L → EVert L
  | Sum.inr (Sum.inl (k, t)) => Sum.inr (Sum.inl (degSlot a b k, t))
  | x => x

theorem degFun_involutive (a b : Fin L) : Function.Involutive (degFun (L := L) a b) := by
  rintro (⟨c, i⟩ | ⟨k, t⟩ | g)
  · rfl
  · show Sum.inr (Sum.inl (degSlot a b (degSlot a b k), t)) = _
    rw [degSlot_involutive a b k]
  · rfl

def degSwap (a b : Fin L) : EVert L ≃ EVert L :=
  Function.Involutive.toPerm _ (degFun_involutive (L := L) a b)

@[simp] theorem degSwap_apply (a b : Fin L) (x : EVert L) : degSwap a b x = degFun a b x := rfl

@[simp] theorem degSwap_epay (a b : Fin L) (c : EColr L) (i : Fin L) :
    degSwap a b (epay c i) = epay c i := rfl

theorem esort_degSwap (a b : Fin L) (x : EVert L) : esort (degSwap a b x) = esort x := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rfl

/-- A degenerate slot carries no payload edge, and every copy gives it type `false`. -/
theorem inSlot_deg (x i : Fin L) : inSlot ((x, x) : ESlot L) i = false := by simp [inSlot]

theorem eAdj_degSwap (a b : Fin L) (x y : EVert L) :
    eAdj (degSwap a b x) (degSwap a b y) = eAdj x y := by
  have key : ∀ (c : EColr L) (i : Fin L) (k : ESlot L) (t : Bool),
      (inSlot (degSlot a b k) i && decide (c.val (degSlot a b k) = t))
        = (inSlot k i && decide (c.val k = t)) := by
    intro c i k t
    by_cases hk : k.1 = k.2
    · have hd : (degSlot a b k).1 = (degSlot a b k).2 := degSlot_deg a b k hk
      have h1 : inSlot (degSlot a b k) i = false := by
        simp only [inSlot, decide_eq_false_iff_not, not_and]; intro hne; exact absurd hd hne
      have h2 : inSlot k i = false := by
        simp only [inSlot, decide_eq_false_iff_not, not_and]; intro hne; exact absurd hk hne
      rw [h1, h2]; rfl
    · rw [degSlot_fix a b k hk]
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rcases y with ⟨c', j⟩ | ⟨k', t'⟩ | g'
  · rfl
  · exact key c i k' t'
  · rfl
  · exact key c' j k t
  · show decide (degSlot a b k = degSlot a b k' ∧ t ≠ t') = decide (k = k' ∧ t ≠ t')
    exact decide_eq_decide.2 (and_congr_left' (degSlot_involutive a b).injective.eq_iff)
  · show decide (g'.val (degSlot a b k) = t) = decide (g'.val k = t)
    by_cases hk : k.1 = k.2
    · rw [colr_diag g' (degSlot a b k) (degSlot_deg a b k hk), colr_diag g' k hk]
    · rw [degSlot_fix a b k hk]
  · rfl
  · show decide (g.val (degSlot a b k') = t') = decide (g.val k' = t')
    by_cases hk : k'.1 = k'.2
    · rw [colr_diag g (degSlot a b k') (degSlot_deg a b k' hk), colr_diag g k' hk]
    · rw [degSlot_fix a b k' hk]
  · rfl

theorem invG_degSwap (a b : Fin L) : InvG (degSwap (L := L) a b) (eRoot L) :=
  invG_wl2G (by intro p; simp only [eInit, esort_degSwap, eAdj_degSwap, Equiv.apply_eq_iff_eq])

/-- ★★ **Nobody can see which self-loop slot is which.** -/
theorem deg_blind (c : EColr L) (i : Fin L) (a b : Fin L) (t : Bool) :
    eRoot L (epay c i, efrm (a, a) t) = eRoot L (epay c i, efrm (b, b) t) := by
  have h := (invG_degSwap (L := L) a b (epay c i, efrm (a, a) t)).symm
  simpa only [degSwap_apply, degSwap_epay, degFun, degSlot, if_pos rfl] using h


/-! ## 4. ★★★ (A) AT THE OBJECT — both hypotheses discharged

With a copy being a graph, the two frame symmetries of §3 are exactly the fibres a ruler is *allowed*
to have, so `(R)` becomes a theorem; and `CopyProbe.sameLabelOrbit_of_tag` now applies to every copy,
so `(i)` does too. ⟹ `readings_translate` fires with **no hypothesis but discreteness of one copy**. -/

/-- **(R)** — *the ruler's view is at least as fine as every reading*. -/
def RulerRefines (L : Nat) (w₀ : PayIdx L) : Prop :=
  ∀ (w : PayIdx L) (s s' : SlotIdx L), bE L w₀ s = bE L w₀ s' → bE L w s = bE L w s'

/-- **(i)** — *the tag names the ruler's orbit*. -/
def TagIsolates (L : Nat) (w₀ : PayIdx L) : Prop :=
  ∀ w : PayIdx L, yE L w = yE L w₀ → ∃ σ : Equiv.Perm (Fin L), w = σ • w₀

/-- (A) as a reduction to the two hypotheses — both are discharged below. -/
theorem readings_translate {w₀ : PayIdx L} (hiso : TagIsolates L w₀)
    {w₁ w₂ : PayIdx L} (href : RulerRefines L w₀) (h : yE L w₁ = yE L w₂) :
    ∃ σ : Equiv.Perm (Fin L), ∀ s, bE L w₂ s = bE L w₁ (σ • s) :=
  RulerLemma.ruler' (y := yE L) bE_equivariant w₀ hiso (href w₂) (phi_determined h)

/-- ### ★★★ (R) IS A THEOREM.
A refinement-discrete copy's payload vertex sees everything about the frame that any payload vertex
sees. Its fibres are exactly the two forced ones — twin slots (§3, from **symmetry** of a copy) and
self-loop slots (§3, from **irreflexivity**) — and every payload vertex has those same fibres. -/
theorem rulerRefines_of_discrete {c : EColr L} (hd : Function.Injective (eCopy L c)) (i : Fin L) :
    RulerRefines L ((c, i) : PayIdx L) := by
  rintro w ⟨k, t⟩ ⟨k', t'⟩ h
  have ht : t = t' := frame_type_eq' h
  subst ht
  show eRoot L (epayI w, efrm k t) = eRoot L (epayI w, efrm k' t)
  by_cases hk : k.1 = k.2
  · -- both slots are self-loops: nobody can tell them apart
    have hk' : k'.1 = k'.2 := by
      by_contra hk'
      rcases (profile_injective hd hk' h.symm).2 with hh | hh
      · exact hk' (by rw [hh]; exact hk)
      · exact hk' (by rw [hh]; exact hk.symm)
    rw [show k = (k.1, k.1) from Prod.ext rfl hk.symm,
        show k' = (k'.1, k'.1) from Prod.ext rfl hk'.symm]
    exact deg_blind w.1 w.2 k.1 k'.1 t
  · -- otherwise the ruler pins the unordered slot, and the twins are invisible to everyone
    rcases (profile_injective hd hk h).2 with rfl | hkk
    · rfl
    · rw [show k = swapSlot k' from hkk]
      exact (twin_blind w.1 w.2 k' t).symm

/-- ### ★★★ (i) IS A THEOREM. -/
theorem tagIsolates_of_discrete {c : EColr L} (hd : Function.Injective (eCopy L c)) (i : Fin L) :
    TagIsolates L ((c, i) : PayIdx L) := by
  intro w hw
  obtain ⟨σ, hσ⟩ :=
    sameLabelOrbit_of_tag (symCopy_all w.1) (proper_all c) (proper_all w.1) hd hw.symm
  exact ⟨σ, (epayI_injective (by rw [epayI_smul]; exact hσ)).symm⟩

/-- ### ★★★★ (A), AT THE REAL OBJECT.
**If one copy of the ensemble is refinement-discrete, then any two payload vertices sharing a 2-WL
colour read the shared frame the same way up to a relabelling of the labels.**

⚠⚠ Two inputs remain between this and *"no mixed cell"* (§6e.4g items 4b3, 4c), and neither is
supplied here: **(4b3)** §6e.4a's *"the reading determines the copy"* — this gives translate
**readings**, `Ensemble.MixedCell` is about **vertices**; and **(4c)** that a refinement-discrete copy
exists in `E(L)`, which is a Babai–Erdős–Selkow statement about the payload family, measured
(5760/32768 at `L = 6`) and not formalized. ⛔ Do not quote this as *"Construction C is dead"*. -/
theorem readings_translate_of_discrete {c : EColr L} (hd : Function.Injective (eCopy L c))
    (i : Fin L) {w₁ w₂ : PayIdx L} (h : yE L w₁ = yE L w₂) :
    ∃ σ : Equiv.Perm (Fin L), ∀ s, bE L w₂ s = bE L w₁ (σ • s) :=
  readings_translate (tagIsolates_of_discrete hd i) (rulerRefines_of_discrete hd i) h

/-- ▶ The same statement from the *copy-side* hypothesis the caller can actually check: the copy's own
2-WL closure is discrete. `(LB)` converts it. -/
theorem readings_translate_of_wl2G_discrete {c : EColr L}
    (hdisc : ∀ p q : Fin L × Fin L, wl2G (hInit c) p = wl2G (hInit c) q → p = q) (i : Fin L)
    {w₁ w₂ : PayIdx L} (h : yE L w₁ = yE L w₂) :
    ∃ σ : Equiv.Perm (Fin L), ∀ s, bE L w₂ s = bE L w₁ (σ • s) :=
  readings_translate_of_discrete (eCopy_injective_of_discrete c (symCopy_all c) hdisc) i h

end RulerAtEnsemble
end ChainDescent
