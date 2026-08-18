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

/-! ## 1. The label group acts on the two index sets

⚠ Written out componentwise rather than through `sact`/`cact` so that both `MulAction` laws and the
compatibility with `Ensemble.eact` close by `rfl` — the project's standing trap about building actions
from `Equiv` combinators is about the *inverse* laws, which is exactly what is free here. -/

instance : SMul (Equiv.Perm (Fin L)) (SlotIdx L) :=
  ⟨fun σ s => ((σ s.1.1, σ s.1.2), s.2)⟩

instance : MulAction (Equiv.Perm (Fin L)) (SlotIdx L) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : SMul (Equiv.Perm (Fin L)) (PayIdx L) :=
  ⟨fun σ w => (fun k => w.1 (σ.symm k.1, σ.symm k.2), σ w.2)⟩

instance : MulAction (Equiv.Perm (Fin L)) (PayIdx L) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The slot action agrees with the ensemble's vertex action. -/
@[simp] theorem efrmI_smul (σ : Equiv.Perm (Fin L)) (s : SlotIdx L) :
    efrmI (σ • s) = eact σ (efrmI s) := rfl

/-- The payload action agrees with the ensemble's vertex action. -/
@[simp] theorem epayI_smul (σ : Equiv.Perm (Fin L)) (w : PayIdx L) :
    epayI (σ • w) = eact σ (epayI w) := rfl

/-! ## 2. ✅ The ensemble **is** an instance of the abstract setup — unconditionally -/

/-- ★ **The slot profiles are equivariant.** Straight off `Ensemble.invG_eRoot`: the closure inherits
every symmetry of the atoms, and the label action is one. -/
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

/-! ## 3. ▶ (A), reduced to two named hypotheses -/

/-- **(R)** — *the ruler's view is at least as fine as every reading*. Two frame vertices that `w₀`'s
payload vertex cannot separate are separated by **no** payload vertex.

★ `CopyProbe.transfer` proves this for `w` inside `w₀`'s own copy, from `(LB)` alone. Across copies it
is exactly what (B) must deny, and it is **finite and measurable** at small `L`. -/
def RulerRefines (L : Nat) (w₀ : PayIdx L) : Prop :=
  ∀ (w : PayIdx L) (s s' : SlotIdx L), bE L w₀ s = bE L w₀ s' → bE L w s = bE L w s'

/-- **(i)** — *the tag names the ruler's orbit*. `CopyProbe.sameLabelOrbit_of_tag` gives this against
any `SymCopy`+`Proper` copy; ⛔ `Ensemble`'s copy set is larger than that, so it is not discharged. -/
def TagIsolates (L : Nat) (w₀ : PayIdx L) : Prop :=
  ∀ w : PayIdx L, yE L w = yE L w₀ → ∃ σ : Equiv.Perm (Fin L), w = σ • w₀

/-- ### ▶▶ (A), AS A REDUCTION.
If the ensemble contains a **ruler** — a payload vertex whose tag names its orbit and whose view of the
frame is at least as fine as every other payload vertex's — then any two payload vertices sharing a
closure colour have `S_L`-translate readings of the frame.

⚠⚠ **This is not (A)**, on two counts, both flagged in the header: the hypotheses are not known to hold
at this model, and *"translate readings"* becomes *"same label orbit"* only via §6e.4a's unproved
*"the reading determines the copy"*. It is (A) with every remaining obligation named and finite. -/
theorem readings_translate {w₀ : PayIdx L} (hiso : TagIsolates L w₀)
    {w₁ w₂ : PayIdx L} (href : RulerRefines L w₀)
    (h : yE L w₁ = yE L w₂) :
    ∃ σ : Equiv.Perm (Fin L), ∀ s, bE L w₂ s = bE L w₁ (σ • s) :=
  RulerLemma.ruler' bE_equivariant w₀ hiso (href w₂) (phi_determined h)

/-- ▶ The half of `(R)` that is already a theorem: within the ruler's **own** copy it follows from
`(LB)`, with no extra hypothesis beyond the copy being refinement-discrete. ★ So `(R)`'s content is
entirely *cross-copy* — which is precisely the channel the whole disjunction is about. -/
theorem rulerRefines_within {c : EColr L} (hd : Function.Injective (eCopy L c)) (i : Fin L)
    (y : Fin L) (s s' : SlotIdx L)
    (h : bE L ((c, i) : PayIdx L) s = bE L ((c, i) : PayIdx L) s') :
    bE L ((c, y) : PayIdx L) s = bE L ((c, y) : PayIdx L) s' :=
  transfer hd h y

/-! ## 4. ⛔⛔ AND NOW THE BAD NEWS — `(R)` IS **UNATTAINABLE IN THIS MODEL**, and why

The slot-transposition `(i,j) ↦ (j,i)` is an **automorphism** of `Ensemble`: it swaps each pair of
twin frame vertices and reindexes every copy by the same transposition. Consequently

* a payload vertex of a **symmetric** copy is *blind* to the twins (the automorphism fixes it), but
* a payload vertex of a **non-symmetric** copy *sees* them (it attaches to `f(k,t)` and not to
  `f(swap k, t)`),

and `Ensemble.EColr` is **all** slot-colourings, so both kinds are present. `not_rulerRefines` is that,
as a theorem: **no symmetric copy can serve as the ruler.** ⚠ The doc's Construction C has only
symmetric copies, so *"take the ruler from the construction"* is exactly what this blocks.

★ This is a defect of the **model**, not of the argument, and it is the same defect that stops
`CopyProbe.sameLabelOrbit_of_tag` from discharging `TagIsolates` (which needs *every* copy to be
`SymCopy` and `Proper`). ▶ The fix is one model change — make a slot a **non-degenerate unordered**
pair, so `EColr` is a graph and the twins do not exist — and then `(R)` becomes a theorem via
`twin_blind` and `TagIsolates` via `sameLabelOrbit_of_tag`. Everything above this section survives it
unchanged; §3's two definitions and `readings_translate` are what it makes non-vacuous. -/

/-- The slot transposition. -/
def swapSlot (k : ESlot L) : ESlot L := (k.2, k.1)

theorem swapSlot_involutive : Function.Involutive (swapSlot (L := L)) := fun _ => rfl

/-- Reindexing a copy by the slot transposition. -/
def swapColr (c : EColr L) : EColr L := fun k => c (swapSlot k)

theorem swapColr_involutive : Function.Involutive (swapColr (L := L)) := fun c => by funext k; rfl

theorem swapColr_swapSlot (c : EColr L) (k : ESlot L) : swapColr c (swapSlot k) = c k := rfl

@[simp] theorem swapColr_swapColr (c : EColr L) : swapColr (swapColr c) = c := swapColr_involutive c

@[simp] theorem swapSlot_swapSlot (k : ESlot L) : swapSlot (swapSlot k) = k := rfl

theorem inSlot_swapSlot (k : ESlot L) (i : Fin L) : inSlot (swapSlot k) i = inSlot k i := by
  simp only [inSlot, swapSlot, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun hh => h1 hh.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun hh => h1 hh.symm, h2.symm⟩

/-- The slot transposition, as a map of the ensemble's vertices. -/
def tswapFun : EVert L → EVert L
  | Sum.inl (c, i) => Sum.inl (swapColr c, i)
  | Sum.inr (Sum.inl (k, t)) => Sum.inr (Sum.inl (swapSlot k, t))
  | Sum.inr (Sum.inr g) => Sum.inr (Sum.inr (swapColr g))

theorem tswapFun_involutive : Function.Involutive (tswapFun (L := L)) := by
  rintro (⟨c, i⟩ | ⟨k, t⟩ | g) <;>
    simp only [tswapFun, swapColr_involutive _, swapSlot_involutive _]

/-- ★ **The slot transposition is a symmetry of the ensemble.** -/
def tswap : EVert L ≃ EVert L := Function.Involutive.toPerm _ (tswapFun_involutive (L := L))

@[simp] theorem tswap_apply (x : EVert L) : tswap x = tswapFun x := rfl

theorem esort_tswap (x : EVert L) : esort (tswap x) = esort x := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g
  · rfl
  · rfl
  · show (if swapColr g = ebase L then 3 else 2) = (if g = ebase L then 3 else 2)
    by_cases hg : g = ebase L
    · rw [hg]; rfl
    · rw [if_neg hg, if_neg (fun hh => hg (by
        have := congrArg (swapColr (L := L)) hh
        rwa [swapColr_involutive g] at this))]

theorem eAdj_tswap (x y : EVert L) : eAdj (tswap x) (tswap y) = eAdj x y := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rcases y with ⟨c', j⟩ | ⟨k', t'⟩ | g' <;>
    simp only [tswap_apply, tswapFun, eAdj, inSlot_swapSlot, swapColr_swapSlot,
      swapColr_involutive.eq_iff, swapSlot_involutive.injective.eq_iff, swapColr_swapColr,
      swapSlot_swapSlot] <;>
    try rfl

theorem invG_tswap_eInit : InvG (tswap (L := L)) (eInit L) := by
  intro p
  simp only [eInit, esort_tswap, eAdj_tswap, Equiv.apply_eq_iff_eq]

theorem invG_tswap : InvG (tswap (L := L)) (eRoot L) := invG_wl2G invG_tswap_eInit

/-- ★ **A symmetric copy is blind to the twins.** -/
theorem twin_blind {c : EColr L} (hs : SymCopy c) (i : Fin L) (k : ESlot L) (t : Bool) :
    eRoot L (epay c i, efrm k t) = eRoot L (epay c i, efrm (swapSlot k) t) := by
  have hc : swapColr c = c := by funext s; exact hs s.2 s.1
  have h := invG_tswap (L := L) (epay c i, efrm k t)
  simp only [tswap_apply, tswapFun, hc] at h
  exact h.symm

/-- ### ⛔⛔ NO SYMMETRIC COPY CAN BE THE RULER, in this model.
A symmetric copy's payload vertex cannot separate the twin frame vertices `f(k,t)` and
`f(swap k, t)`; a non-symmetric copy's can, and this model contains non-symmetric copies. So `(R)`
fails at every symmetric `w₀` — including every copy the doc's construction actually uses.

★ Read this as *"the Lean rendering of the ensemble is coarser than the construction it models"*, not
as evidence about (A) or (B). ⛔ In particular it is **not** a point for (B). -/
private theorem ruler_sees {L : Nat} {a b : Fin L} (hab : a ≠ b) :
    eRoot L (epay (fun s => decide (s = ((a, b) : ESlot L))) a, efrm (a, b) true)
      ≠ eRoot L (epay (fun s => decide (s = ((a, b) : ESlot L))) a,
          efrm (swapSlot ((a, b) : ESlot L)) true) := by
  intro hsee
  have hadj := eAdj_eq_of_eRoot_eq
    (p := (epay (fun s => decide (s = ((a, b) : ESlot L))) a, efrm (a, b) true))
    (q := (epay (fun s => decide (s = ((a, b) : ESlot L))) a,
      efrm (swapSlot ((a, b) : ESlot L)) true)) hsee
  have e1 : eAdj (epay (fun s => decide (s = ((a, b) : ESlot L))) a) (efrm (a, b) true) = true := by
    simp [eAdj, inSlot, hab]
  have e2 : eAdj (epay (fun s => decide (s = ((a, b) : ESlot L))) a)
      (efrm (swapSlot ((a, b) : ESlot L)) true) = false := by
    simp [eAdj, inSlot, swapSlot, Prod.mk.injEq, hab, Ne.symm hab]
  rw [e1, e2] at hadj
  exact absurd hadj (by decide)

/-- ### ⛔⛔ NO SYMMETRIC COPY CAN BE THE RULER, in this model.
A symmetric copy's payload vertex cannot separate the twin frame vertices `f(k,t)` and
`f(swap k, t)`; a non-symmetric copy's can, and this model contains non-symmetric copies. So `(R)`
fails at every symmetric `w₀` — including every copy the doc's construction actually uses.

★ Read this as *"the Lean rendering of the ensemble is coarser than the construction it models"*, not
as evidence about (A) or (B). ⛔ In particular it is **not** a point for (B). -/
theorem not_rulerRefines {L : Nat} (hL : 2 ≤ L) {w₀ : PayIdx L} (hsym : SymCopy w₀.1) :
    ¬ RulerRefines L w₀ := by
  intro hR
  have h0 : (0 : Nat) < L := by omega
  have h1 : (1 : Nat) < L := by omega
  have hab : (⟨0, h0⟩ : Fin L) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
  exact ruler_sees hab
    (hR (⟨fun s => decide (s = ((⟨0, h0⟩, ⟨1, h1⟩) : ESlot L)), ⟨0, h0⟩⟩)
      (((⟨0, h0⟩, ⟨1, h1⟩) : ESlot L), true)
      (swapSlot ((⟨0, h0⟩, ⟨1, h1⟩) : ESlot L), true)
      (twin_blind hsym w₀.2 _ true))

end RulerAtEnsemble
end ChainDescent
