import ChainDescent.FrameTransfer

/-!
# Augmenting the encoding's atoms — what R3 actually costs

(`docs/chain-descent-cao-carrier-falsifiers.md` §6f.5a(β) and §6e.5's R3.)

## The coupling this makes explicit

R3 (§6e.5) is the fallback for the collapse (i): *"we never needed the exact collapse; define
`M⁺ = M` with `Φ` adjoined as an extra colour coordinate, close under refinement, and show
`ensemble ⊑ M⁺`."* It is promoted there to a co-equal first target, with one proviso —
*provided `M⁺` is still not a complete invariant.*

⛔ **There is a second cost, and it was not stated: adjoining atoms re-opens (ii).** The machine-checked
transfer (`FrameTransfer.merge_of_tuple_merge`) proves `Adequate` for **`mInit E`'s** atoms. Change the
atoms and `refinesAtoms` must be re-established for the new ones — so any adjoined data must itself be
determined by the bounded-arity tuple colouring. ⟹ **R3 buys (i) with currency drawn from (ii).**

`adequateFor_augment_iff` below is that statement, and it is an **iff**: the *only* extra obligation
is `Refines (pull b) extra`, and it is unavoidable.

## ⚠⚠ Why this is bad news for R3 as written, specifically

`Φ(c,i)` depends only on the **`S_L`-orbit** of the slot profile `a(c,i)` (§6e.2), and at the fixpoint
`a(c,i)` decorates each typed slot with an `M(c)`-2-WL colour. So `Φ` is at least as strong as *the
isomorphism type of a WL-colour-decorated structure* — an **orbit** computation, not a WL computation.
Nothing suggests that is bounded-arity, and §6e.2's own trap box explains why it had better not be.

▶ **So run R3 in the other direction.** Rather than *adjoin `Φ`, then hope it is bounded*, adjoin only
data that is **tuple-determined by construction**; then (ii) is free and the whole obligation stays
where it belongs, on (i). `adequateFor_augment_self` is the ceiling for that: the strongest legitimate
augmentation is the bound itself.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace AtomAugment

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.FrameTransfer
open ChainDescent.TupleWL

variable {L : Nat}

/-! ## 1. The transfer with the start colouring left free -/

/-- `FrameEncoding.Adequate` with the atoms as a parameter. ⚠ Note `blocks` does **not** mention the
start colouring at all — the entire start-dependence of the transfer is the one `refinesAtoms`
clause, which is exactly why the cost of changing atoms is computable. -/
structure AdequateFor (init : Col (MVert L × MVert L)) (b : Col (TCode L × TCode L)) : Prop where
  /-- The pullback separates at least as much as the chosen atoms do. -/
  refinesAtoms : PartitionClosure.Refines (pull b) init
  /-- ⛔ The crux, unchanged — and start-colouring-free. -/
  blocks : ∀ p q : MVert L × MVert L, pull b p = pull b q → pairSigG (pull b) p = pairSigG (pull b) q

theorem adequateFor_of_adequate {E : Fin L → Fin L → Bool} {b : Col (TCode L × TCode L)}
    (h : Adequate E b) : AdequateFor (mInit E) b :=
  ⟨h.refinesAtoms, h.blocks⟩

/-- The consumer, at arbitrary atoms. ⚠ Direction discipline is unchanged: **merges** only. -/
theorem merge_of_adequateFor {init : Col (MVert L × MVert L)} {b : Col (TCode L × TCode L)}
    (h : AdequateFor init b) {x y : MVert L}
    (hb : b (code x, code x) = b (code y, code y)) :
    wl2G init (x, x) = wl2G init (y, y) :=
  refines_wl2G_of_stable (stable_iff_sig.mpr h.blocks) h.refinesAtoms (x, x) (y, y) hb

/-! ## 2. ★★★ The price of an augmentation, named -/

/-- Adjoin `extra` to `init` as a second colour coordinate. -/
def augment (init extra : Col (MVert L × MVert L)) : Col (MVert L × MVert L) :=
  fun p => Nat.pair (init p) (extra p)

theorem refines_augment_iff {c init extra : Col (MVert L × MVert L)} :
    PartitionClosure.Refines c (augment init extra) ↔
      (PartitionClosure.Refines c init ∧ PartitionClosure.Refines c extra) := by
  constructor
  · intro h
    exact ⟨fun x y hxy => (Nat.pair_eq_pair.mp (h x y hxy)).1,
           fun x y hxy => (Nat.pair_eq_pair.mp (h x y hxy)).2⟩
  · rintro ⟨h1, h2⟩ x y hxy
    show Nat.pair _ _ = Nat.pair _ _
    rw [h1 x y hxy, h2 x y hxy]

/-- **★★★ THE PRICE OF R3, AND IT IS AN `iff`.**

Augmenting the encoding's atoms by `extra` costs **exactly** `Refines (pull b) extra` — the adjoined
data must itself be determined by the bounded-arity bound. Nothing less will do, and nothing more is
required. ⟹ *"adjoin `Φ` and close"* is not free: it is a fresh (ii)-obligation about `Φ`. -/
theorem adequateFor_augment_iff {init extra : Col (MVert L × MVert L)}
    {b : Col (TCode L × TCode L)} :
    AdequateFor (augment init extra) b ↔
      (AdequateFor init b ∧ PartitionClosure.Refines (pull b) extra) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := refines_augment_iff.mp h.refinesAtoms
    exact ⟨⟨h1, h.blocks⟩, h2⟩
  · rintro ⟨h, hx⟩
    exact ⟨refines_augment_iff.mpr ⟨h.refinesAtoms, hx⟩, h.blocks⟩

/-! ## 3. The augmented transfer, and the ceiling on legitimate augmentations -/

/-- **The §6f chain with adjoined atoms.** ⚠ `hex` is the whole of (β): it is the clause R3 has to
discharge for whatever it adjoins, and for `Φ` it is not known and looks false (see the header). -/
theorem merge_of_tuple_merge_aug {E : Fin L → Fin L → Bool}
    {extra : Col (MVert L × MVert L)} {s : Col (Tup 6 L)}
    (hs : Stable (roundTS (k := 6) (L := L)) s)
    (hat : PartitionClosure.Refines (pull (bOf s)) (mInit E))
    (hex : PartitionClosure.Refines (pull (bOf s)) extra) {x y : MVert L}
    (hb : bOf s (code x, code x) = bOf s (code y, code y)) :
    wl2G (augment (mInit E) extra) (x, x) = wl2G (augment (mInit E) extra) (y, y) :=
  merge_of_adequateFor
    (adequateFor_augment_iff.mpr ⟨adequateFor_of_adequate (adequate_bOf hs hat), hex⟩) hb

/-- **★★ THE CEILING — the strongest augmentation the transfer can carry is the bound itself.**

This is R3 run in the safe direction: adjoin `pull (bOf s)`, which is tuple-determined by
construction, so (ii) costs nothing and the entire obligation stays on (i). ⛔ Anything strictly finer
than `pull (bOf s)` is unavailable *by this route* — which is the precise sense in which R3 cannot
over-approximate the cross-copy channel for free. -/
theorem adequateFor_augment_self {E : Fin L → Fin L → Bool} {s : Col (Tup 6 L)}
    (hs : Stable (roundTS (k := 6) (L := L)) s)
    (hat : PartitionClosure.Refines (pull (bOf s)) (mInit E)) :
    AdequateFor (augment (mInit E) (pull (bOf s))) (bOf s) :=
  adequateFor_augment_iff.mpr
    ⟨adequateFor_of_adequate (adequate_bOf hs hat), PartitionClosure.Refines.refl _⟩

/-- Non-vacuity at the other end: a constant `extra` adjoins nothing and is always affordable, so
`augment` does not silently trivialize the interface in either direction. -/
theorem adequateFor_augment_const {init : Col (MVert L × MVert L)}
    {b : Col (TCode L × TCode L)} (h : AdequateFor init b) (n : Nat) :
    AdequateFor (augment init (fun _ => n)) b :=
  adequateFor_augment_iff.mpr ⟨h, fun _ _ _ => rfl⟩

end AtomAugment
end ChainDescent
